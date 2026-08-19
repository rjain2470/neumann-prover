"""Lean-specific utilities shared across pipelines and correction loops.

The important piece here is `verify_lean`: a *sound* success check. Plain
compilation is not enough — `sorry` is only a warning, so a `sorry` /
`native_decide` / `admit` "proof" exits 0 and would otherwise be counted as a
win. `verify_lean` rejects those and (for proofs) audits `#print axioms` against
a conservative whitelist, closing the reward-hacking hole.
"""
from __future__ import annotations

import os
import re
import pathlib
import subprocess
from dataclasses import dataclass, field

# Tactics/terms that let a "proof" pass the compiler without real content.
# `sorry`/`admit` leave a hole; `native_decide` trusts the compiler (ofReduceBool)
# rather than the kernel and has produced proofs of False.
_BANNED_IN_PROOF = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b")
_BANNED_IN_STATEMENT = re.compile(r"\b(admit|native_decide)\b")

# Axioms a normal Mathlib proof may depend on. Anything else (notably `sorryAx`
# or `Lean.ofReduceBool`) means the proof is unsound.
AXIOM_WHITELIST = frozenset({"propext", "Classical.choice", "Quot.sound"})

_DECL_NAME = re.compile(r"^\s*(?:theorem|lemma)\s+([A-Za-z_][\w'.]*)", re.MULTILINE)
_AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]")
_SORRY_WARNING = re.compile(r"uses 'sorry'|declaration uses 'sorry'")


@dataclass
class LeanResult:
    ok: bool                       # compiled *and* sound for the expectation
    compiled: bool                 # lean exited 0
    stdout: str = ""
    stderr: str = ""
    reason: str = ""               # why `ok` is False (empty if ok)
    axioms: list[str] = field(default_factory=list)


# --------------------------------------------------------------------------
# Project root + compilation
# --------------------------------------------------------------------------

def resolve_project_root(project_root: str | None = None) -> pathlib.Path:
    """Single source of truth for where the Lean project lives."""
    if not project_root:
        project_root = os.environ.get(
            "NEUMANN_LEAN_PROJECT", str(pathlib.Path.cwd() / "lean_project")
        )
    return pathlib.Path(project_root).expanduser().resolve()


def compile_lean_snippet(
    lean_code: str,
    project_root: str | None = None,
    filename: str = "Main.lean",
    *,
    timeout: int = 300,
) -> tuple[bool, str, str]:
    """Write `lean_code` (with `import Mathlib` ensured) into the project and
    compile it with `lake env lean`. Returns (ok, stdout, stderr)."""
    root = resolve_project_root(project_root)
    root.mkdir(parents=True, exist_ok=True)
    (root / filename).write_text(ensure_import_mathlib(lean_code), encoding="utf-8")

    env = os.environ.copy()
    elan_bin = pathlib.Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"

    try:
        proc = subprocess.run(
            ["lake", "-q", "env", "lean", filename],
            cwd=root,
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except FileNotFoundError as e:
        return False, "", f"Lean toolchain not found: {e}"
    except subprocess.TimeoutExpired:
        return False, "", f"Lean compilation timed out after {timeout}s"
    except Exception as e:  # pragma: no cover - defensive
        return False, "", f"Lean invocation error: {e}"

    return proc.returncode == 0, (proc.stdout or "").strip(), (proc.stderr or "").strip()


# --------------------------------------------------------------------------
# Sound verification
# --------------------------------------------------------------------------

def verify_lean(
    code: str,
    *,
    expect: str,                       # "statement" | "proof"
    project_root: str | None = None,
    filename: str = "Main.lean",
    check_axioms: bool = True,
) -> LeanResult:
    """Compile and check *soundly*.

    - statement: must compile; `native_decide`/`admit` are rejected (a bare
      statement has no business using them). The `sorry` body is expected.
    - proof: must compile with no `sorry`/`admit`/`native_decide`, no
      "declaration uses 'sorry'" warning, and (when `check_axioms`) only
      whitelisted axioms.
    """
    code = ensure_import_mathlib(extract_lean_code(code))

    if expect == "statement":
        if _BANNED_IN_STATEMENT.search(code):
            return LeanResult(False, False, reason="banned tactic in statement")
        ok, out, err = compile_lean_snippet(code, project_root, filename)
        return LeanResult(ok, ok, out, err, "" if ok else "did not compile")

    # expect == "proof"
    if _BANNED_IN_PROOF.search(code):
        return LeanResult(False, False, reason="proof uses sorry/admit/native_decide")

    to_compile = code
    names = _DECL_NAME.findall(code)
    if check_axioms and names:
        to_compile = _append_axiom_prints(code, names)

    ok, out, err = compile_lean_snippet(to_compile, project_root, filename)
    if not ok:
        return LeanResult(False, False, out, err, "did not compile")
    if _SORRY_WARNING.search(out) or _SORRY_WARNING.search(err):
        return LeanResult(False, True, out, err, "declaration uses sorry")

    used = _parse_axioms(out)
    bad = [a for a in used if a not in AXIOM_WHITELIST]
    if bad:
        return LeanResult(False, True, out, err, f"non-whitelisted axioms: {bad}", used)
    return LeanResult(True, True, out, err, "", used)


def _append_axiom_prints(code: str, names: list[str]) -> str:
    """Insert `#print axioms <name>` before the final `end <ns>` (so unqualified
    names resolve inside their namespace), else append at the end."""
    prints = "\n".join(f"#print axioms {n}" for n in names)
    lines = code.splitlines()
    for i in range(len(lines) - 1, -1, -1):
        if lines[i].strip().startswith("end "):
            lines.insert(i, prints)
            return "\n".join(lines)
    return code.rstrip() + "\n" + prints + "\n"


def _parse_axioms(stdout: str) -> list[str]:
    used: list[str] = []
    for m in _AXIOM_LINE.finditer(stdout):
        used.extend(a.strip() for a in m.group(1).split(",") if a.strip())
    return used


# --------------------------------------------------------------------------
# Code extraction
# --------------------------------------------------------------------------

def extract_lean_code(text: str) -> str:
    """Pull Lean from a model reply: prefer the last fenced ```lean(4)``` block,
    otherwise the whole text. Namespace-agnostic (no hard-coded `end Demo`)."""
    blocks = re.findall(r"```lean4?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    if blocks:
        return blocks[-1].strip()
    # No fenced block: keep from the first `import` if present, else raw text.
    start = text.find("import ")
    return (text[start:] if start != -1 else text).strip()


def ensure_import_mathlib(lean_code: str) -> str:
    lines = lean_code.splitlines()
    while lines and lines[0].strip() == "":
        lines.pop(0)
    if not lines or not lines[0].lstrip().startswith("import Mathlib"):
        lines.insert(0, "import Mathlib")
    return "\n".join(lines).rstrip() + "\n"
