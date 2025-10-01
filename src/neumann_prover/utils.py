
'''
src/neumann_prover/utils.py

This module contains Lean-specific utilities that are shared across pipelines and correction loops.

Functions:

extract_lean_code(text: str) -> str
Input: arbitrary text. Output: Lean code extracted from fenced blocks, or the original text if none are found.

ensure_import_mathlib(code: str) -> str
Input: Lean code. Output: code with minimal Mathlib import header ensured at the top.

compile_lean_snippet(code: str) -> tuple[bool, str]
Input: Lean code. Output: (success flag, compiler output or diagnostics).
'''

import os
import re
import subprocess
import pathlib
from typing import Tuple

def compile_lean_snippet(
    lean_code: str,
    project_root: str | None = None,
    filename: str = "Main.lean",
    *,
    echo: bool = False,
) -> tuple[bool, str, str]:
    """
    Write `lean_code` to {project_root}/{filename}, ensure `import Mathlib` is present,
    and compile using `lake env lean`.

    Returns (ok, stdout, stderr).
    - ok: True if compilation succeeded, False otherwise.
    - stdout/stderr: compiler outputs (possibly empty).
    """
    # Resolve project root
    if not project_root:
        env_root = os.environ.get("NEUMANN_LEAN_PROJECT")
        if env_root:
            project_root = env_root
        else:
            project_root = str(pathlib.Path.cwd() / "lean_project")

    root = pathlib.Path(project_root).expanduser().resolve()
    root.mkdir(parents=True, exist_ok=True)
    (root / filename).write_text(ensure_import_mathlib(lean_code), encoding="utf-8")

    cmd = [
        "bash", "-lc",
        f"cd {root} && "
        f"source \"$HOME/.elan/env\" >/dev/null 2>&1 || true && "
        f"lake -q env lean {filename}"
    ]

    try:
        proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        stdout, stderr = proc.communicate()
        ok = (proc.returncode == 0)
        return ok, (stdout or "").strip(), (stderr or "").strip()
    except FileNotFoundError as e:
        return False, "", f"Lean toolchain not found: {e}"
    except Exception as e:
        return False, "", f"Lean invocation error: {e}"

def extract_lean_code(text: str) -> str:
    m = re.search(r"```lean4\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    if not m:
        m = re.search(r"```lean\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    code = m.group(1).strip() if m else text.strip()
    start = code.find("import Mathlib")
    end = code.rfind("end Demo")
    if start != -1 and end != -1:
        end_line_break = code.find("\n", end)
        if end_line_break == -1:
            end_line_break = len(code)
        code = code[start:end_line_break].strip()
    return code

def ensure_import_mathlib(lean_code: str) -> str:
    lines = [ln for ln in lean_code.splitlines()]
    while lines and lines[0].strip() == "":
        lines.pop(0)
    if not lines or not lines[0].startswith("import Mathlib"):
        lines.insert(0, "import Mathlib")
    return "\n".join(lines).rstrip() + "\n"
