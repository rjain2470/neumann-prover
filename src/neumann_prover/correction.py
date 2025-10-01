'''
src/neumann_prover/correction.py

This module owns all error-correction and retry logic so it can be replaced independently in a future version. It fixes statements and proofs and, when requested, iterates until compilation succeeds or a limit is reached.

Functions:

formal_statement_corrector(code: str, model: str | None = None) -> str
Input: a formal statement or diagnostic bundle, optional model id. Output: corrected statement text.

formal_proof_corrector(code: str, model: str | None = None) -> str
Input: a formal proof or diagnostic bundle, optional model id. Output: corrected proof text.

formal_statement_until_compiles(spec: str, model: str | None = None, max_iters: int = 3) -> str
Input: a specification, optional model id, and iteration cap. Output: the best compiling statement (or last attempt).

try_formal_proof_until_compiles(spec: str, model: str | None = None, max_iters: int = 3) -> str
Input: a specification, optional model id, and iteration cap. Output: the best compiling proof (or last attempt).
'''

from __future__ import annotations
from typing import Optional, Dict, List
from .ask_llm import ask_llm
from .utils import extract_lean_code, ensure_import_mathlib, compile_lean_snippet
from .pipelines.formal_proof import formal_proof_generator
from .pipelines.formal_statement import formal_statement_generator

def formal_statement_corrector(
    prev_lean_code: str,
    error: str,
    *,
    restated: str | None = None,
    model: str = "gpt-5-mini",
) -> str:
    """
    Ask GPT to correct a *failing* Lean 4 file that is supposed to only STATE a theorem
    (body is `by\n  sorry`). It preserves intent, keeps `import Mathlib`, the `Demo` namespace.
    Returns a *full* Lean file as text.
    """
    intent = (
        restated.strip()
        if restated
        else "Use the same mathematical content as in the previous attempt; do not change the meaning."
    )

    prompt = (
        "You are a mathematician and computer scientist. The Lean 4 file below fails to compile.\n"
        "Correct it so that it compiles and *only states* the theorem (the proof body remains `by\\n  sorry`).\n"
        "Keep the intended meaning exactly, but fix missing typeclass assumptions, universes, variables, etc.\n"
        "Rules:\n"
        "• Start with `import Mathlib`.\n"
        "• Use `namespace Demo` … `end Demo`.\n"
        "• The body should end with `:= by\\n  sorry` (no other placeholders).\n"
        "• Do not add extraneous commentary; return ONLY a single ```lean4 fenced block containing the full file.\n\n"
        f"Intended statement (precise English):\n{intent}\n\n"
        "Current Lean file (fails to compile):\n```lean4\n"
        f"{prev_lean_code.strip()}\n"
        "```\n\n"
        "Compiler output:\n```\n"
        f"{(error or '').strip()}\n"
        "```\n"
        "Return the corrected Lean file now."
    )

    gpt_raw = ask_llm(prompt, model=model)
    return extract_lean_code(gpt_raw)

def formal_statement_until_compiles(
    statement: str,
    model: str | None = None,
    max_iters: int = 3,
    project_root: str = None,
    filename: str = "Main.lean",
) -> str:
    """
    Try up to max_iters times. On the first compilation success, return immediately.
    If none succeed, return the last attempted code.
    """

    if not project_root:
        import os, pathlib
        project_root = os.environ.get("NEUMANN_LEAN_PROJECT", str(pathlib.Path.cwd() / "lean_project"))
    
    last_code: str = ""
    last_error: str | None = None

    for i in range(1, max_iters + 1):
        print(f"\n=== Attempt {i}/{max_iters} (Formal Statement) ===")

        if i == 1:
            # 1) Generate initial draft (generator may return a report; extract Lean).
            raw = formal_statement_generator(statement, model=model, project_root=project_root)
            code = extract_lean_code(raw) or str(raw)
        else:
            # 2) Correct using previous code + diagnostics bundled together.
            if not last_code or last_error is None:
                print("Correction requires previous code and error. Stopping.")
                break

            corrected = formal_statement_corrector(
                last_code,
                error=last_error,
                restated=statement,
                model=model,
              )
            code = extract_lean_code(corrected) or str(corrected)

        # Normalize and compile
        code = ensure_import_mathlib(code)
        ok, out, err = compile_lean_snippet(
            code
        )
        last_code = code

        if ok:
            print("File successfully compiled!")
            return code

        else:
          print("Compile failed; attempting correction.")
          last_error = err

    print(f"\n=== Failed to compile formal statement after {max_iters} attempts. Returning last attempt. ===")
    return last_code


def try_formal_proof_until_compiles(
    informal_statement: str | None = None,
    informal_proof: str | None = None,
    pseudocode: str | None = None,
    formal_statement: str | None = None,
    *,
    model: str | None = None,
    max_iters: int = 4,          # renamed for clarity; pass this from your pipeline
    project_root: str | None = None,
    filename: str = "Main.lean",
) -> Dict[str, object]:
    """
    Attempt to synthesize a complete Lean proof up to max_iters times.
    On each failure, feed compiler stderr back into the next prompt.
    Returns: {"success": bool, "final_code": str, "attempts": [ {...} , ...] }
    """

    if not project_root:
        import os, pathlib
        project_root = os.environ.get("NEUMANN_LEAN_PROJECT", str(pathlib.Path.cwd() / "lean_project"))
    
    attempts: List[Dict[str, str]] = []
    last_error: str | None = None
    final_code: str = ""
    success = False

    for i in range(1, max_iters + 1):
        print(f"\n=== Attempt {i}/{max_iters} (Formal Proof) ===")

        # Generate candidate Lean code (the generator auto-fills missing artifacts)
        gen = formal_proof_generator(
            informal_statement=informal_statement,
            informal_proof=informal_proof,
            pseudocode=pseudocode,
            formal_statement=formal_statement,
            model=model,
            error=last_error,
        )
        code = gen.get("lean_code", "") if isinstance(gen, dict) else str(gen)
        code = ensure_import_mathlib(extract_lean_code(code) or code)

        # Compile
        ok, out, err = compile_lean_snippet(
            code
        )

        # Log this round
        attempts.append({
            "attempt": str(i),
            "gpt_raw": gen.get("gpt_raw", "") if isinstance(gen, dict) else "",
            "lean_code": code,
            "stdout": (out or "").strip(),
            "stderr": (err or "").strip(),
            "ok": str(bool(ok)),
        })

        if ok:
            print("File successfully compiled!")
            final_code = code
            success = True
            break

        else:
          print("Compile failed; feeding error back into the next attempt.")
          last_error = err or ""

    return {
        "success": success,
        "final_code": final_code,
        "attempts": attempts,
    }
