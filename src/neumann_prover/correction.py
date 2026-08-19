"""Error-correction and retry loops.

Isolated here so it can be swapped independently. Both loops now judge success
with `verify_lean` (sound: no sorry/native_decide, whitelisted axioms), not a
bare exit code.
"""
from __future__ import annotations

from typing import Optional

from .ask_llm import ask_llm
from .stages import default_model_for
from .utils import extract_lean_code, ensure_import_mathlib, verify_lean, LeanResult
from .pipelines.formal_proof import formal_proof_generator
from .pipelines.formal_statement import formal_statement_generator


def formal_statement_corrector(
    prev_lean_code: str,
    error: str,
    *,
    restated: Optional[str] = None,
    model: Optional[str] = None,
) -> str:
    """Repair a failing Lean 4 file that should only *state* a theorem (body is
    `by\\n  sorry`), preserving intent. Returns the extracted Lean code."""
    model = model or default_model_for("formal_statement_correction")
    intent = (
        restated.strip()
        if restated
        else "Use the same mathematical content as before; do not change the meaning."
    )
    prompt = (
        "You are a mathematician and computer scientist. The Lean 4 file below fails to compile.\n"
        "Correct it so it compiles and *only states* the theorem (the body stays `by\\n  sorry`).\n"
        "Keep the intended meaning exactly; fix missing typeclass assumptions, universes, variables, etc.\n"
        "Rules: start with `import Mathlib`; wrap in `namespace Demo` ... `end Demo`; body ends with "
        "`:= by\\n  sorry`; return ONLY a single ```lean4 fenced block with the full file.\n\n"
        f"Intended statement (precise English):\n{intent}\n\n"
        "Current Lean file (fails to compile):\n```lean4\n"
        f"{prev_lean_code.strip()}\n```\n\n"
        "Compiler output:\n```\n"
        f"{(error or '').strip()}\n```\n"
        "Return the corrected Lean file now."
    )
    return extract_lean_code(ask_llm(prompt, model=model))


def formal_statement_until_compiles(
    statement: str,
    model: Optional[str] = None,
    max_iters: int = 3,
    project_root: Optional[str] = None,
) -> str:
    """Generate, then correct-until-it-compiles. Returns the first compiling
    statement, else the last attempt."""
    last_code = ""
    last_error: Optional[str] = None

    for i in range(1, max_iters + 1):
        print(f"\n=== Attempt {i}/{max_iters} (Formal Statement) ===")
        if i == 1:
            code = formal_statement_generator(statement, model=model)
        elif last_code and last_error is not None:
            code = formal_statement_corrector(
                last_code, error=last_error, restated=statement, model=model
            )
        else:
            print("Correction requires previous code and error. Stopping.")
            break

        code = ensure_import_mathlib(code)
        last_code = code
        res = verify_lean(code, expect="statement", project_root=project_root)
        if res.ok:
            print("Statement compiled.")
            return code
        print(f"Statement not accepted ({res.reason}); attempting correction.")
        last_error = res.stderr or res.stdout or res.reason

    print(f"\n=== No compiling statement after {max_iters} attempts; returning last. ===")
    return last_code


def try_formal_proof_until_compiles(
    informal_statement: Optional[str] = None,
    informal_proof: Optional[str] = None,
    pseudocode: Optional[str] = None,
    formal_statement: Optional[str] = None,
    *,
    model: Optional[str] = None,
    max_iters: int = 4,
    project_root: Optional[str] = None,
) -> dict:
    """Synthesize a Lean proof, feeding compiler errors back each round. Success
    requires a *sound* proof (verify_lean). Returns
    {"success", "final_code", "attempts"}."""
    attempts: list[dict] = []
    last_error: Optional[str] = None
    final_code = ""
    success = False

    for i in range(1, max_iters + 1):
        print(f"\n=== Attempt {i}/{max_iters} (Formal Proof) ===")
        gen = formal_proof_generator(
            informal_statement=informal_statement,
            informal_proof=informal_proof,
            pseudocode=pseudocode,
            formal_statement=formal_statement,
            model=model,
            error=last_error,
        )
        code = ensure_import_mathlib(gen["lean_code"])
        res: LeanResult = verify_lean(code, expect="proof", project_root=project_root)

        attempts.append({
            "attempt": str(i),
            "gpt_raw": gen.get("gpt_raw", ""),
            "lean_code": code,
            "stdout": res.stdout,
            "stderr": res.stderr,
            "ok": str(res.ok),
            "reason": res.reason,
        })

        if res.ok:
            print("Proof verified (compiles, no sorry, whitelisted axioms).")
            final_code = code
            success = True
            break
        print(f"Proof not accepted ({res.reason}); feeding error into next attempt.")
        last_error = res.stderr or res.stdout or res.reason

    return {"success": success, "final_code": final_code, "attempts": attempts}
