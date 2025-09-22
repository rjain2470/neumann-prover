
'''
src/neumann_prover/pipelines/formal_statement.py

This module contains the single-shot generator for formal statements. Iterative correction lives in neumann_prover.correction.

Functions:

formal_statement_generator(statement: str, model: str) -> str
Input: a mathematical specification and model id. Output: a first-draft formal statement (Lean text).
'''

from ..ask_llm import ask_llm
from ..utils import extract_lean_code, ensure_import_mathlib, compile_lean_snippet

def formal_statement_generator(
    statement: str,
    model: str = "gpt-5-mini",
    project_root: str = "/content/lean_project",
) -> str:
    """
    Ask GPT for a *formal statement only* (a compilable Lean file skeleton),
    then try compiling it. We deliberately ask for `sorry` in the proof position
    so the focus is on getting the declaration header right.

    Returns a short human-readable report string containing:
      - a success/failure headline,
      - the Lean code it produced,
      - compiler stdout/stderr (on failure).
    """
    prompt = (
        "You are a mathematician and computer scientist. Produce a minimal, compilable Lean 4 file "
        "that *states* the theorem below, with the proof body as `sorry` (no placeholders other than `sorry`). "
        "Rules:\n"
        "• If you are not sure of the name of a nontrivial definition in the statement in Mathlib, then formalize it. For example, 'simple group' is such a nontrivial definition \n"
        "• Put `import Mathlib` at the top.\n"
        "• Use `namespace Demo` ... `end Demo`.\n"
        "• Give an explicit theorem type matching the intended meaning of the statement.\n"
        "• End with `:= by\n  sorry`.\n"
        "• Return ONLY the Lean code inside a ```lean fenced block.\n\n"
        f"Informal statement:\n{statement.strip()}\n"
    )

    raw = ask_llm(prompt, model=model)
    lean_code = extract_lean_code(raw)

    ok, out, err = compile_lean_snippet(lean_code, project_root=project_root, filename="Main.lean")

    if ok:
        return (
            "Formal statement parsed and compiled.\n\n"
            "----- Lean file -----\n"
            f"{lean_code}\n"
            + (f"\n----- Lean stdout -----\n{out.strip()}\n" if out.strip() else "")
        )

    # Compilation likely fails when `sorry` is treated as an error; still useful to inspect header.
    msg = "Could not compile the formal statement."
    details = "\n".join(
        part for part in [
            "----- Lean file -----",
            lean_code,
            "----- Lean stdout -----",
            out.strip(),
            "----- Lean stderr -----",
            err.strip(),
        ] if part
    )
    return f"{msg}\n\n{details}\n"
