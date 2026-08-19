"""Single-shot generator for a formal *statement* (Lean text out).

Compilation and iterative correction live in `neumann_prover.correction`.
"""
from __future__ import annotations

from ..ask_llm import ask_llm
from ..stages import OPENAI_BUDGET
from ..utils import extract_lean_code


def formal_statement_generator(statement: str, model: str = OPENAI_BUDGET) -> str:
    """Informal statement -> a minimal Lean 4 file that *states* the theorem with
    a `sorry` body. Returns the extracted Lean code."""
    prompt = (
        "You are a mathematician and computer scientist. Produce a minimal, compilable Lean 4 file "
        "that *states* the theorem below, with the proof body as `sorry` (no placeholders other than `sorry`).\n"
        "Rules:\n"
        "- If a nontrivial notion in the statement has no standard Mathlib name, define it (e.g. 'simple group').\n"
        "- Put `import Mathlib` at the top.\n"
        "- Wrap the declaration in `namespace Demo` ... `end Demo`.\n"
        "- Give an explicit theorem type matching the intended meaning.\n"
        "- End the body with `:= by\n  sorry`.\n"
        "- Return ONLY the Lean code inside a ```lean4 fenced block.\n\n"
        f"Informal statement:\n{statement.strip()}\n"
    )
    return extract_lean_code(ask_llm(prompt, model=model))
