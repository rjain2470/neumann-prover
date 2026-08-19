"""Single-shot generators for informal artifacts (plain text out)."""
from __future__ import annotations

from ..ask_llm import ask_llm
from ..stages import OPENAI_BUDGET


def informal_proof_generator(statement: str, model: str = OPENAI_BUDGET) -> str:
    """Informal statement -> a short, rigorous informal proof."""
    prompt = (
        "You are a careful mathematician. Given the statement below, write a clear, rigorous, "
        "self-contained informal proof (2-8 sentences). Avoid placeholders and avoid Lean code. "
        "If the claim needs assumptions, state them explicitly.\n\n"
        f"Statement:\n{statement.strip()}"
    )
    return ask_llm(prompt, model=model)


def lean_pseudocode_generator(informal_proof: str, model: str = OPENAI_BUDGET) -> str:
    """Informal proof -> Lean 4 pseudocode (a guide for synthesis, not expected
    to compile)."""
    prompt = (
        "You are a mathematician and computer scientist. Translate the informal proof below into Lean 4 "
        "pseudocode using standard tactic patterns only (intro, refine, apply, exact, have, rw, simp, cases, rcases, calc). "
        "Do not invent lemma names; prefer canonical names from core or Mathlib (e.g., add_comm, mul_add, add_assoc, "
        "inv_mul_cancel). Use goal-shaped steps and keep it concise and readable.\n\n"
        f"{informal_proof.strip()}"
    )
    return ask_llm(prompt, model=model)
