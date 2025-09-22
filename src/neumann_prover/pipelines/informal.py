
'''
src/neumann_prover/pipelines/informal.py

This module contains single-shot generators for informal reasoning artifacts. They select a provider based on the model identifier and return plain text results.

Functions:

informal_proof_generator(prompt: str, model: str) -> str
Input: an informal statement and model id. Output: an informal proof draft as text.

lean_pseudocode_generator(prompt: str, model: str) -> str
Input: a natural-language description and model id. Output: Lean-style pseudocode as text.
'''

from ..ask_llm import ask_llm

def informal_proof_generator(statement: str, model: str = "gpt-5-mini") -> str:
    prompt = (
        "You are a careful mathematician. Given the statement below, write a clear, rigorous, "
        "self‑contained informal proof (2–8 sentences). Avoid placeholders and avoid Lean code. "
        "If the claim needs assumptions, state them explicitly.\n\n"
        f"Statement:\n{statement.strip()}"
    )
    return ask_llm(prompt, model=model)

def lean_pseudocode_generator(
    informal_proof: str,
    model: str = "gpt-5-mini",
) -> str:
    """
    Translate an informal proof into Lean-4 pseudocode using only standard
    tactic patterns. The output is *not* expected to compile; it’s a guide
    for later code synthesis.
    """
    prompt = (
        "You are a mathematician and computer scientist. Translate the informal proof below into Lean 4 "
        "pseudocode using standard tactic patterns only (intro, refine, apply, exact, have, rw, simp, cases, rcases, calc). "
        "Do not invent lemma names; prefer canonical names from core or Mathlib (e.g., add_comm, mul_add, add_assoc, "
        "inv_mul_cancel, etc.). Use goal‑shaped steps and keep it concise and readable.\n\n"
        f"{informal_proof.strip()}"
    )
    return ask_llm(prompt, model=model)
