"""Single-shot generator for a formal *proof* (Lean text out).

Compilation and iterative correction live in `neumann_prover.correction`.
"""
from __future__ import annotations

import textwrap
from typing import Optional

from ..ask_llm import ask_llm
from ..stages import OPENAI_STRONG
from ..utils import extract_lean_code
from .informal import informal_proof_generator, lean_pseudocode_generator
from .formal_statement import formal_statement_generator

_RULES = (
    "- Begin with `import Mathlib`.\n"
    "- Wrap the declaration in `namespace Demo` ... `end Demo`.\n"
    "- Keep the theorem header EXACTLY as in <FORMAL_STATEMENT> (name, arguments, types).\n"
    "- No placeholders (`sorry`, `admit`) and no `native_decide`.\n"
    "- Use only existing lemmas/tactics from Lean core/Mathlib; prefer canonical names.\n"
    "- If a short auxiliary lemma is essential, place it above the theorem and prove it fully.\n"
    "- Output ONLY one fenced block: ```lean4 ... ``` containing the COMPLETE file."
)


def formal_proof_generator(
    informal_statement: str,
    informal_proof: Optional[str] = None,
    pseudocode: Optional[str] = None,
    formal_statement: Optional[str] = None,
    *,
    model: str = OPENAI_STRONG,
    error: Optional[str] = None,
    width: int = 80,
) -> dict[str, str]:
    """Generate Lean 4 code proving a statement. Missing supporting artifacts
    (formal statement, informal proof, pseudocode) are generated from the
    informal statement. Returns {"gpt_raw": ..., "lean_code": ...}."""
    if formal_statement is None:
        formal_statement = formal_statement_generator(informal_statement, model=model)
    if informal_proof is None:
        informal_proof = informal_proof_generator(informal_statement, model=model)
    if pseudocode is None:
        pseudocode = lean_pseudocode_generator(informal_proof, model=model)

    sections = [
        "<TASK>\nProduce compiling Lean 4 code proving the given statement exactly. "
        "Be meticulous and self-check lemma availability.",
        "<RULES>\n" + _RULES,
        "<FORMAL_STATEMENT>\n" + formal_statement.strip(),
        "<INFORMAL_STATEMENT>\n" + informal_statement.strip(),
        "<INFORMAL_PROOF>\n" + informal_proof.strip(),
        "<PSEUDOCODE>\n" + pseudocode.strip(),
    ]
    if error:
        sections.append("<LAST_COMPILER_ERROR>\n" + error.strip())
    prompt = "\n\n".join(sections) + "\n\n<OUTPUT>\nReturn only a single ```lean4 fenced block."

    raw = ask_llm(prompt, model=model)
    gpt_reflowed = "\n".join(
        textwrap.fill(p.strip(), width=width) if p.strip() else "" for p in raw.split("\n")
    )
    return {"gpt_raw": gpt_reflowed, "lean_code": extract_lean_code(raw)}
