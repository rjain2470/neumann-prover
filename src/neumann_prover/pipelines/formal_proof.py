
'''
src/neumann_prover/pipelines/formal_proof.py

This module contains the single-shot generator for formal proofs. Iterative correction lives in neumann_prover.correction.

Functions:

formal_proof_generator(spec: str, model: str) -> str
Input: a theorem or specification and model id. Output: a first-draft formal proof (Lean text).
'''

import textwrap
from ..ask_llm import ask_llm
from ..utils import extract_lean_code
from .informal import informal_proof_generator, lean_pseudocode_generator
from .formal_statement import formal_statement_generator


def formal_proof_generator(
    informal_statement: str,
    informal_proof: str | None = None,
    pseudocode: str | None = None,
    formal_statement: str | None = None,
    *,
    model: str = "gpt-5-mini",
    error: str | None = None,
    width: int = 80,
) -> dict[str, str]:
    """
    Generate Lean 4 code proving a statement. If any of the supporting artifacts
    (informal_proof, pseudocode, formal_statement) are not supplied, they are
    generated automatically from the informal_statement.

    Returns:
      {
        "gpt_raw": <model text reflowed to paragraphs>,
        "lean_code": <contents of ```lean4 fenced block or raw fallback>
      }
    """

    # Fill missing dependencies with the existing single-shot generators.
    if formal_statement is None:
        formal_statement = formal_statement_generator(informal_statement, model=model)

    if informal_proof is None:
        informal_proof = informal_proof_generator(informal_statement, model=model)

    if pseudocode is None:
        #pseudocode = lean_pseudocode_generator(informal_statement, model=model)
        pseudocode = "Pseudocode not available."

    # Compact, structured, and directive prompt for high compliance.
    # Formal statement is treated as the single source of truth for the header.
    rules = (
        "- Begin with `import Mathlib`.\n"
        "- Use `namespace Demo` … `end Demo`.\n"
        "- Keep the theorem header EXACTLY as in <FORMAL_STATEMENT> (name, arguments, types).\n"
        "- No placeholders (`sorry`, `admit`).\n"
        "- Use only existing lemmas/tactics from Lean core/Mathlib; prefer canonical names.\n"
        "- If a short auxiliary lemma is essential, place it above the theorem and prove it fully.\n"
        "- Output ONLY one fenced block: ```lean4 ... ``` containing the COMPLETE file."
    )

    sections = [
        "<TASK>\nProduce compiling Lean 4 code proving the given statement exactly. Be meticulous and self-check lemma availability.",
        "<RULES>\n" + rules,
        "<FORMAL_STATEMENT>\n" + formal_statement.strip(),
        "<INFORMAL_STATEMENT>\n" + informal_statement.strip(),
        "<INFORMAL_PROOF>\n" + informal_proof.strip(),
        "<PSEUDOCODE>\n" + pseudocode.strip(),
    ]
    if error:
        sections.append("<LAST_COMPILER_ERROR>\n" + error.strip())

    prompt = "\n\n".join(sections) + "\n\n<OUTPUT>\nReturn only a single ```lean4 fenced block."

    # Call model
    raw = ask_llm(prompt, model=model)

    # Reflow assistant text for readability in notebooks
    paras = raw.split("\n")
    gpt_reflowed = "\n".join(
        textwrap.fill(p.strip(), width=width) if p.strip() else "" for p in paras
    )

    # Extract Lean code block
    lean_code = extract_lean_code(raw)

    return {
        "gpt_raw": gpt_reflowed,
        "lean_code": lean_code,
    }
