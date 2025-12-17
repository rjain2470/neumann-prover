
'''
src/neumann_prover/stages.py

This module defines the mapping from pipeline stages to default model identifiers and provides small helpers to query it.

Data:

STAGE_DEFAULTS: dict[str, str]
Mapping from stage name to default model identifier.

Functions:

list_stages() -> list[str]
Input: none. Output: list of valid stage names defined in STAGE_DEFAULTS.

default_model_for(stage: str) -> str
Input: a stage name. Output: default model identifier for that stage, or raises ValueError if unknown.
'''

# ---------------------------
# Canonical model choices
# ---------------------------
OPENAI_STRONG  = "gpt-5"
OPENAI_BUDGET  = "gpt-5-mini"

ANTHROPIC_BAL  = "claude-opus-4-1-20250805"
ANTHROPIC_STRG = "claude-sonnet-4-20250514"

OPENAI_CHEAP = "gpt-5-nano"

# ---------------------------
# Stage defaults
# ---------------------------
STAGE_DEFAULTS = {
    "informal_proof": OPENAI_BUDGET,
    "formal_statement_draft": OPENAI_BUDGET,
    "formal_proof_draft": OPENAI_STRONG,
    "formal_statement_correction": OPENAI_BUDGET,
    "formal_proof_correction": OPENAI_BUDGET,

    "formal_statement": OPENAI_BUDGET, # aliases
    "formal_proof": OPENAI_BUDGET,
}

VALID_STAGES = tuple(STAGE_DEFAULTS.keys())

def list_stages():
    return list(VALID_STAGES)

def default_model_for(stage: str) -> str:
    if stage not in STAGE_DEFAULTS:
        raise ValueError(f"Unknown stage '{stage}'. Valid: {VALID_STAGES}")
    return STAGE_DEFAULTS[stage]
