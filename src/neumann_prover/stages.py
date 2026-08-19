"""Pipeline stages and their default models — the single source of truth.

`STAGE_DEFAULTS` maps each stage to a default model id. Change a default here and
every pipeline picks it up. Callers may still override per call.
"""
from __future__ import annotations

# --------------------------------------------------------------------------
# Canonical model choices (current-best as of Aug 2026; override per call).
# NOTE: gpt-5 reasoning models and Claude Opus 4.7/4.8 reject `temperature`;
# providers.py omits it for those automatically.
# --------------------------------------------------------------------------
OPENAI_STRONG = "gpt-5"
OPENAI_BUDGET = "gpt-5-mini"
OPENAI_CHEAP = "gpt-5-nano"

ANTHROPIC_STRONG = "claude-opus-4-8"
ANTHROPIC_BUDGET = "claude-sonnet-4-6"

# --------------------------------------------------------------------------
# Stage defaults
# --------------------------------------------------------------------------
STAGE_DEFAULTS: dict[str, str] = {
    "informal_proof": OPENAI_BUDGET,
    "formal_statement_draft": OPENAI_BUDGET,
    "formal_proof_draft": OPENAI_STRONG,
    "formal_statement_correction": OPENAI_BUDGET,
    "formal_proof_correction": OPENAI_STRONG,
    # aliases used by the batch runner
    "formal_statement": OPENAI_BUDGET,
    "formal_proof": OPENAI_STRONG,
}

VALID_STAGES = tuple(STAGE_DEFAULTS)


def list_stages() -> list[str]:
    return list(VALID_STAGES)


def default_model_for(stage: str) -> str:
    try:
        return STAGE_DEFAULTS[stage]
    except KeyError:
        raise ValueError(f"Unknown stage '{stage}'. Valid: {VALID_STAGES}") from None
