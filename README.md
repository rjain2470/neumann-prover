# Neumann-Prover ✈️

**Neumann-Prover** is an end-to-end, multi-purpose autoformalization tool designed to produce formal proofs in Lean. It uses cutting-edge foundation models from OpenAI, and Anthropic,
as well over twenty open-source models available via Together, including offerings from DeepSeek, Qwen, and Meta. It offers extraordinary flexibility: not only can users choose which
model to use, they have the option to input an informal statement and/or a formal statement in Lean, as well as the option to input an informal formal proof. Moreover, the user can choose
whether they want (i) an informal proof, (ii) a formal statement, (iii) Lean pseudocode of a formal proof, or (iv) a formal proof. The model then interacts dynamically with the Lean4 
compiler to iterate until it produces a correct result.

## Features 🚀

- **Text-to-Proof Automation**: Generate informal proofs, formal statements, and Lean-4 pseudocode from natural language inputs.
- **Formal Statement Verification**: Translate informal mathematical theorem statement into Lean4 code.
- **Integration with Lean Theorem Prover**: Ensures compatibility with Lean and Mathlib.
- **Multi-Model Support**: Seamlessly utilize OpenAI, Anthropic, and Together APIs for diverse functionality.

## Repository Structure 📂

```plaintext
├── neumann-prover/       # Core library
│   ├── __init__.py       # Entry point for library exports
│   ├── pipelines/        # Multi-stage autoformalization pipeline modules
│   ├── providers.py      # Integrations for OpenAI, Anthropic, etc.
│   ├── utils.py          # Utility functions for Lean code extraction
├── scripts/              # Scripts for setup and environment configuration
    └── setup_lean_env.sh # Shell script to configure Lean and Mathlib
├── src/                  # Source package directory
│   └── neumann_prover/
├── pyproject.toml        # Build and dependency configuration
├── README.md             # Project documentation
└── .gitignore            # Files to exclude from version control
```

## Installation 🔧
### X

### Import onto Local Library
You can import `neumann-prover` into your local Python environment by running the following code.
```python
%pip install -e /Users/jain/neumann-prover > /dev/null 2>&1

import os, subprocess
repo = "/Users/jain/neumann-prover"
os.chdir(repo)
subprocess.run(["bash", "scripts/setup_lean_env.sh"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=True)
from neumann_prover import ask_llm, list_stages, default_model_for
from neumann_prover.utils import extract_lean_code, ensure_import_mathlib, compile_lean_snippet
from neumann_prover.providers import _provider_for
from neumann_prover.pipelines import informal_proof_generator, lean_pseudocode_generator, formal_statement_generator, formal_proof_generator, run_pipeline, batch
from neumann_prover.correction import formal_statement_corrector, formal_statement_until_compiles, try_formal_proof_until_compiles
```
### Example Usage
Here is an example of how one might use this repo to generate the formal statement from an informal statement.
```python
informal_text = "For every even integer n, 4 divides n^2."
print(formal_statement_until_compiles(informal_text, model="gpt-5-mini", max_iters=2))
```

```
=== Attempt 1/2 (Formal Statement) ===
File successfully compiled!
import Mathlib

namespace Demo

def even (n : Int) : Prop := ∃ k : Int, n = 2 * k

def divides (a b : Int) : Prop := ∃ k : Int, b = a * k

theorem four_dvd_square_of_even : ∀ n : Int, even n → divides 4 (n * n) := by
  sorry

end Demo
```

## 📜 Configuration

### Dependencies
The project relies on the following dependencies:
- `openai>=1.0.0`
- `anthropic>=0.30.0`
- `together>=0.2.0`
- `tqdm>=4.66.0`

Ensure these dependencies are installed via `pyproject.toml`.

### Environment Variables
API keys must be set for the respective providers:
- **OpenAI**: Set `OPENAI_API_KEY` in your environment.
- **Anthropic**: Add `ANTHROPIC_API_KEY`.
- **Together**: Configure with `TOGETHER_API_KEY`.

To set API keys:
```bash
export OPENAI_API_KEY="your-openai-key"
export ANTHROPIC_API_KEY="your-anthropic-key"
export TOGETHER_API_KEY="your-together-key"
```

---

## License 📄
This project is licensed under the MIT License. See the [LICENSE](LICENSE) file for details.

---

## Acknowledgments ❤️
Thanks to OpenAI, Anthropic, and Together for access their foundational models which made this project possible.




