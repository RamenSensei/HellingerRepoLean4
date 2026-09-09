# HellingerRepoLean4

[![Lean verification](https://github.com/RamenSensei/HellingerRepoLean4/actions/workflows/lean.yml/badge.svg)](https://github.com/RamenSensei/HellingerRepoLean4/actions/workflows/lean.yml)

[中文说明](README.zh-CN.md) · [MIT license](LICENSE)

Lean 4 proofs about Boolean noise, Hellinger bounds, bent functions, quadratic phases, and spectral inequalities. The library contains 87 proof modules. The general Hellinger and Courtade–Kumar conjectures remain open; the formal statements specify the proved classes, assumptions, and equality conditions.

## Build and verify

Install Git, elan, and Python 3.10 or later, then run:

```sh
git clone https://github.com/RamenSensei/HellingerRepoLean4.git
cd HellingerRepoLean4
lake exe cache get
lake build
python3 checks/verify.py
```

Lean is pinned to `v4.33.1` and mathlib to `0df444a360eaa60ab8c11dca51a86af692955474`. Transitive dependencies are pinned in `lake-manifest.json`. The initial dependency download requires network access and enough space for mathlib.

Verification checks the source file allowlist, library imports, clean pinned dependencies, and each proof module with warnings as errors. It audits project declarations using the axiom allowlist `propext`, `Classical.choice`, and `Quot.sound`, then independently replays them into a dependency-only kernel environment. Negative controls check that invalid proofs and disallowed trust mechanisms are rejected. Generated results go to the ignored `checks/results/` directory.

## Code guide

| Entry point | Purpose |
|---|---|
| [Hellinger.lean](Hellinger.lean) | Imports every proof module |
| [FunctionContracts](Hellinger/FunctionContracts.lean) | Translation, bent, quadratic, and odd-function interfaces |
| [SpectralContracts](Hellinger/SpectralContracts.lean) | Matrix lifting and spectral comparisons |
| [ProbabilityContracts](Hellinger/ProbabilityContracts.lean) | Probability and information bounds |
| [IndependentChannels](Hellinger/IndependentChannels.lean) | Independent-channel extension |
| [QuotientContracts](Hellinger/QuotientContracts.lean) | Linear-quotient comparison |
| [checks](checks) | Verification driver, axiom audit, kernel replay, and interface checks |

The Lean theorem types and proofs are the reference for this codebase. Kernel verification checks those formal statements; it does not establish correspondence to an external prose document.

## Repository scope

This repository distributes Lean source and the small set of files needed to build, verify, document, and license it. Manuscripts, PDFs, LaTeX sources, research notes, publication packages, and generated logs are excluded. `checks/source_only.py` enforces an explicit tracked-file allowlist in local verification and CI.

Run `python3 checks/verify.py` before submitting changes. Keep the toolchain and dependency pins unless intentionally upgrading them, and explain changes to theorem statements.

Original code and documentation are under the [MIT License](LICENSE). Dependencies retain their own licenses.
