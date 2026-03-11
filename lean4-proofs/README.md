# Lean 4 Formal Verification

Machine-checked proofs for key lemmas in the ScrollCipher paper, verified with **Lean 4.29.0** and **Mathlib**.

## Proof Modules

| File | Paper Reference | What is proved |
|------|----------------|----------------|
| `MarkovMixing.lean` | Proposition 1 | Spectral gap positivity, TV distance bounds (λ₂^5 < 0.003, λ₂^10 < 10⁻⁵), mixing convergence |
| `Correctness.lean` | Theorem 2 | Precision error bounds, glyph lookup sufficiency at 4/7/17 sig figs, phase-by-phase correctness via analytical override, inductive correctness |
| `GameHopping.lean` | Theorem 1 | IND-CPA advantage bound structure, SCIP dominance, nonce collision bound, combined non-SCIP term bound |

## Building

```bash
# Install elan (Lean version manager)
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y

# Set up project (downloads Mathlib — ~2GB, takes several minutes)
cp lakefile.toml lean-toolchain ScrollCipherProofs.lean ../  # or set up a fresh project
mkdir -p ScrollCipherProofs
cp MarkovMixing.lean Correctness.lean GameHopping.lean ScrollCipherProofs/
lake update
lake exe cache get
lake build
```

A successful build with `Build completed successfully` and zero errors confirms all proofs are valid.

## Axioms

One explicit axiom is used in `MarkovMixing.lean`: the standard spectral bound for reversible Markov chains (that TV distance after k steps is bounded by |λ₂|^k). All concrete numerical bounds (λ₂^5, λ₂^10, etc.) are fully proved by `norm_num`.
