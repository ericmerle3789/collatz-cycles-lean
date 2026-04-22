> **⚠️ Repository archived 2026-04-22 — historical reference only.**
>
> **Active repo** : [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4)
>
> ## ⚠️ Known formula error — do NOT cite the `lean/range-exclusion/` module
>
> The `lean/range-exclusion/` directory of this repository contains a Lean module with a **documented formula error** : the function computed in that module differs from Steiner's `corrSum`, so any result proven in `range-exclusion/` does NOT establish cycle non-existence. See `docs/AUDIT_CORRSUM.md` in this repo for the full diagnostic.
>
> **Rule for readers and reviewers** :
> - ❌ Do NOT copy, cite, or re-use any theorem from `lean/range-exclusion/`.
> - ❌ Do NOT treat the `range-exclusion/` results as valid Collatz cycle non-existence proofs.
> - ✅ The correct results of this archived repo are in `lean/verified/` (k = 3..15, 280 theorems, 0 sorry, 0 axiom, Lean 4.15) and `lean/skeleton/` (Junction Theorem skeleton).
> - ✅ For current and publication-target work, consult [collatz-nocycle-lean4](https://github.com/ericmerle3789/collatz-nocycle-lean4).
>
> ## Relationship to the active repo
>
> `collatz-nocycle-lean4` supersedes this companion repo with :
> - A single consolidated Lean tree (36 files, 393 theorems, 0 sorry).
> - No known formula errors.
> - Central theorem `no_nontrivial_cycle_phase59` depends on `propext, Classical.choice, Quot.sound` only — verified via `#print axioms` on 2026-04-22.
>
> ## Maintenance
>
> No further commits. Issues → [active repo issue tracker](https://github.com/ericmerle3789/collatz-nocycle-lean4/issues).
>
> — Eric Merle, 2026-04-22

---

# collatz-cycles-lean

Companion code for: *Nonexistence of Nontrivial Cycles in the Collatz Dynamics* (Eric Merle, 2026).

## Result

N₀(d(k)) = 0 (no composition achieves corrsum ≡ 0 mod d) is established:
- For k = 3..15 by Lean 4 certified computation (0 sorry, 0 axiom)
- For k ≤ 91 by Hercher (2025), independently
- For k ≥ 18, nonsurjectivity C(S−1,k−1) < d is proved (Lean skeleton)

## Known Issue

The `lean/range-exclusion/` module contains a formula error: it computes a different
function than Steiner's corrsum. This module's results do not establish cycle nonexistence.
The correct proofs are in `lean/verified/` (k = 3..15) and `lean/skeleton/` (nonsurjectivity).
See `docs/AUDIT_CORRSUM.md` for the full analysis.

## Repository structure

```
├── paper/                      Article (md, tex, pdf)
├── lean/
│   ├── verified/               280 theorems, 0 sorry, 0 axiom (Lean 4.15) — CORRECT
│   ├── skeleton/               Junction Theorem (Lean 4.29 + Mathlib) — CORRECT
│   └── range-exclusion/        Range Exclusion — ⚠️ FORMULA ERROR (see WARNING.md)
├── scripts/                    Python verification
├── docs/
│   ├── AUDIT_CORRSUM.md        Corrsum bug analysis
│   └── PROOF_ASSEMBLY.md       Proof assembly
└── VERIFICATION.md             Article ↔ code mapping
```

## Verification

```bash
# Correct proofs (k = 3..15, Steiner formula)
cd lean/verified && lake build    # 280 theorems, 0 sorry

# Python check with correct formula
python scripts/verify_range_exclusion.py
```

## License

Code: MIT. Paper: CC BY 4.0.
