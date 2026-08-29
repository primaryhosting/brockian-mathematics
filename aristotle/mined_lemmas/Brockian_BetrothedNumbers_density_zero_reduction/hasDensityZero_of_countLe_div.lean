/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter

/-!
# Density Zero Reduction for Betrothed (Quasi-Amicable) Numbers

Pollack's theorem asserts that the set of betrothed numbers has asymptotic density zero.  This
file decomposes that statement into Mathlib-sized pieces: it fixes the definitions, proves the
weakest reusable analytic-number-theory lemmas unconditionally, and then states and proves the
*reduction* theorem, which isolates exactly what analytic input is still missing.  No claim of
the unconditional density theorem is made.

## Dependency graph

```
properDivisorSum ── IsBetrothedPair ── betrothed
                                        │
                                        ├── isBetrothedPair_comm
                                        ├── betrothed_partner_unique
                                        ├── not_prime_of_betrothed   (uses
                                        │     Nat.sum_properDivisors_eq_one_iff_prime)
                                        ├── two_le_of_betrothed
                                        └── isBetrothedPair_48_75 ── betrothed_nonempty

sectionLe ── sectionLe_subset_Iic ── sectionLe_finite
     │                                    │
     └── countLe ─┬─ countLe_mono ────────┘
                  ├─ countLe_le_succ
                  ├─ countLe_union_le
                  ├─ countLe_le_ncard_of_finite
                  ├─ countLe_empty ── countLe_biUnion_le
                  └─ countLe_multiples_le ─┐
                                           ├── countLe_multiplesUnion_le
                    countLe_biUnion_le ────┘        │
                                                    │
HasDensityZero ── hasDensityZero_iff ─┬── HasDensityZero.subset            │
                                      ├── hasDensityZero_of_finite         │
                                      ├── HasDensityZero.union             │
                                      ├── hasDensityZero_of_countLe_div    │
                                      └── hasDensityZero_of_multiples_cover ┘
                                                    │
   HasDensityZero.subset + hasDensityZero_of_finite │
                     └── hasDensityZero_of_subset_union_finite
                                                    │
                                                    ▼
              density_zero_reduction                (main target)
              density_zero_reduction_of_div_bound   (variant, via the finite-perturbation
                                                     and `C x / f x` criteria)
              density_zero_reduction_of_multiples_cover
                                                    (variant, via the sifting criterion)
```

## What remains for the full theorem

The only unproved ingredient of Pollack's theorem is the construction of the covering family:
for each `ε > 0`, a set (or a finite set of moduli) capturing every betrothed number outside a
sparse remainder.  Feeding such a construction into `density_zero_reduction` (or one of its two
variants) yields `HasDensityZero betrothed`.
-/

namespace Brockian
namespace BetrothedNumbers

/-! ## Basic definitions -/

/-- The sum of the proper divisors of `n`, usually written `s(n) = σ(n) - n`. -/

theorem hasDensityZero_of_countLe_div {A : Set ℕ} (C : ℝ) (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hbound : ∀ᶠ x : ℕ in atTop, (countLe A x : ℝ) ≤ C * x / f x) :
    HasDensityZero A := by
  rw [hasDensityZero_iff]
  intro ε hε
  have hfpos : ∀ᶠ x : ℕ in atTop, max (C / ε) 1 < f x := hf.eventually_gt_atTop _
  filter_upwards [hbound, hfpos, eventually_ge_atTop 1] with x hx hfx _
  have hf1 : (1 : ℝ) < f x := lt_of_le_of_lt (le_max_right _ _) hfx
  have hf0 : (0 : ℝ) < f x := by linarith
  have hCf : C / ε < f x := lt_of_le_of_lt (le_max_left _ _) hfx
  have hxpos : (0 : ℝ) ≤ (x : ℝ) := by positivity
  rw [div_lt_iff₀ hε] at hCf
  have hdiv : C * x / f x ≤ ε * x := by
    rw [div_le_iff₀ hf0]
    nlinarith
  linarith

/-- Sifting criterion: a set that, for every `ε > 0`, can be covered by the multiples of the
elements of a finite set `D_ε` whose reciprocals sum to at most `ε / 2`, has density zero. -/
