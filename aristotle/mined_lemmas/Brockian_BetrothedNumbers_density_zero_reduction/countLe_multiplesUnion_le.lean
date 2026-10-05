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

theorem countLe_multiplesUnion_le (D : Finset ℕ) (x : ℕ) :
    (countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x : ℝ)
      ≤ (x : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
  classical
  have hset : {n : ℕ | ∃ d ∈ D, d ∣ n} = ⋃ d ∈ D, {n : ℕ | d ∣ n} := by
    ext n; simp
  have h1 : countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x ≤ ∑ d ∈ D, countLe {n : ℕ | d ∣ n} x := by
    rw [hset]; exact countLe_biUnion_le D _ x
  have h2 : (∑ d ∈ D, countLe {n : ℕ | d ∣ n} x : ℝ) ≤ ∑ d ∈ D, ((x : ℝ) / d + 1) := by
    refine Finset.sum_le_sum ?_
    intro d _
    have hd : (countLe {n : ℕ | d ∣ n} x : ℝ) ≤ ((x / d : ℕ) : ℝ) + 1 := by
      exact_mod_cast countLe_multiples_le d x
    have : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
    linarith
  have h3 : (∑ d ∈ D, ((x : ℝ) / d + 1)) = (x : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [div_eq_mul_inv, mul_comm]
  have h1' : (countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x : ℝ)
      ≤ (∑ d ∈ D, countLe {n : ℕ | d ∣ n} x : ℝ) := by exact_mod_cast h1
  linarith [h1', h2, h3.le, h3.ge]

/-! ## Reusable density-zero criteria -/

/-- Density zero is equivalent to the "for every `ε > 0`, eventually `count ≤ ε x`" formulation. -/
