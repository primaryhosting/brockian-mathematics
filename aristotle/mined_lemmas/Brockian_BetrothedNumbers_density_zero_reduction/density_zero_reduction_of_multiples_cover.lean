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

theorem density_zero_reduction_of_multiples_cover
    (cover : ℝ → Finset ℕ)
    (hsub : ∀ ε : ℝ, 0 < ε → betrothed ⊆ {n : ℕ | ∃ d ∈ cover ε, d ∣ n})
    (hsum : ∀ ε : ℝ, 0 < ε → ∑ d ∈ cover ε, (1 : ℝ) / d ≤ ε / 2) :
    HasDensityZero betrothed :=
  hasDensityZero_of_multiples_cover cover hsub hsum

end BetrothedNumbers
end Brockian

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

