import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The development below follows the classical Galois-theoretic argument: the quintic
`X ^ 5 - 4 * X + 2` is irreducible over `ℚ` (Eisenstein at `2`), it has exactly two real roots
and five complex roots, hence its Galois group is the full symmetric group `S₅`, which is not
solvable.  Consequently no complex root of it is expressible by radicals.
-/

namespace Math

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

section Quintic

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`, over an arbitrary commutative ring. -/

theorem abel_ruffini_deg5 :
    ∃ q : ℚ[X], q.Monic ∧ q.natDegree = 5 ∧ ¬ IsSolvable q.Gal ∧
      (∃ x : ℂ, aeval x q = 0) ∧
      (∀ x : ℂ, aeval x q = 0 → ¬ IsSolvableByRad ℚ x) := by
  refine ⟨quintic ℚ 4 2, monic_quintic 4 2, natDegree_quintic 4 2, ?_, ?_, ?_⟩
  · exact not_solvable_gal_quintic 4 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide)
  · obtain ⟨x, hx⟩ := (IsAlgClosed.splits (quintic ℂ 4 2)).exists_eval_eq_zero
      (by simp [degree_quintic])
    rw [← map_quintic 4 2 (algebraMap ℚ ℂ), eval_map] at hx
    exact ⟨x, hx⟩
  · intro x hx
    exact not_solvable_by_rad_quintic 4 2 2 x hx (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide)

end Math

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

