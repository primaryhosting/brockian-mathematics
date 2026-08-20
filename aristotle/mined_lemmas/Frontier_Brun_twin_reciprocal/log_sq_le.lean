import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma log_sq_le : ∃ C : ℝ, 0 < C ∧
    ∀ m : ℕ, 1 ≤ m → ((Nat.log 2 m : ℝ)) ^ 2 ≤ C * Real.sqrt m := by
  obtain ⟨C, hCpos, hC⟩ := poly_le_geom 4
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hCpos, fun m hm => ?_⟩
  set l := Nat.log 2 m with hl
  have h1 : (2 : ℕ) ^ l ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ)) ^ l ≤ (m : ℝ) := by exact_mod_cast h1
  have h3 : (l : ℝ) ^ 4 ≤ C * (m : ℝ) := by
    have := hC l
    nlinarith [hCpos, h2]
  have h4 : Real.sqrt ((l : ℝ) ^ 4) ≤ Real.sqrt (C * m) := Real.sqrt_le_sqrt h3
  rw [show ((l : ℝ) ^ 4) = ((l : ℝ) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity),
    Real.sqrt_mul hCpos.le] at h4
  exact h4

