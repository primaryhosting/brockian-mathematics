import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/

theorem fermatForm_nonsingular (n : ℕ) (hn : 2 ≤ n) :
    IsNonsingularPlaneCurve (fermatForm n) := by
  intro v hv
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by
    simpa using (by omega : n ≠ 0)
  have hn1 : n - 1 ≠ 0 := by omega
  have e0 : v 0 = 0 := by
    have h := hv 0
    rw [pderiv_fermatForm_zero] at h
    simp only [map_mul, map_pow, aeval_X, map_natCast] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  have e1 : v 1 = 0 := by
    have h := hv 1
    rw [pderiv_fermatForm_one] at h
    simp only [map_mul, map_pow, aeval_X, map_natCast] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  have e2 : v 2 = 0 := by
    have h := hv 2
    rw [pderiv_fermatForm_two] at h
    simp only [map_neg, map_mul, map_pow, aeval_X, map_natCast, neg_eq_zero] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-! ### Finiteness of the rational points -/

