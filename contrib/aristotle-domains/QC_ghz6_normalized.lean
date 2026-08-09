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

namespace QC

/-- The amplitude function of the 6-qubit GHZ state
`(|000000⟩ + |111111⟩)/√2`: a computational basis state `x : Fin 6 → Fin 2`
gets amplitude `1/√2` if it is all-zeros or all-ones, and `0` otherwise. -/
noncomputable def ghz6Fun : (Fin 6 → Fin 2) → ℂ :=
  fun x =>
    if x = (fun _ => 0) then (1 : ℂ) / (Real.sqrt 2 : ℂ)
    else if x = (fun _ => 1) then (1 : ℂ) / (Real.sqrt 2 : ℂ)
    else 0

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, as a vector in the
`2^6`-dimensional complex Hilbert space indexed by the bit strings `Fin 6 → Fin 2`. -/
noncomputable def ghz6 : EuclideanSpace ℂ (Fin 6 → Fin 2) := WithLp.toLp 2 ghz6Fun

/-- The 6-qubit GHZ state is a unit vector. -/
theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hne : (fun _ => (0 : Fin 2)) ≠ (fun _ : Fin 6 => (1 : Fin 2)) := by
    intro h
    have := congrFun h 0
    simp at this
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ x : (Fin 6 → Fin 2), ‖ghz6.ofLp x‖ ^ 2
      = ‖ghz6.ofLp (fun _ => 0)‖ ^ 2 + ‖ghz6.ofLp (fun _ => 1)‖ ^ 2 := by
    refine Finset.sum_eq_add _ _ hne ?_ ?_ ?_
    · intro c _ hc
      simp [ghz6, ghz6Fun, hc.1, hc.2]
    · simp
    · simp
  have hv : ‖((1 : ℂ) / (Real.sqrt 2 : ℂ))‖ ^ 2 = 1 / 2 := by
    rw [norm_div]
    simp [Complex.norm_real, abs_of_pos h2, Real.sq_sqrt]
  rw [hsum]
  simp only [ghz6, ghz6Fun, WithLp.ofLp_toLp, if_neg hne.symm, if_true]
  rw [hv]
  norm_num

end QC

