/-
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 6 Normalized
Category: Quantum Computing
Target: QC.ghz6_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 6-qubit GHZ state `(|000000⟩ + |111111⟩)/√2`, represented as a vector in the
Hilbert space `ℂ^(Fin 6 → Bool)`, whose index type is the set of 6-bit computational
basis labels. -/

theorem ghz6_normalized : ‖ghz6‖ = 1 := by
  have hsq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have key : ‖((1 / Real.sqrt 2 : ℝ) : ℂ)‖ ^ 2 = (1 / 2 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.sqrt 2), div_pow, hsq]
    norm_num
  rw [EuclideanSpace.norm_eq]
  have hne : (fun _ : Fin 6 => false) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  have h : ∀ b : Fin 6 → Bool, ‖(ghz6.ofLp) b‖ ^ 2 =
      (if b = (fun _ => false) then (1 / 2 : ℝ) else 0) +
      (if b = (fun _ => true) then (1 / 2 : ℝ) else 0) := by
    intro b
    by_cases h1 : b = (fun _ => false)
    · subst h1
      simp only [ghz6, WithLp.ofLp_toLp, if_neg hne, if_pos, key, add_zero]
    · by_cases h2 : b = (fun _ => true)
      · subst h2
        simp only [ghz6, WithLp.ofLp_toLp, if_neg h1, if_pos, key, zero_add]
      · simp [ghz6, h1, h2]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  norm_num

end QC

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

