/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace QC

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector of the Hilbert space
`EuclideanSpace ℂ (Fin 8 → Fin 2)`, whose index type is the set of the 256
computational basis states (bit strings of length 8).  The amplitude is `1/√2`
on the all-zeros and the all-ones strings, and `0` elsewhere. -/
noncomputable def ghz8 : EuclideanSpace ℂ (Fin 8 → Fin 2) :=
  WithLp.toLp 2 (fun x : Fin 8 → Fin 2 =>
    if (∀ i, x i = 0) ∨ (∀ i, x i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 8-qubit GHZ state is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hcard : (Finset.univ.filter
      (fun x : Fin 8 → Fin 2 => (∀ i, x i = 0) ∨ (∀ i, x i = 1))).card = 2 := by decide
  have hterm : ∀ x : Fin 8 → Fin 2, ‖ghz8 x‖ ^ 2 =
      if ((∀ i, x i = 0) ∨ (∀ i, x i = 1)) then (1 / 2 : ℝ) else 0 := by
    intro x
    have hx : ghz8 x =
        if (∀ i, x i = 0) ∨ (∀ i, x i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0 := by
      simp [ghz8]
    rw [hx]
    split
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
        div_pow, one_pow, Real.sq_sqrt (by norm_num)]
    · simp
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, hcard]
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

