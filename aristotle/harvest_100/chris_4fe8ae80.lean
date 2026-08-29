import Mathlib

/-!
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Computational basis states of an 8-qubit register: bit strings of length 8. -/
abbrev Qubits8 := Fin 8 → Fin 2

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`, as a vector of the Hilbert space
`EuclideanSpace ℂ Qubits8`: its amplitude is `1/√2` on the all-zeros and all-ones
basis states, and `0` elsewhere. -/
noncomputable def ghz8 : EuclideanSpace ℂ Qubits8 :=
  WithLp.toLp 2 (fun b => if (∀ i, b i = 0) ∨ (∀ i, b i = 1) then (1 : ℂ) / Real.sqrt 2 else 0)

/-- The 8-qubit GHZ state is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set c0 : Qubits8 := fun _ => 0 with hc0
  set c1 : Qubits8 := fun _ => 1 with hc1
  have hcne : c0 ≠ c1 := by
    intro h
    have := congrFun h 0
    simp [hc0, hc1] at this
  -- each amplitude squares to `1/2` on the two GHZ basis states and to `0` elsewhere
  have key : ∀ b : Qubits8,
      ‖ghz8.ofLp b‖ ^ 2 = if b ∈ ({c0, c1} : Finset Qubits8) then (1 / 2 : ℝ) else 0 := by
    intro b
    have hiff : ((∀ i, b i = 0) ∨ (∀ i, b i = 1)) ↔ b ∈ ({c0, c1} : Finset Qubits8) := by
      simp [hc0, hc1, funext_iff]
    simp only [ghz8, WithLp.ofLp_toLp, hiff]
    split
    · rw [norm_div, norm_one, div_pow, one_pow]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2), hs2]
    · simp
  rw [EuclideanSpace.norm_eq]
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.card_insert_of_notMem (by simpa using hcne), Finset.card_singleton]
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

