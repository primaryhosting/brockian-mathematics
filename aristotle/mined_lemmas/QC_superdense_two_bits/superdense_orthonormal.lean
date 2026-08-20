/-
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
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

set_option grind.warning false

namespace QC

/-- The amplitude `1/√2` of a maximally entangled two-qubit state. -/

theorem superdense_orthonormal (m m' : Fin 2 × Fin 2) :
    (∑ p : Fin 2 × Fin 2, (starRingEnd ℂ) (encode m p) * encode m' p) =
      if m = m' then 1 else 0 := by
  have hstar : (starRingEnd ℂ) amp = amp := by
    simp [amp, Complex.conj_ofReal]
  obtain ⟨a, b⟩ := m
  obtain ⟨a', b'⟩ := m'
  have hsum : ∀ f : Fin 2 × Fin 2 → ℂ,
      (∑ p : Fin 2 × Fin 2, f p) = f (0,0) + f (0,1) + f (1,0) + f (1,1) := by
    intro f
    simp [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc]
  rw [hsum]
  simp only [encode_apply]
  have h2 : amp * amp = 1 / 2 := amp_sq
  fin_cases a <;> fin_cases b <;> fin_cases a' <;> fin_cases b' <;>
    simp [hstar] <;> linear_combination (2 : ℂ) * h2

end QC

