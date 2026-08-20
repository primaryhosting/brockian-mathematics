/-
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Steane Code
Category: Frontier Qi
Target: QI.steane_code
Statement: The 7-qubit Steane (CSS) code corrects any single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

/-! ## Basic setting: 7 qubits, computational basis indexed by bit strings -/

/-- Labels of the computational basis of `(ℂ²)^{⊗7}`: bit strings of length 7. -/
abbrev Bits := Fin 7 → ZMod 2

/-- Syndrome values: three bits (one per parity check of each CSS type). -/
abbrev Chk := Fin 3 → ZMod 2

/-- A state of the 7-qubit register, in the computational basis. -/
abbrev State := Bits → ℂ

/-- Mod-2 inner product of two bit strings. -/

theorem steane_code_arbitrary_error (i : Fin 7) (c : ZMod 2 → ZMod 2 → ℂ) (psi : State)
    (hpsi : IsCode psi) (a b : ZMod 2) :
    Rec (decode (syn (pauliVec a i))) (decode (syn (pauliVec b i)))
        (syndProj (syn (pauliVec a i)) (syn (pauliVec b i)) (SingleQubitError i c psi))
      = c a b • psi := by
  have hdec : ∀ a' : ZMod 2, decode (syn (pauliVec a' i)) = pauliVec a' i := by
    intro a'
    refine decode_syn_of_weight_le_one _ ⟨i, ?_⟩
    intro j hj
    simp [pauliVec, hj]
  have hproj : syndProj (syn (pauliVec a i)) (syn (pauliVec b i)) (SingleQubitError i c psi)
      = c a b • Err (pauliVec a i) (pauliVec b i) psi := by
    simp only [SingleQubitError, map_sum, map_smul, syndProj_Err _ _ _ _ _ hpsi]
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hb'
        rw [if_neg, smul_zero]
        rintro ⟨-, h2⟩
        exact hb' (syn_pauliVec_injective i b b' h2).symm
      · intro hb; exact absurd (Finset.mem_univ b) hb
    · intro a' _ ha'
      refine Finset.sum_eq_zero ?_
      intro b' _
      rw [if_neg, smul_zero]
      rintro ⟨h1, -⟩
      exact ha' (syn_pauliVec_injective i a a' h1).symm
    · intro ha; exact absurd (Finset.mem_univ a) ha
  rw [hproj, hdec, hdec, Rec_smul, Rec_Err]

end QI

