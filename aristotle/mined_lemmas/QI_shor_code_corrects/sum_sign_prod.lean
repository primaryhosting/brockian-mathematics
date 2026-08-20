/-
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Statement: The 9-qubit Shor code corrects an arbitrary single-qubit error.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace QI

/-- Index set of the nine qubits: three blocks of three. -/
abbrev Idx : Type := Fin 3 × Fin 3

/-- Computational basis states of the nine qubits are bit strings. -/
abbrev Bits : Type := Idx → Bool

/-- Pointwise `xor` of two bit strings. -/

lemma sum_sign_prod (a : Fin 3 → Bool) :
    (∑ t : Fin 3 → Bool, ∏ m : Fin 3, (if t m && a m then (-1 : ℤ) else 1))
      = ∏ m : Fin 3, (if a m then (0 : ℤ) else 2) := by
  have := Finset.prod_univ_sum (ι := Fin 3) (κ := fun _ => Bool) (fun _ => Finset.univ)
    (fun m s => (if s && a m then (-1 : ℤ) else 1))
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  refine Finset.prod_congr rfl ?_
  intro m _
  simp only [Fintype.sum_bool]
  cases a m <;> norm_num

/-! ## The core computation -/

/-- Turning a `±1` prefactor into the product form. -/
