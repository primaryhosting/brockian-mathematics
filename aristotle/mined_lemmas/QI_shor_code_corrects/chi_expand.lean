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

lemma chi_expand (u : Bits) (t : Fin 3 → Bool) :
    chi u (expand t) = ∏ m : Fin 3, (if t m && wpar u m then (-1 : ℤ) else 1) := by
  unfold chi
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl ?_
  intro m _
  rw [Fin.prod_univ_three]
  exact sign_three (u (m, 0)) (u (m, 1)) (u (m, 2)) (t m)

