import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

lemma KL_off (p q : P1) (i j : Fin 9) :
    inner ℂ (op p i (cw false)) (op q j (cw true)) = 0 := by
  rw [inner_op_cw]
  split
  · rename_i hc
    have h : ∀ t : T, conj (sgnc false t * ampP p i (emb t)) * (sgnc true t * ampP q j (emb t))
        = sgnc true t * (conj (ampP p i (emb t)) * ampP q j (emb t)) := by
      intro t; rw [sgnc_false]; simp; ring
    rw [Finset.sum_congr rfl (fun t _ => h t), off_sum p q i j hc, mul_zero]
  · rfl

