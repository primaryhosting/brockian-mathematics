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

lemma inner_op_cw (p q : P1) (i j : Fin 9) (k l : Bool) :
    inner ℂ (op p i (cw k)) (op q j (cw l)) =
      if compat p q i j = true then
        (1/8 : ℂ) * ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t))
      else 0 := by
  have key : inner ℂ (∑ t : T, (sgnc k t * ampP p i (emb t)) • eb (flP p i (emb t)))
                     (∑ t : T, (sgnc l t * ampP q j (emb t)) • eb (flP q j (emb t)))
      = if compat p q i j = true then
          ∑ t : T, conj (sgnc k t * ampP p i (emb t)) * (sgnc l t * ampP q j (emb t))
        else 0 := by
    rw [sum_inner]
    simp only [inner_smul_left, inner_sum, inner_smul_right, inner_eb, flP_emb_eq_iff,
      Finset.mul_sum]
    exact double_sum_delta _ _ _
  rw [op_cw, op_cw, inner_smul_left, inner_smul_right, key, ← mul_assoc, nrm_sq]
  split <;> simp

