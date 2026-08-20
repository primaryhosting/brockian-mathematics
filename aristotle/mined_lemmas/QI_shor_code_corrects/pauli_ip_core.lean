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

lemma pauli_ip_core {k l : Idx} {x z x' z' : Bits}
    (hx : ∀ q, q ≠ k → x q = false) (hz : ∀ q, q ≠ k → z q = false)
    (hx' : ∀ q, q ≠ l → x' q = false) (hz' : ∀ q, q ≠ l → z' q = false) :
    (∀ a b : Bool, a ≠ b → ip (pauli x z (psi a)) (pauli x' z' (psi b)) = 0) ∧
      ip (pauli x z (psi true)) (pauli x' z' (psi true))
        = ip (pauli x z (psi false)) (pauli x' z' (psi false)) := by
  have hsuppu : ∀ q, (bxor z z') q = true → q = k ∨ q = l := by
    intro q hq
    by_contra hcon
    push_neg at hcon
    rw [bxor, hz q hcon.1, hz' q hcon.2] at hq
    exact Bool.noConfusion hq
  have hsuppd : ∀ q, (bxor x x') q = true → q = k ∨ q = l := by
    intro q hq
    by_contra hcon
    push_neg at hcon
    rw [bxor, hx q hcon.1, hx' q hcon.2] at hq
    exact Bool.noConfusion hq
  by_cases hd : bxor x x' = bzero
  · have hxx : x = x' := (bxor_eq_bzero_iff x x').1 hd
    subst hxx
    obtain ⟨m, hm⟩ := exists_wpar_false hsuppu
    constructor
    · intro a b hab
      rw [ip_pauli, S_of_eq]
      have hxorab : xor a b = true := by revert hab; revert a b; decide
      have hzero : (∏ m : Fin 3, (if xor (wpar (bxor z z') m) (xor a b) then (0 : ℤ) else 2)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ m) (by simp [hm, hxorab])
      rw [hzero]
      simp
    · rw [ip_pauli, ip_pauli, S_of_eq, S_of_eq]
      norm_num
  · have hnb : ¬ Blocky (bxor x x') := not_blocky_of_support hd hsuppd
    constructor
    · intro a b _
      rw [ip_pauli, S_of_not_blocky _ _ _ _ _ hnb]
      simp
    · rw [ip_pauli, ip_pauli, S_of_not_blocky _ _ _ _ _ hnb, S_of_not_blocky _ _ _ _ _ hnb]

/-! ## Orthonormality of the logical basis -/

