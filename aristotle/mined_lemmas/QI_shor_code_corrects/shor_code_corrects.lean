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

theorem shor_code_corrects :
    (∀ a b : Bool, ip (psi a) (psi b) = if a = b then 1 else 0) ∧
      ∀ (k l : Idx) (M N : Bool → Bool → ℂ), ∃ w : ℂ, ∀ a b : Bool,
        ip (applyOp k M (psi a)) (applyOp l N (psi b)) = if a = b then w else 0 := by
  refine ⟨ip_psi, ?_⟩
  intro k l M N
  refine ⟨ip (applyOp k M (psi false)) (applyOp l N (psi false)), ?_⟩
  intro a b
  by_cases hab : a = b
  · subst hab
    cases a
    · rfl
    · rw [ip_applyOp_expand, ip_applyOp_expand]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [(pauli_ip_core (sel_support p.1 k) (sel_support p.2 k) (sel_support q.1 l)
        (sel_support q.2 l)).2]
  · simp only [if_neg hab]
    rw [ip_applyOp_expand]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    rw [(pauli_ip_core (sel_support p.1 k) (sel_support p.2 k) (sel_support q.1 l)
      (sel_support q.2 l)).1 a b hab, mul_zero]

/-! ## Sanity checks on the model of single-qubit operators -/

/-- The identity matrix acts as the identity operator. -/
