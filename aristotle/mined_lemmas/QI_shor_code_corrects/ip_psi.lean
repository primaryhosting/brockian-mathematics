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

lemma ip_psi (a b : Bool) : ip (psi a) (psi b) = if a = b then 1 else 0 := by
  have h0 : psi a = pauli bzero bzero (psi a) := by
    funext v; simp [pauli]
  have h1 : psi b = pauli bzero bzero (psi b) := by
    funext v; simp [pauli]
  rw [h0, h1, ip_pauli]
  have hzz : bxor bzero bzero = bzero := by funext q; simp [bxor, bzero]
  rw [hzz]
  have hs : (∑ v : Bits, chi bzero v * f a (bxor v bzero) * f b (bxor v bzero))
      = ∏ m : Fin 3, (if xor (wpar bzero m) (xor a b) then (0 : ℤ) else 2) := by
    have := S_of_eq bzero bzero a b
    simpa using this
  rw [hs]
  have hw : ∀ m : Fin 3, wpar bzero m = false := by intro m; simp [wpar, bzero]
  cases a <;> cases b <;> simp [hw]

/-! ## Expanding an arbitrary single-qubit operator in the Pauli basis -/

/-- `sel b k` is `e_k` if `b` is true, and the zero string otherwise. -/
