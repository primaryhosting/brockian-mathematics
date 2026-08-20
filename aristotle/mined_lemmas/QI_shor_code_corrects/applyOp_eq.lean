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

lemma applyOp_eq (k : Idx) (M : Bool → Bool → ℂ) (ψ : Bits → ℂ) (v : Bits) :
    applyOp k M ψ v
      = ∑ p : Bool × Bool, coefM M p * pauli (sel p.1 k) (sel p.2 k) ψ v := by
  unfold applyOp
  rw [Fintype.sum_bool, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, pauli, sel, if_true, chi_bone, coefM]
  have hup : ∀ s : Bool, v k = s → Function.update v k s = v := by
    intro s hs; rw [← hs]; exact Function.update_eq_self k v
  have hupn : ∀ s : Bool, v k = !s → Function.update v k s = bxor v (bone k) := by
    intro s hs
    have : s = ! v k := by rw [hs]; simp
    rw [this, update_bxor]
  cases hv : v k
  · rw [hup false hv, hupn true (by simp [hv])]
    simp
    ring
  · rw [hup true hv, hupn false (by simp [hv])]
    simp
    ring

/-! ## Sesquilinearity of the inner product -/

