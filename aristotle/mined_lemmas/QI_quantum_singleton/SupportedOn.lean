/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/

def SupportedOn (T : Finset (Fin n)) (E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) : Prop :=
  ∃ F : (Fin n → Fin q) → (Fin n → Fin q) → ℂ,
    (∀ x x' y y' : Fin n → Fin q, (∀ i ∈ T, x i = x' i) → (∀ i ∈ T, y i = y' i) → F x y = F x' y')
      ∧ ∀ x y, E x y = if (∀ i ∉ T, x i = y i) then F x y else 0

/-- The Knill–Laflamme condition: the quantum code spanned by the columns of `M` (a code in
`(ℂ^q)^{⊗n}` of dimension `K`) has distance at least `d`, i.e. for every error operator `E`
acting on fewer than `d` of the `n` qudits, `Mᴴ E M` is a scalar multiple of the identity. -/
