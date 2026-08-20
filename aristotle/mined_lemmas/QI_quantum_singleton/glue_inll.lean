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

lemma glue_inll (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (P : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) (s : Fin a) :
    glue (q := q) e P (e (Sum.inl (Sum.inl s))) = P.1 s := by simp [glue]

