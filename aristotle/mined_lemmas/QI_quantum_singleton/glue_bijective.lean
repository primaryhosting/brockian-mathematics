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

lemma glue_bijective (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) :
    Function.Bijective (glue (q := q) (a := a) (b := b) (c := c) e) := by
  constructor
  · intro P Q h
    obtain ⟨u, v, w⟩ := P
    obtain ⟨u', v', w'⟩ := Q
    have h1 : u = u' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inl (Sum.inl s)))
    have h2 : v = v' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inl (Sum.inr s)))
    have h3 : w = w' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inr s))
    simp [h1, h2, h3]
  · intro x
    refine ⟨(fun s => x (e (Sum.inl (Sum.inl s))), fun s => x (e (Sum.inl (Sum.inr s))),
      fun s => x (e (Sum.inr s))), ?_⟩
    funext i
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s <;> simp [glue]

