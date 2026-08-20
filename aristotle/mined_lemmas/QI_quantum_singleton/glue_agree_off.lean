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

lemma glue_agree_off (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (P Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) :
    (∀ i ∉ firstBlock e, glue (q := q) e P i = glue (q := q) e Q i) ↔ P.2 = Q.2 := by
  constructor
  · intro h
    have hb : ∀ s : Fin b, e (Sum.inl (Sum.inr s)) ∉ firstBlock e := by
      intro s hs
      rw [mem_firstBlock_iff] at hs
      obtain ⟨t, ht⟩ := hs
      simpa using e.injective ht
    have hc : ∀ s : Fin c, e (Sum.inr s) ∉ firstBlock e := by
      intro s hs
      rw [mem_firstBlock_iff] at hs
      obtain ⟨t, ht⟩ := hs
      simpa using e.injective ht
    refine Prod.ext ?_ ?_
    · funext s
      simpa [glue] using h _ (hb s)
    · funext s
      simpa [glue] using h _ (hc s)
  · intro h i hi
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s
    · exact absurd ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩) hi
    · have h1 : P.2.1 = Q.2.1 := congrArg Prod.fst h
      simp [glue, h1]
    · have h2 : P.2.2 = Q.2.2 := congrArg Prod.snd h
      simp [glue, h2]

