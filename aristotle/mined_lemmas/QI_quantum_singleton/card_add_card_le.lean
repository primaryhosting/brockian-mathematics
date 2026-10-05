import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

open Module

/-- The symplectic (phase-space) representation of the Pauli group on `n` qudits over the
finite field `F`: a Pauli operator is recorded by its `X`-part and `Z`-part on each qudit. -/
abbrev PSpace (F : Type*) (n : ℕ) := Fin n → F × F

variable {F : Type*} [Field F] {n : ℕ}

/-- The symplectic form on the phase space, as a bilinear map.  Two Pauli operators commute
iff their symplectic form vanishes. -/

lemma card_add_card_le {S : Submodule F (PSpace F n)} {d : ℕ} {A B : Finset (Fin n)}
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v) (hA : A.card < d) (hB : B.card < d)
    (hAB : Disjoint A B) :
    A.card + B.card ≤ finrank F S := by
  classical
  set C : Finset (Fin n) := (A ∪ B)ᶜ with hC
  have hBC : B ∪ C = Aᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, Finset.mem_union, not_or]
    constructor
    · rintro (hi | ⟨hi, -⟩)
      · exact Finset.disjoint_right.mp hAB hi
      · exact hi
    · intro hi
      by_cases hb : i ∈ B
      · exact Or.inl hb
      · exact Or.inr ⟨hi, hb⟩
  have hAC : A ∪ C = Bᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, Finset.mem_union, not_or]
    constructor
    · rintro (hi | ⟨-, hi⟩)
      · exact Finset.disjoint_left.mp hAB hi
      · exact hi
    · intro hi
      by_cases ha : i ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨ha, hi⟩
  have hdBC : Disjoint B C := by
    rw [Finset.disjoint_right]
    intro i hi hiB
    simp only [hC, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.2 hiB
  have hdAC : Disjoint A C := by
    rw [Finset.disjoint_right]
    intro i hi hiA
    simp only [hC, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.1 hiA
  have k1 := key (S := S) (d := d) A hd hA
  have k2 := key (S := S) (d := d) B hd hB
  have s1 := finrank_add_le_of_disjoint S hdBC
  have s2 := finrank_add_le_of_disjoint S hdAC
  rw [hBC] at s1
  rw [hAC] at s2
  omega

