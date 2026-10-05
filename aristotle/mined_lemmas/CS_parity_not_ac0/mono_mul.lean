import Mathlib

/-!
# Parity Not Ac 0
Category: Frontier Cs
Target: CS.parity_not_ac0
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators

namespace CS

/-- The field with three elements. -/
abbrev F3 := ZMod 3

/-- The Boolean cube on `n` coordinates. -/
abbrev Cube (n : ℕ) := Fin n → Bool

/-- `±1` encoding of a Boolean value inside `F3`. -/

lemma mono_mul {n : ℕ} (A B : Finset (Fin n)) :
    mono A * mono B = mono (symmDiff A B) := by
  funext x
  have hA : (∏ i ∈ A, sgn (x i)) = (∏ i ∈ A \ B, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) := by
    rw [← Finset.prod_sdiff (show A ∩ B ⊆ A from Finset.inter_subset_left)]
    congr 1
    · congr 1
      ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
      tauto
  have hB : (∏ i ∈ B, sgn (x i)) = (∏ i ∈ B \ A, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) := by
    rw [← Finset.prod_sdiff (show A ∩ B ⊆ B from Finset.inter_subset_right)]
    congr 1
    · congr 1
      ext i; simp [Finset.mem_sdiff, Finset.mem_inter]
      tauto
  have hsq : (∏ i ∈ A ∩ B, sgn (x i)) * (∏ i ∈ A ∩ B, sgn (x i)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    simp
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp [Finset.mem_sdiff] at ha hb
    exact hb.2 ha.1
  have hsymm : symmDiff A B = (A \ B) ∪ (B \ A) := rfl
  have hsq2 : (∏ i ∈ A ∩ B, sgn (x i)) ^ 2 = 1 := by rw [sq]; exact hsq
  simp only [Pi.mul_apply, mono, hA, hB, hsymm, Finset.prod_union hdisj]
  ring_nf
  rw [hsq2]
  ring

/-- The `F3`-submodule of functions on the cube spanned by monomials of degree at most `D`. -/
