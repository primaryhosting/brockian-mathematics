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

lemma mul_mem_Deg {n a b : ℕ} {f g : Cube n → F3} (hf : f ∈ Deg n a) (hg : g ∈ Deg n b) :
    f * g ∈ Deg n (a + b) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨A, hA, rfl⟩ := hf
      induction hg using Submodule.span_induction with
      | mem g hg =>
          obtain ⟨B, hB, rfl⟩ := hg
          rw [mono_mul]
          refine mono_mem_Deg ?_
          calc (symmDiff A B).card ≤ (A ∪ B).card := by
                apply Finset.card_le_card
                intro i hi
                simp only [Finset.mem_union]
                have : i ∈ A \ B ∪ B \ A := hi
                simp [Finset.mem_union, Finset.mem_sdiff] at this
                tauto
            _ ≤ A.card + B.card := Finset.card_union_le _ _
            _ ≤ a + b := Nat.add_le_add hA hB
      | zero => simpa using Submodule.zero_mem _
      | add g1 g2 _ _ ih1 ih2 =>
          rw [mul_add]; exact Submodule.add_mem _ ih1 ih2
      | smul c g _ ih =>
          have : mono A * (c • g) = c • (mono A * g) := by
            funext x; simp [mul_comm, mul_left_comm]
          rw [this]; exact Submodule.smul_mem _ _ ih
  | zero => simpa using Submodule.zero_mem _
  | add f1 f2 _ _ ih1 ih2 => rw [add_mul]; exact Submodule.add_mem _ ih1 ih2
  | smul c f _ ih =>
      have : (c • f) * g = c • (f * g) := by funext x; simp [mul_assoc]
      rw [this]; exact Submodule.smul_mem _ _ ih

/-- Every function on the cube is a combination of monomials of degree at most `n`. -/
