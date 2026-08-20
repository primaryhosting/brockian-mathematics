/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Arrow's impossibility theorem

A *ranking* of a type `A` of alternatives is a strict total order (transitive, total on
distinct elements, asymmetric).  A *social welfare function* is a map
`F : (V → Ranking A) → Ranking A` sending each profile of individual rankings (one for each
voter `i : V`) to a social ranking.

We prove: if `V` is a finite nonempty set of voters, `A` has at least three elements, and `F`
satisfies unanimity (Pareto) and independence of irrelevant alternatives (IIA), then `F` has a
dictator.  Equivalently, no `F` satisfies unanimity, IIA and non-dictatorship
(`Frontier.arrow_impossibility`).

Mathlib does not contain Arrow's theorem, so the development is from scratch.  The proof is the
classical one: a *field expansion* lemma (semi-decisiveness over one pair implies decisiveness
over all pairs) followed by a *group contraction* lemma (a decisive coalition splits into two
parts, one of which is decisive), and then induction on the size of the coalition starting from
the grand coalition, which is decisive by unanimity.
-/

namespace Frontier

/-- A strict total order ("ranking") on the type of alternatives `A`. -/
structure Ranking (A : Type*) where
  /-- The strict preference relation. -/
  rel : A → A → Prop
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_total : ∀ {x y}, x ≠ y → rel x y ∨ rel y x
  rel_asymm : ∀ {x y}, rel x y → ¬ rel y x

namespace Ranking

variable {A : Type*}


lemma decisiveAll_split [DecidableEq V] (hPar : Pareto F) (hIIA : IIA F)
    (h3 : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z) {S₁ S₂ : Finset V}
    (hdisj : Disjoint S₁ S₂) (h : DecisiveAll F (S₁ ∪ S₂)) :
    DecisiveAll F S₁ ∨ DecisiveAll F S₂ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := h3
  have h3' : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z := ⟨a, b, c, hab, hac, hbc⟩
  set f₁ : A → ℕ := fun z => if z = a then 0 else if z = b then 1 else if z = c then 2 else 3
    with hf₁
  set f₂ : A → ℕ := fun z => if z = b then 0 else if z = c then 1 else if z = a then 2 else 3
    with hf₂
  set f₃ : A → ℕ := fun z => if z = c then 0 else if z = a then 1 else if z = b then 2 else 3
    with hf₃
  set P : V → Ranking A :=
    fun i => if i ∈ S₁ then mkRank f₁ else if i ∈ S₂ then mkRank f₂ else mkRank f₃ with hP
  have h1a : f₁ a = 0 := by simp [hf₁]
  have h1b : f₁ b = 1 := by simp [hf₁, Ne.symm hab]
  have h1c : f₁ c = 2 := by simp [hf₁, Ne.symm hac, Ne.symm hbc]
  have h2b : f₂ b = 0 := by simp [hf₂]
  have h2c : f₂ c = 1 := by simp [hf₂, Ne.symm hbc]
  have h2a : f₂ a = 2 := by simp [hf₂, hab, hac]
  have h3c : f₃ c = 0 := by simp [hf₃]
  have h3a : f₃ a = 1 := by simp [hf₃, hac]
  have h3b : f₃ b = 2 := by simp [hf₃, hbc, Ne.symm hab]
  have hP₁ : ∀ i ∈ S₁, P i = mkRank f₁ := by intro i hi; simp [hP, hi]
  have hP₂ : ∀ i, i ∉ S₁ → i ∈ S₂ → P i = mkRank f₂ := by intro i hi hi2; simp [hP, hi, hi2]
  have hP₃ : ∀ i, i ∉ S₁ → i ∉ S₂ → P i = mkRank f₃ := by intro i hi hi2; simp [hP, hi, hi2]
  -- the whole coalition prefers `b` to `c`
  have hbc' : (F P).rel b c := by
    refine h b c hbc P ?_
    intro i hi
    by_cases h₁ : i ∈ S₁
    · rw [hP₁ i h₁]; exact mkRank_of_lt (by rw [h1b, h1c]; norm_num)
    · have h₂ : i ∈ S₂ := by
        rcases Finset.mem_union.1 hi with h' | h'
        · exact absurd h' h₁
        · exact h'
      rw [hP₂ i h₁ h₂]; exact mkRank_of_lt (by rw [h2b, h2c]; norm_num)
  by_cases hcase : (F P).rel a c
  · -- then `S₁` is semi-decisive for `(a, c)`
    left
    refine decisiveAll_of_semiDecisive hPar hIIA h3' hac ⟨P, ?_, ?_, hcase⟩
    · intro i hi; rw [hP₁ i hi]; exact mkRank_of_lt (by rw [h1a, h1c]; norm_num)
    · intro i hi
      by_cases h₂ : i ∈ S₂
      · rw [hP₂ i hi h₂]; exact mkRank_of_lt (by rw [h2c, h2a]; norm_num)
      · rw [hP₃ i hi h₂]; exact mkRank_of_lt (by rw [h3c, h3a]; norm_num)
  · -- otherwise `S₂` is semi-decisive for `(b, a)`
    right
    have hca : (F P).rel c a := ((F P).rel_total hac).resolve_left hcase
    have hba : (F P).rel b a := (F P).rel_trans hbc' hca
    refine decisiveAll_of_semiDecisive hPar hIIA h3' (Ne.symm hab) ⟨P, ?_, ?_, hba⟩
    · intro i hi
      have h₁ : i ∉ S₁ := fun hc => (Finset.disjoint_left.1 hdisj hc) hi
      rw [hP₂ i h₁ hi]; exact mkRank_of_lt (by rw [h2b, h2a]; norm_num)
    · intro i hi
      by_cases h₁ : i ∈ S₁
      · rw [hP₁ i h₁]; exact mkRank_of_lt (by rw [h1a, h1b]; norm_num)
      · rw [hP₃ i h₁ hi]; exact mkRank_of_lt (by rw [h3a, h3b]; norm_num)

/-- A nonempty decisive coalition contains a decisive singleton. -/
