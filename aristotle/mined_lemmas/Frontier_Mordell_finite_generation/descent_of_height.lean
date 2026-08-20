/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Classical

namespace Frontier

/-- The subgroup `2A` of an additive commutative group `A`. -/

theorem descent_of_height {A : Type*} [AddCommGroup A] (ht : A → ℝ)
    (hfin : ∀ C : ℝ, {P : A | ht P ≤ C}.Finite)
    (hadd : ∀ Q : A, ∃ C : ℝ, ∀ P : A, ht (P + Q) ≤ 2 * ht P + C)
    (hdouble : ∃ C : ℝ, ∀ P : A, 4 * ht P ≤ ht (P + P) + C)
    (hquot : Finite (A ⧸ twoSubgroup A)) :
    AddGroup.FG A := by
  classical
  haveI := hquot
  -- coset representatives of `A / 2A`
  set r : (A ⧸ twoSubgroup A) → A := fun q => Quotient.out q with hr
  have hrep : ∀ P : A, ∃ P₁ : A, P₁ + P₁ = P + -(r (QuotientAddGroup.mk P)) := by
    intro P
    have h : (QuotientAddGroup.mk (r (QuotientAddGroup.mk P)) : A ⧸ twoSubgroup A) =
        QuotientAddGroup.mk P := Quotient.out_eq _
    rw [QuotientAddGroup.eq, neg_add_eq_sub] at h
    obtain ⟨x, hx⟩ := mem_twoSubgroup_iff.mp h
    exact ⟨x, by rw [hx]; abel⟩
  -- a uniform constant for translation by (minus) a representative
  have hg : ∀ q : A ⧸ twoSubgroup A, ∃ C : ℝ, ∀ P : A, ht (P + -(r q)) ≤ 2 * ht P + C :=
    fun q => hadd (-(r q))
  set g : (A ⧸ twoSubgroup A) → ℝ := fun q => Classical.choose (hg q) with hgdef
  have hgspec : ∀ q : A ⧸ twoSubgroup A, ∀ P : A, ht (P + -(r q)) ≤ 2 * ht P + g q :=
    fun q => Classical.choose_spec (hg q)
  obtain ⟨q₀, hq₀⟩ := Finite.exists_max g
  set C₁ : ℝ := g q₀ with hC₁
  obtain ⟨C₂, hC₂⟩ := hdouble
  set B : ℝ := max ((C₁ + C₂) / 2) 0 with hB
  -- the key inequality: the height of a "half" is essentially halved
  have key : ∀ (P P₁ : A) (q : A ⧸ twoSubgroup A), P₁ + P₁ = P + -(r q) →
      4 * ht P₁ ≤ 2 * ht P + (C₁ + C₂) := by
    intro P P₁ q h2
    have h1 : 4 * ht P₁ ≤ ht (P₁ + P₁) + C₂ := hC₂ P₁
    have h3 : ht (P + -(r q)) ≤ 2 * ht P + g q := hgspec q P
    have h4 : g q ≤ C₁ := hq₀ q
    rw [h2] at h1
    linarith
  -- the generating set
  set S : Set A := Set.range r ∪ {P : A | ht P ≤ B} with hS
  have hSfin : S.Finite := (Set.finite_range r).union (hfin B)
  refine AddGroup.fg_iff.mpr ⟨S, ?_, hSfin⟩
  rw [eq_top_iff]
  rintro P -
  by_contra hP
  -- among the non-generated elements of height at most `ht P`, pick one of minimal height
  set T : Set A := {Q : A | Q ∉ AddSubgroup.closure S ∧ ht Q ≤ ht P} with hT
  have hTfin : T.Finite := (hfin (ht P)).subset (fun x hx => hx.2)
  have hTne : T.Nonempty := ⟨P, hP, le_rfl⟩
  obtain ⟨M, hMT, hMmin⟩ := Set.exists_min_image T ht hTfin hTne
  obtain ⟨hMnot, hMle⟩ := hMT
  have hMB : B < ht M := by
    by_contra hcon
    push_neg at hcon
    exact hMnot (AddSubgroup.subset_closure (Or.inr hcon))
  obtain ⟨M₁, hM₁⟩ := hrep M
  have hkey := key M M₁ (QuotientAddGroup.mk M) hM₁
  have hB1 : (C₁ + C₂) / 2 ≤ B := le_max_left _ _
  have hlt : ht M₁ < ht M := by nlinarith [hMB, hB1]
  have hM₁gen : M₁ ∈ AddSubgroup.closure S := by
    by_contra hcon
    have hmem : M₁ ∈ T := ⟨hcon, le_trans hlt.le hMle⟩
    exact absurd (hMmin M₁ hmem) (not_le.mpr hlt)
  have hrgen : r (QuotientAddGroup.mk M) ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure (Or.inl ⟨_, rfl⟩)
  have hMeq : M₁ + M₁ + r (QuotientAddGroup.mk M) = M := by rw [hM₁]; abel
  exact hMnot
    (hMeq ▸ AddSubgroup.add_mem _ (AddSubgroup.add_mem _ hM₁gen hM₁gen) hrgen)

/-- Sanity check that the hypotheses of `Frontier.descent_of_height` are satisfiable in a
nontrivial situation: `ℤ` with the height `n ↦ n ^ 2` satisfies all of them, and descent then
recovers the finite generation of `ℤ`. -/
