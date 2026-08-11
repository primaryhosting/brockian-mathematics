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
def twoSubgroup (A : Type*) [AddCommGroup A] : AddSubgroup A :=
  (zsmulAddGroupHom (2 : ℤ) : A →+ A).range

lemma mem_twoSubgroup_iff {A : Type*} [AddCommGroup A] {P : A} :
    P ∈ twoSubgroup A ↔ ∃ x : A, x + x = P := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [zsmulAddGroupHom, two_zsmul] using hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by simpa [zsmulAddGroupHom, two_zsmul] using hx⟩

/-- **Descent theorem** (the group-theoretic heart of the Mordell–Weil theorem).

If an abelian group `A` carries a real-valued *height* function `ht` such that

* every set of bounded height is finite,
* translation by a fixed element at most doubles the height, up to a constant,
* duplication at least quadruples the height, up to a constant,

and if the quotient `A / 2A` is finite (*weak Mordell–Weil*), then `A` is finitely generated. -/
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
theorem int_fg_via_descent : AddGroup.FG ℤ := by
  refine descent_of_height (fun n : ℤ => ((n : ℝ)) ^ 2) ?_ ?_ ?_ ?_
  · intro C
    refine Set.Finite.subset (Set.finite_Icc (-(⌈|C|⌉)) ⌈|C|⌉) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have h1 : ((n : ℝ)) ^ 2 ≤ (⌈|C|⌉ : ℝ) := le_trans (le_trans hn (le_abs_self C)) (Int.le_ceil _)
    have h2 : n ^ 2 ≤ ⌈|C|⌉ := by exact_mod_cast h1
    have h3 : |n| ≤ n ^ 2 := by
      rcases eq_or_ne n 0 with h | h
      · simp [h]
      · have : 1 ≤ |n| := Int.one_le_abs (by omega)
        nlinarith [sq_abs n, abs_nonneg n]
    have h4 := abs_le.mp (le_trans h3 h2)
    simp only [Set.mem_Icc]
    omega
  · intro Q
    refine ⟨2 * (Q : ℝ) ^ 2, fun P => ?_⟩
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) - (Q : ℝ)), sq_nonneg ((P : ℝ) + (Q : ℝ))]
  · refine ⟨0, fun P => ?_⟩
    push_cast
    ring_nf
    nlinarith [sq_nonneg ((P : ℝ))]
  · have heq : twoSubgroup ℤ = AddSubgroup.zmultiples ((2 : ℕ) : ℤ) := by
      ext x
      simp only [mem_twoSubgroup_iff, AddSubgroup.mem_zmultiples_iff, smul_eq_mul]
      constructor
      · rintro ⟨y, rfl⟩; exact ⟨y, by push_cast; ring⟩
      · rintro ⟨k, rfl⟩; exact ⟨k, by push_cast; ring⟩
    rw [heq]
    exact Finite.of_equiv (ZMod 2) (Int.quotientZMultiplesNatEquivZMod 2).symm.toEquiv

/-- **Mordell's theorem** (finite generation of the Mordell–Weil group), as a Lean-checked
reduction to its two standard inputs:

* `weakMordellWeil` : for every elliptic curve over `ℚ`, the quotient `E(ℚ)/2E(ℚ)` is finite;
* `heightTheory` : every such curve carries a height function on its rational points with the
  three standard properties (finiteness of bounded-height sets, quasi-doubling under
  translation, quasi-quadrupling under duplication).

Given these, the group `E(ℚ)` of rational points of any elliptic curve over `ℚ` is finitely
generated. -/
theorem Mordell_finite_generation
    (weakMordellWeil : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
      Finite (W.toAffine.Point ⧸ twoSubgroup W.toAffine.Point))
    (heightTheory : ∀ (W : WeierstrassCurve ℚ), W.IsElliptic →
      ∃ ht : W.toAffine.Point → ℝ,
        (∀ C : ℝ, {P : W.toAffine.Point | ht P ≤ C}.Finite) ∧
        (∀ Q : W.toAffine.Point, ∃ C : ℝ, ∀ P, ht (P + Q) ≤ 2 * ht P + C) ∧
        (∃ C : ℝ, ∀ P : W.toAffine.Point, 4 * ht P ≤ ht (P + P) + C))
    (W : WeierstrassCurve ℚ) (hW : W.IsElliptic) :
    AddGroup.FG W.toAffine.Point := by
  obtain ⟨ht, hfin, hadd, hdouble⟩ := heightTheory W hW
  exact descent_of_height ht hfin hadd hdouble (weakMordellWeil W hW)

end Frontier

