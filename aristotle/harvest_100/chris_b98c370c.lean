/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Descent theorem** (the group-theoretic engine of the Mordell–Weil theorem).

Let `A` be an abelian group equipped with a "height" function `h : A → ℝ` such that

* every set of bounded height is finite (`hfin`);
* the height is (up to a bounded error depending on `Q`) at most doubled by translation by a
  fixed element `Q` (`htrans`);
* the height is (up to a bounded error) at least quadrupled by duplication (`hdup`);
* `A / 2A` is finite, expressed concretely: there is a finite set `R` of coset representatives
  such that every `P : A` can be written as `P = Q + 2 • P₁` with `Q ∈ R` (`hweak`).

Then `A` is a finitely generated group. -/
theorem descent_fg_of_height {A : Type*} [AddCommGroup A]
    (h : A → ℝ)
    (hfin : ∀ C : ℝ, {P : A | h P ≤ C}.Finite)
    (hdup : ∃ C : ℝ, ∀ P : A, 4 * h P - C ≤ h (2 • P))
    (htrans : ∀ Q : A, ∃ C : ℝ, ∀ P : A, h (P - Q) ≤ 2 * h P + C)
    (hweak : ∃ R : Finset A, ∀ P : A, ∃ Q ∈ R, ∃ P₁ : A, P = Q + 2 • P₁) :
    AddGroup.FG A := by
  obtain ⟨C₂, hC₂⟩ := hdup
  obtain ⟨R, hR⟩ := hweak
  choose g hg using htrans
  -- a single constant `C₁` that works for all the (finitely many) representatives
  set C₁ : ℝ := ∑ Q ∈ R, |g Q| with hC₁def
  have hgC₁ : ∀ Q ∈ R, g Q ≤ C₁ := by
    intro Q hQ
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun Q => |g Q|) (fun i _ => abs_nonneg _) hQ
  -- the height threshold below which we take all points as generators
  set B : ℝ := max 0 ((C₁ + C₂) / 2) with hBdef
  set S : Set A := (R : Set A) ∪ {P : A | h P ≤ B} with hSdef
  have hSfin : S.Finite := R.finite_toSet.union (hfin B)
  have hRS : ∀ Q ∈ R, Q ∈ AddSubgroup.closure S := fun Q hQ =>
    AddSubgroup.subset_closure (Or.inl hQ)
  have hsmall : ∀ P : A, h P ≤ B → P ∈ AddSubgroup.closure S := fun P hP =>
    AddSubgroup.subset_closure (Or.inr hP)
  -- the main claim: the closure of `S` is everything
  have hall : ∀ P : A, P ∈ AddSubgroup.closure S := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨P₀, hP₀⟩ := hcon
    set T : Set A := {P : A | h P ≤ h P₀ ∧ P ∉ AddSubgroup.closure S} with hTdef
    have hTfin : T.Finite := (hfin (h P₀)).subset (fun x hx => hx.1)
    have hTne : T.Nonempty := ⟨P₀, le_refl _, hP₀⟩
    obtain ⟨P, hPT, hPmin⟩ := hTfin.exists_minimalFor h T hTne
    have hPB : B < h P := by
      by_contra hle
      exact hPT.2 (hsmall P (not_lt.mp hle))
    obtain ⟨Q, hQR, P₁, hP₁⟩ := hR P
    have hsub : P - Q = 2 • P₁ := by
      rw [hP₁]; abel
    have h1 : h (2 • P₁) ≤ 2 * h P + C₁ := by
      have := hg Q P
      rw [hsub] at this
      linarith [hgC₁ Q hQR]
    have h2 : 4 * h P₁ - C₂ ≤ h (2 • P₁) := hC₂ P₁
    have hBge : (C₁ + C₂) / 2 ≤ B := le_max_right _ _
    have hlt : h P₁ < h P := by linarith
    have hP₁not : P₁ ∉ AddSubgroup.closure S := by
      intro hmem
      apply hPT.2
      rw [hP₁]
      exact AddSubgroup.add_mem _ (hRS Q hQR)
        (AddSubgroup.nsmul_mem _ hmem 2)
    have hP₁T : P₁ ∈ T := ⟨le_trans hlt.le hPT.1, hP₁not⟩
    exact absurd (hPmin hP₁T hlt.le) (not_le.mpr hlt)
  rw [AddGroup.fg_iff]
  exact ⟨S, eq_top_iff.mpr fun P _ => hall P, hSfin⟩

/-- A sanity check that the hypotheses of `Frontier.descent_fg_of_height` are consistent (and
hence that the reduction below is not vacuous): the group `ℤ`, with height `n ↦ n ^ 2`,
satisfies all of them, and is indeed finitely generated. -/
example : AddGroup.FG ℤ := by
  refine descent_fg_of_height (A := ℤ) (fun n => (n : ℝ) ^ 2) ?_ ?_ ?_ ?_
  · intro C
    apply Set.Finite.subset (Set.finite_Icc (-(⌈C⌉ + 1)) (⌈C⌉ + 1))
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    have h1 : (|n| : ℝ) ≤ (n : ℝ) ^ 2 + 1 := by
      have hcast : (|n| : ℝ) = |(n : ℝ)| := by push_cast [abs]; rfl
      rw [hcast]
      nlinarith [abs_nonneg ((n : ℝ)), sq_abs ((n : ℝ)), sq_nonneg (|(n : ℝ)| - 1)]
    have h2 : (|n| : ℝ) ≤ (⌈C⌉ : ℝ) + 1 := by
      have := Int.le_ceil C
      linarith
    have h3 : |n| ≤ ⌈C⌉ + 1 := by exact_mod_cast h2
    simp only [Set.mem_Icc]
    constructor <;> [linarith [neg_abs_le n, abs_nonneg n]; linarith [le_abs_self n]]
  · refine ⟨0, fun P => ?_⟩
    have hx : ((2 • P : ℤ) : ℝ) = 2 * (P : ℝ) := by simp
    simp only [hx]
    nlinarith [sq_nonneg ((P : ℝ))]
  · refine fun Q => ⟨2 * (Q : ℝ) ^ 2, fun P => ?_⟩
    push_cast
    nlinarith [sq_nonneg ((P : ℝ) + (Q : ℝ))]
  · refine ⟨{0, 1}, fun P => ?_⟩
    rcases Int.even_or_odd P with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨0, by simp, k, by simp; omega⟩
    · exact ⟨1, by simp, k, by simp; omega⟩

/-- **Mordell's theorem** (finite generation of the group of rational points of an elliptic
curve over `ℚ`), reduced in Lean to its two standard arithmetic inputs.

Given an elliptic curve `E` over `ℚ` together with

* a height function `h` on the group `E(ℚ)` of rational points whose sublevel sets
  are finite (Northcott property), which is quasi-quadratic in the sense that translation by a
  fixed point at most doubles it up to a constant and duplication at least quadruples it up to
  a constant, and
* the weak Mordell–Weil theorem for `E`, i.e. finiteness of `E(ℚ)/2E(ℚ)`, given concretely by
  a finite set of coset representatives,

the group `E(ℚ)` is finitely generated. -/
theorem Mordell_finite_generation
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : E.toAffine.Point → ℝ)
    (hfin : ∀ C : ℝ, {P : E.toAffine.Point | h P ≤ C}.Finite)
    (hdup : ∃ C : ℝ, ∀ P : E.toAffine.Point, 4 * h P - C ≤ h (2 • P))
    (htrans : ∀ Q : E.toAffine.Point, ∃ C : ℝ,
      ∀ P : E.toAffine.Point, h (P - Q) ≤ 2 * h P + C)
    (hweak : ∃ R : Finset E.toAffine.Point,
      ∀ P : E.toAffine.Point, ∃ Q ∈ R, ∃ P₁ : E.toAffine.Point, P = Q + 2 • P₁) :
    AddGroup.FG E.toAffine.Point :=
  descent_fg_of_height h hfin hdup htrans hweak

end Frontier

