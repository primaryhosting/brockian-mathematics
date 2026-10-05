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

/-! ## The descent machinery

Mordell's theorem states that the group `E(ℚ)` of rational points of an elliptic curve over `ℚ`
is finitely generated.  Its classical proof has two inputs:

* the *weak Mordell–Weil theorem*: the quotient `E(ℚ)/2E(ℚ)` is finite;
* the *theory of heights*: there is a height function `h : E(ℚ) → ℝ` satisfying the three
  standard properties recorded in `Frontier.HeightData` below.

The purely group-theoretic step which combines these two inputs into finite generation is the
*descent theorem*, `Frontier.fg_of_quotient_two_finite_of_heightData`, which is proved here in
full generality for an arbitrary additive commutative group.  The target theorem
`Frontier.Mordell_finite_generation` is the resulting Lean-checked reduction of Mordell's

theorem fg_of_quotient_two_finite_of_heightData {A : Type*} [AddCommGroup A]
    (hquot : Finite (A ⧸ twoSubgroup A)) (hd : HeightData A) : AddGroup.FG A := by
  classical
  obtain ⟨C₂, hC₂⟩ := hd.duplication
  -- A finite set `R` of representatives for the cosets of `2A`.
  set R : Set A := Set.range (fun q : A ⧸ twoSubgroup A => (Quotient.out q : A)) with hRdef
  have hRfin : R.Finite := Set.finite_range _
  have hrep : ∀ P : A, ∃ Q ∈ R, ∃ P' : A, P = Q + (P' + P') := by
    intro P
    refine ⟨(Quotient.out (QuotientAddGroup.mk (s := twoSubgroup A) P) : A), ⟨_, rfl⟩, ?_⟩
    have h1 : (QuotientAddGroup.mk (s := twoSubgroup A)
        (Quotient.out (QuotientAddGroup.mk (s := twoSubgroup A) P)) : A ⧸ twoSubgroup A)
        = QuotientAddGroup.mk (s := twoSubgroup A) P :=
      QuotientAddGroup.out_eq' _
    have h2 : -(Quotient.out (QuotientAddGroup.mk (s := twoSubgroup A) P) : A) + P
        ∈ twoSubgroup A := QuotientAddGroup.eq.mp h1
    obtain ⟨x, hx⟩ := mem_twoSubgroup_iff.mp h2
    exact ⟨x, by rw [← hx]; abel⟩
  -- A uniform constant for the quasi-parallelogram law over the (finite) set `R`.
  choose f hf using fun Q : A => hd.quasi_parallelogram (-Q)
  obtain ⟨C₁, hC₁'⟩ := Finset.exists_le (α := ℝ) ((hRfin.toFinset).image f)
  have hC₁ : ∀ Q ∈ R, f Q ≤ C₁ := by
    intro Q hQ
    exact hC₁' (f Q) (Finset.mem_image_of_mem f (by simpa using hQ))
  set B : ℝ := (C₁ + C₂) / 2 with hBdef
  -- The candidate generating set.
  set S : Set A := R ∪ {P : A | hd.h P ≤ B} with hSdef
  have hSfin : S.Finite := hRfin.union (hd.finite_of_bounded B)
  -- Key descent step.
  have hstep : ∀ P : A, B < hd.h P → ∃ Q ∈ R, ∃ P' : A, P = Q + (P' + P') ∧ hd.h P' < hd.h P := by
    intro P hP
    obtain ⟨Q, hQ, P', hPQ⟩ := hrep P
    refine ⟨Q, hQ, P', hPQ, ?_⟩
    have h1 : hd.h (P' + P') ≤ 2 * hd.h P + f Q := by
      have : P' + P' = P + -Q := by rw [hPQ]; abel
      rw [this]
      exact hf Q P
    have h2 : 4 * hd.h P' ≤ hd.h (P' + P') + C₂ := hC₂ P'
    have h3 : f Q ≤ C₁ := hC₁ Q hQ
    have h4 : C₁ + C₂ < 2 * hd.h P := by
      rw [hBdef] at hP; linarith
    linarith
  rw [AddGroup.fg_iff]
  refine ⟨S, ?_, hSfin⟩
  -- `S` generates `A`.
  by_contra hne
  have hex : ∃ P : A, P ∉ AddSubgroup.closure S := by
    by_contra hall
    push_neg at hall
    exact hne (eq_top_iff.mpr fun P _ => hall P)
  obtain ⟨P₀, hP₀⟩ := hex
  set T : Set A := {P : A | P ∉ AddSubgroup.closure S ∧ hd.h P ≤ hd.h P₀} with hTdef
  have hTfin : T.Finite :=
    (hd.finite_of_bounded (hd.h P₀)).subset (fun P hP => hP.2)
  have hTne : T.Nonempty := ⟨P₀, hP₀, le_refl _⟩
  obtain ⟨P₁, hP₁T, hP₁min⟩ := Set.exists_min_image T hd.h hTfin hTne
  have hP₁closure : P₁ ∉ AddSubgroup.closure S := hP₁T.1
  have hP₁B : B < hd.h P₁ := by
    by_contra hle
    push_neg at hle
    exact hP₁closure (AddSubgroup.subset_closure (Or.inr hle))
  obtain ⟨Q, hQ, P', hP₁eq, hlt⟩ := hstep P₁ hP₁B
  have hP'closure : P' ∉ AddSubgroup.closure S := by
    intro hmem
    refine hP₁closure ?_
    rw [hP₁eq]
    exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure (Or.inl hQ))
      (AddSubgroup.add_mem _ hmem hmem)
  have hP'T : P' ∈ T := ⟨hP'closure, le_trans hlt.le hP₁T.2⟩
  exact absurd (hP₁min P' hP'T) (not_le.mpr hlt)

/-! ## A base case: the descent machinery is non-vacuous

To check that the hypotheses of the descent theorem are satisfiable, we run the argument on the
simplest Mordell–Weil-type group, `ℤ`: the quotient `ℤ/2ℤ` is finite, the square of the absolute
value is a height function in the above sense, and the descent theorem then produces finite
generation of `ℤ`. -/

/-- `ℤ / 2ℤ` is finite. -/
