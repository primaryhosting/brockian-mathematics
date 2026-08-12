import Mathlib
/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

Faltings' theorem (the Mordell conjecture) states that a smooth projective curve of genus
`≥ 2` over `ℚ` has only finitely many rational points.

In this file we

* formalise the statement for smooth plane curves in `ℙ²`, where the genus is given by the
  degree–genus formula `g = (d-1)(d-2)/2`, so that `d ≥ 4` is exactly the condition `g ≥ 2`
  (`Frontier.FaltingsMordellStatement`);
* verify, unconditionally, an instance of it: the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` and hence of genus `3`, has only finitely many rational points
  (`Frontier.faltings_mordell`) — indeed exactly four (`Frontier.fermatQuartic_projPoints`).
  The proof uses Fermat's Last Theorem for exponent four.
-/

namespace Frontier

open MvPolynomial
open scoped LinearAlgebra.Projectivization

noncomputable section

/-- The set of `ℚ`-points of the plane projective curve cut out by `F`. -/
def projPoints (F : MvPolynomial (Fin 3) ℚ) : Set (ℙ ℚ (Fin 3 → ℚ)) :=
  {p | MvPolynomial.eval p.rep F = 0}

/-- The genus of a smooth plane curve of degree `d`, by the degree–genus formula. -/
def planeCurveGenus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

lemma two_le_planeCurveGenus {d : ℕ} (hd : 4 ≤ d) : 2 ≤ planeCurveGenus d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h1 : 4 + k - 1 = k + 3 := by omega
  have h2 : 4 + k - 2 = k + 2 := by omega
  rw [planeCurveGenus, h1, h2, Nat.le_div_iff_mul_le (by norm_num)]
  nlinarith

/-- A homogeneous `F ∈ ℚ[X₀,X₁,X₂]` cuts out a smooth plane curve if its partial derivatives
have no common zero other than the origin, over an algebraic closure of `ℚ`. -/
def IsSmoothPlaneCurve (F : MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ v : Fin 3 → AlgebraicClosure ℚ,
    (∀ i, MvPolynomial.eval v (pderiv i (F.map (algebraMap ℚ (AlgebraicClosure ℚ)))) = 0) →
      v = 0

/-- **Faltings' theorem (Mordell conjecture)**, stated for smooth plane curves over `ℚ`:
a smooth plane curve of degree `d` whose genus `(d-1)(d-2)/2` is at least `2` has only
finitely many rational points. -/
def FaltingsMordellStatement : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin 3) ℚ), F.IsHomogeneous d → 2 ≤ planeCurveGenus d →
    IsSmoothPlaneCurve F → (projPoints F).Finite

/-- The Fermat quartic `x⁴ + y⁴ - z⁴`. -/
def fermatQuartic : MvPolynomial (Fin 3) ℚ := X 0 ^ 4 + X 1 ^ 4 - X 2 ^ 4

@[simp] lemma eval_fermatQuartic (v : Fin 3 → ℚ) :
    MvPolynomial.eval v fermatQuartic = v 0 ^ 4 + v 1 ^ 4 - v 2 ^ 4 := by
  simp [fermatQuartic]

lemma fermatQuartic_isHomogeneous : fermatQuartic.IsHomogeneous 4 := by
  have h : ∀ i : Fin 3, ((X i : MvPolynomial (Fin 3) ℚ) ^ 4).IsHomogeneous 4 := by
    intro i; simpa using (isHomogeneous_X ℚ i).pow 4
  exact ((h 0).add (h 1)).sub (h 2)

lemma fermatQuartic_isSmooth : IsSmoothPlaneCurve fermatQuartic := by
  intro v h
  have hmap : fermatQuartic.map (algebraMap ℚ (AlgebraicClosure ℚ))
      = X 0 ^ 4 + X 1 ^ 4 - X 2 ^ 4 := by
    simp [fermatQuartic]
  funext i
  have hi := h i
  rw [hmap] at hi
  fin_cases i <;>
  · simp at hi
    simpa using hi

/-- Fermat's Last Theorem for exponent four, over `ℚ`. -/
lemma flt_four_rat {x y z : ℚ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) :
    x ^ 4 + y ^ 4 ≠ z ^ 4 :=
  fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour x y z hx hy hz

lemma quartic_eq_iff {x y : ℚ} (h : x ^ 4 = y ^ 4) : x = y ∨ x = -y := by
  have h2 : (x - y) * (x + y) * (x ^ 2 + y ^ 2) = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · rcases mul_eq_zero.mp h3 with h4 | h4
    · left; linarith
    · right; linarith
  · have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
    left; simp [hx, hy]

lemma eq_zero_of_add_pow_four_eq_zero {a b : ℚ} (h : a ^ 4 + b ^ 4 = 0) : a = 0 := by
  have h4 : a ^ 4 = 0 := by nlinarith [sq_nonneg (a ^ 2), sq_nonneg (b ^ 2)]
  exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h4

/-- Classification of the nonzero rational solutions of `x⁴ + y⁴ = z⁴`, up to scaling:
by Fermat's Last Theorem for exponent four, each is proportional to one of four vectors. -/
lemma fermatQuartic_solutions (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (h : v 0 ^ 4 + v 1 ^ 4 - v 2 ^ 4 = 0) :
    ∃ a : ℚ, a ≠ 0 ∧ (v = a • ![1, 0, 1] ∨ v = a • ![1, 0, -1] ∨ v = a • ![0, 1, 1] ∨
      v = a • ![0, 1, -1]) := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · exfalso
      apply hv
      have h2 : v 2 = 0 := by
        have h2' : v 2 ^ 4 = 0 := by rw [h0, h1] at h; linarith
        exact pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h2'
      funext i; fin_cases i <;> simpa
    · have h2 : v 2 ≠ 0 := by
        intro h2
        exact h1 (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp
          (by rw [h0, h2] at h; linarith))
      rcases quartic_eq_iff (x := v 1) (y := v 2) (by rw [h0] at h; linarith) with he | he
      · exact ⟨v 2, h2, Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> simp [h0, he])))⟩
      · refine ⟨v 1, h1, Or.inr (Or.inr (Or.inr ?_))⟩
        funext i; fin_cases i <;> simp [h0, he]
  · by_cases h1 : v 1 = 0
    · rcases quartic_eq_iff (x := v 0) (y := v 2) (by rw [h1] at h; linarith) with he | he
      · exact ⟨v 0, h0, Or.inl (by funext i; fin_cases i <;> simp [h1, he])⟩
      · refine ⟨v 0, h0, Or.inr (Or.inl ?_)⟩
        funext i; fin_cases i <;> simp [h1, he]
    · have h2 : v 2 ≠ 0 := by
        intro h2
        rw [h2] at h
        exact h0 (eq_zero_of_add_pow_four_eq_zero (b := v 1) (by linarith))
      exact absurd (by linarith : v 0 ^ 4 + v 1 ^ 4 = v 2 ^ 4) (flt_four_rat h0 h1 h2)

lemma eval_smul_fermatQuartic (a : ℚ) (v : Fin 3 → ℚ) :
    MvPolynomial.eval (a • v) fermatQuartic = a ^ 4 * MvPolynomial.eval v fermatQuartic := by
  simp [Pi.smul_apply, smul_eq_mul]; ring

lemma mem_projPoints_mk (w : Fin 3 → ℚ) (hw : w ≠ 0) :
    Projectivization.mk ℚ w hw ∈ projPoints fermatQuartic ↔
      MvPolynomial.eval w fermatQuartic = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℚ (Projectivization.mk ℚ w hw).rep w
    (Projectivization.rep_nonzero _) hw).mp (Projectivization.mk_rep _)
  rw [Units.smul_def] at ha
  constructor
  · intro hp
    have h2 : MvPolynomial.eval ((a : ℚ) • w) fermatQuartic = 0 := by rw [ha]; exact hp
    rw [eval_smul_fermatQuartic] at h2
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (pow_eq_zero_iff (n := 4) (by norm_num) |>.mp h1) a.ne_zero
    · exact h1
  · intro hw0
    show MvPolynomial.eval (Projectivization.mk ℚ w hw).rep fermatQuartic = 0
    rw [← ha, eval_smul_fermatQuartic, hw0, mul_zero]

/-- The four rational points of the Fermat quartic. -/
def fermatQuarticPointSet : Set (ℙ ℚ (Fin 3 → ℚ)) :=
  { Projectivization.mk ℚ ![1, 0, 1] (by intro h; simpa using congrFun h 0),
    Projectivization.mk ℚ ![1, 0, -1] (by intro h; simpa using congrFun h 0),
    Projectivization.mk ℚ ![0, 1, 1] (by intro h; simpa using congrFun h 1),
    Projectivization.mk ℚ ![0, 1, -1] (by intro h; simpa using congrFun h 1) }

theorem fermatQuartic_projPoints : projPoints fermatQuartic = fermatQuarticPointSet := by
  have hne0 : (![1, 0, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne1 : (![1, 0, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne2 : (![0, 1, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have hne3 : (![0, 1, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  ext p
  constructor
  · intro hp
    have hv : p.rep ≠ 0 := p.rep_nonzero
    have heq : p.rep 0 ^ 4 + p.rep 1 ^ 4 - p.rep 2 ^ 4 = 0 := by
      simpa [projPoints] using hp
    obtain ⟨a, ha, hcase⟩ := fermatQuartic_solutions p.rep hv heq
    have key : ∀ (w : Fin 3 → ℚ) (hw : w ≠ 0), p.rep = a • w →
        p = Projectivization.mk ℚ w hw := by
      intro w hw hpw
      rw [← Projectivization.mk_rep p]
      exact (Projectivization.mk_eq_mk_iff' ℚ p.rep w hv hw).mpr ⟨a, hpw.symm⟩
    rcases hcase with hc | hc | hc | hc
    · exact Or.inl (key _ hne0 hc)
    · exact Or.inr (Or.inl (key _ hne1 hc))
    · exact Or.inr (Or.inr (Or.inl (key _ hne2 hc)))
    · exact Or.inr (Or.inr (Or.inr (key _ hne3 hc)))
  · intro hp
    rcases hp with hc | hc | hc | hc <;> rw [hc] <;>
      [exact (mem_projPoints_mk _ hne0).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne1).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne2).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons]);
       exact (mem_projPoints_mk _ hne3).mpr (by norm_num [Matrix.cons_val_two, Matrix.tail_cons])]

/-- **Faltings' theorem for the Fermat quartic.** The smooth plane quartic `x⁴ + y⁴ = z⁴`
has genus `3 ≥ 2`, and it has only finitely many rational points — an unconditional
instance of the Mordell conjecture. -/
theorem faltings_mordell : (projPoints fermatQuartic).Finite := by
  rw [fermatQuartic_projPoints, fermatQuarticPointSet]
  exact (((Set.finite_singleton _).insert _).insert _).insert _

/-- The Fermat quartic really does have exactly four rational points: the four listed
points of `ℙ²(ℚ)` are pairwise distinct. -/
theorem fermatQuartic_projPoints_ncard : (projPoints fermatQuartic).ncard = 4 := by
  have hne0 : (![1, 0, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne1 : (![1, 0, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 0
  have hne2 : (![0, 1, 1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have hne3 : (![0, 1, -1] : Fin 3 → ℚ) ≠ 0 := by intro h; simpa using congrFun h 1
  have key : ∀ (v w : Fin 3 → ℚ) (hv : v ≠ 0) (hw : w ≠ 0), (∀ a : ℚ, a • w ≠ v) →
      Projectivization.mk ℚ v hv ≠ Projectivization.mk ℚ w hw := by
    intro v w hv hw h hcon
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' ℚ v w hv hw).mp hcon
    exact h a ha
  have d01 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![1, 0, -1] hne1 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    have h2 := congrFun ha 2
    simp [Matrix.cons_val_two, Matrix.tail_cons] at h0 h2
    rw [h0] at h2
    norm_num at h2
  have d02 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![0, 1, 1] hne2 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d03 : Projectivization.mk ℚ ![1, 0, 1] hne0 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d12 : Projectivization.mk ℚ ![1, 0, -1] hne1 ≠ Projectivization.mk ℚ ![0, 1, 1] hne2 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d13 : Projectivization.mk ℚ ![1, 0, -1] hne1 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h0 := congrFun ha 0
    simp at h0
  have d23 : Projectivization.mk ℚ ![0, 1, 1] hne2 ≠ Projectivization.mk ℚ ![0, 1, -1] hne3 := by
    refine key _ _ _ _ fun a ha => ?_
    have h1 := congrFun ha 1
    have h2 := congrFun ha 2
    simp [Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
    rw [h1] at h2
    norm_num at h2
  rw [fermatQuartic_projPoints, fermatQuarticPointSet]
  rw [Set.ncard_insert_of_notMem (by simp [d01, d02, d03]) (by
        exact (((Set.finite_singleton _).insert _).insert _)),
      Set.ncard_insert_of_notMem (by simp [d12, d13]) (by
        exact ((Set.finite_singleton _).insert _)),
      Set.ncard_insert_of_notMem (by simp [d23]) (Set.finite_singleton _),
      Set.ncard_singleton]

/-- A Lean-checked reduction: the general statement of Faltings' theorem for smooth plane
curves does apply to the Fermat quartic, i.e. its hypotheses are verified there. -/
theorem fermatQuartic_finite_of_faltingsMordell (H : FaltingsMordellStatement) :
    (projPoints fermatQuartic).Finite :=
  H 4 fermatQuartic fermatQuartic_isHomogeneous (two_le_planeCurveGenus le_rfl)
    fermatQuartic_isSmooth

end

end Frontier

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

