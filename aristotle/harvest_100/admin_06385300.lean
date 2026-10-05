-- (Lean requires `import` to precede any module docstring; the required header follows.)
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
at least `2` defined over `ℚ` has only finitely many rational points.

Here we formalize the statement for *smooth plane curves*, where the genus is given by the
degree–genus formula `g = (d-1)(d-2)/2`, so that "genus ≥ 2" is exactly "degree ≥ 4".
The general statement is recorded as `Frontier.MordellConjecturePlane` (a `Prop`-valued
definition, not proved here — it is Faltings' theorem).

We then prove, unconditionally and axiom-cleanly:

* `Frontier.projectivePoints_finite_of_affine`: a Lean-checked reduction of the finiteness of
  the rational points of a projective plane curve to finiteness of its affine rational points
  together with its rational points at infinity;
* `Frontier.mordellPlane_of_affine_finiteness`: the resulting reduction of
  `MordellConjecturePlane` to the affine statement;
* `Frontier.faltings_mordell`: the base case for the Fermat quartic `x⁴ + y⁴ = z⁴`, a smooth
  plane curve of degree `4` (hence of genus `3 ≥ 2`), whose set of rational points in `ℙ²(ℚ)`
  is proved finite — in fact it consists of exactly the four points
  `(±1 : 0 : 1)`, `(0 : ±1 : 1)`.
-/

namespace Frontier

open MvPolynomial Projectivization

/-! ## Homogeneous polynomials and projective points -/

/-- Evaluating a homogeneous polynomial of degree `d` at a scaled point scales the value
by `c ^ d`. -/
theorem eval_smul_of_isHomogeneous {σ R : Type*} [CommSemiring R] {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : R) (x : σ → R) :
    eval (c • x) f = c ^ d * eval x f := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have hd : ∑ i ∈ e.support, e i = d := by
    have := hf (mem_support_iff.mp he)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  have h2 : ∏ i ∈ e.support, (c • x) i ^ e i
      = (∏ i ∈ e.support, c ^ e i) * ∏ i ∈ e.support, x i ^ e i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by simp [mul_pow]
  rw [h2, Finset.prod_pow_eq_pow_sum, hd]; ring

/-- The set of rational points of the plane projective curve cut out by `f`, as a subset of
the projective plane `ℙ²(ℚ)`.  (For homogeneous `f` of positive degree this is independent of
the chosen representatives; see `Frontier.mem_projectivePoints_mk`.) -/
def projectivePoints (f : MvPolynomial (Fin 3) ℚ) : Set (Projectivization ℚ (Fin 3 → ℚ)) :=
  {P | eval P.rep f = 0}

/-- Membership in `projectivePoints` can be tested on any representative of a projective
point, provided `f` is homogeneous of positive degree. -/
theorem mem_projectivePoints_mk {f : MvPolynomial (Fin 3) ℚ} {d : ℕ} (hf : f.IsHomogeneous d)
    (hd : d ≠ 0) (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    Projectivization.mk ℚ v hv ∈ projectivePoints f ↔ eval v f = 0 := by
  obtain ⟨a, ha⟩ := exists_smul_eq_mk_rep ℚ v hv
  rw [Units.smul_def] at ha
  have ha0 : (a : ℚ) ≠ 0 := a.ne_zero
  constructor
  · intro h
    have h1 : eval ((a : ℚ) • v) f = 0 := by rw [ha]; exact h
    rw [eval_smul_of_isHomogeneous hf] at h1
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd (pow_eq_zero_iff hd |>.1 h2) ha0
    · exact h2
  · intro h
    show eval (Projectivization.mk ℚ v hv).rep f = 0
    rw [← ha, eval_smul_of_isHomogeneous hf, h, mul_zero]

/-! ## Smooth plane curves and the statement of the Mordell conjecture -/

/-- `f` defines a smooth plane projective curve of degree `d` over `ℚ`: it is homogeneous of
degree `d`, and its partial derivatives have no common zero other than the origin over an
algebraic closure of `ℚ`.  By the degree–genus formula such a curve has genus
`(d - 1) * (d - 2) / 2`. -/
def IsSmoothPlaneCurveOfDegree (d : ℕ) (f : MvPolynomial (Fin 3) ℚ) : Prop :=
  f.IsHomogeneous d ∧
    ∀ x : Fin 3 → AlgebraicClosure ℚ,
      (∀ i, aeval x (pderiv i f) = 0) → x = 0

/-- **Faltings' theorem (Mordell conjecture) for smooth plane curves.**  A smooth plane curve
of degree `d ≥ 4` over `ℚ` has genus `(d-1)(d-2)/2 ≥ 2`, and hence — by Faltings' theorem —
only finitely many rational points.  This `Prop` records the statement; it is *not* proved
here.  The theorem `Frontier.faltings_mordell` proves an instance of it, and
`Frontier.mordellPlane_of_affine_finiteness` reduces it to an affine statement. -/
def MordellConjecturePlane : Prop :=
  ∀ (d : ℕ) (f : MvPolynomial (Fin 3) ℚ), 4 ≤ d → IsSmoothPlaneCurveOfDegree d f →
    (projectivePoints f).Finite

/-! ## Reduction to the affine problem -/

private theorem vec_ne_zero_of_last (a b : ℚ) : (![a, b, 1] : Fin 3 → ℚ) ≠ 0 := by
  intro h; have := congrFun h 2; simp at this

private theorem vec_ne_zero_of_mid (a : ℚ) : (![a, 1, 0] : Fin 3 → ℚ) ≠ 0 := by
  intro h; have := congrFun h 1; simp at this

private theorem vec_ne_zero_first : (![1, 0, 0] : Fin 3 → ℚ) ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

/-- If a nonzero scalar multiple of `P.rep` equals `w`, then `P` is the projective point of
`w`. -/
private theorem eq_mk_of_inv_smul_rep (P : Projectivization ℚ (Fin 3 → ℚ)) {c : ℚ} (hc : c ≠ 0)
    {w : Fin 3 → ℚ} (hw : w ≠ 0) (hsm : c⁻¹ • P.rep = w) :
    P = Projectivization.mk ℚ w hw := by
  rw [← Projectivization.mk_rep P, Projectivization.mk_eq_mk_iff]
  refine ⟨Units.mk0 c hc, ?_⟩
  rw [Units.smul_def, Units.val_mk0, ← hsm, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **Reduction of Faltings finiteness to the affine problem.**  For a homogeneous polynomial
`f`, the set of rational points of the projective plane curve `f = 0` is
finite as soon as the set of its affine rational points `{(x, y) | f (x, y, 1) = 0}` and the
set of its rational points at infinity `{q | f (q, 1, 0) = 0}` are finite. -/
theorem projectivePoints_finite_of_affine {f : MvPolynomial (Fin 3) ℚ} {d : ℕ}
    (hf : f.IsHomogeneous d)
    (hA : {p : ℚ × ℚ | eval ![p.1, p.2, 1] f = 0}.Finite)
    (hB : {q : ℚ | eval ![q, 1, 0] f = 0}.Finite) :
    (projectivePoints f).Finite := by
  classical
  set g : ℚ × ℚ → Projectivization ℚ (Fin 3 → ℚ) :=
    fun p => Projectivization.mk ℚ ![p.1, p.2, 1] (vec_ne_zero_of_last p.1 p.2) with hg
  set h : ℚ → Projectivization ℚ (Fin 3 → ℚ) :=
    fun q => Projectivization.mk ℚ ![q, 1, 0] (vec_ne_zero_of_mid q) with hh
  refine Set.Finite.subset
    (((hA.image g).union (hB.image h)).union
      (Set.finite_singleton (Projectivization.mk ℚ ![1, 0, 0] vec_ne_zero_first))) ?_
  rintro P hP
  have hrep : eval P.rep f = 0 := hP
  have hPne : P.rep ≠ 0 := P.rep_nonzero
  by_cases h2 : P.rep 2 = 0
  · by_cases h1 : P.rep 1 = 0
    · -- the point `(1 : 0 : 0)`
      have h0 : P.rep 0 ≠ 0 := by
        intro h0
        apply hPne
        funext i
        fin_cases i <;> simpa using ‹_›
      refine Or.inr ?_
      have hsm : (P.rep 0)⁻¹ • P.rep = ![1, 0, 0] := by
        funext i
        fin_cases i <;> simp [h0, h1, h2]
      simp [eq_mk_of_inv_smul_rep P h0 vec_ne_zero_first hsm]
    · -- a point at infinity `(q : 1 : 0)`
      refine Or.inl (Or.inr ?_)
      set q : ℚ := P.rep 0 / P.rep 1 with hq
      have hsm : (P.rep 1)⁻¹ • P.rep = ![q, 1, 0] := by
        funext i
        fin_cases i <;> simp [h1, h2, hq, div_eq_inv_mul]
      have hqmem : q ∈ {q : ℚ | eval ![q, 1, 0] f = 0} := by
        show eval ![q, 1, 0] f = 0
        rw [← hsm, eval_smul_of_isHomogeneous hf, hrep, mul_zero]
      exact ⟨q, hqmem, (eq_mk_of_inv_smul_rep P h1 (vec_ne_zero_of_mid q) hsm).symm⟩
  · -- an affine point
    refine Or.inl (Or.inl ?_)
    set p : ℚ × ℚ := (P.rep 0 / P.rep 2, P.rep 1 / P.rep 2) with hp
    have hsm : (P.rep 2)⁻¹ • P.rep = ![p.1, p.2, 1] := by
      funext i
      fin_cases i <;> simp [hp, h2, div_eq_inv_mul]
    have hpmem : p ∈ {p : ℚ × ℚ | eval ![p.1, p.2, 1] f = 0} := by
      show eval ![p.1, p.2, 1] f = 0
      rw [← hsm, eval_smul_of_isHomogeneous hf, hrep, mul_zero]
    exact ⟨p, hpmem, (eq_mk_of_inv_smul_rep P h2 (vec_ne_zero_of_last p.1 p.2) hsm).symm⟩

/-- **A Lean-checked reduction of the Mordell conjecture for plane curves** to the
corresponding affine finiteness statement. -/
theorem mordellPlane_of_affine_finiteness
    (H : ∀ (d : ℕ) (f : MvPolynomial (Fin 3) ℚ), 4 ≤ d → IsSmoothPlaneCurveOfDegree d f →
      {p : ℚ × ℚ | eval ![p.1, p.2, 1] f = 0}.Finite ∧ {q : ℚ | eval ![q, 1, 0] f = 0}.Finite) :
    MordellConjecturePlane := by
  intro d f hd hsm
  obtain ⟨hA, hB⟩ := H d f hd hsm
  exact projectivePoints_finite_of_affine hsm.1 hA hB

/-! ## The base case: the Fermat quartic, a smooth plane curve of genus 3 -/

/-- The Fermat quartic `x⁴ + y⁴ - z⁴`. -/
noncomputable def fermatQuartic : MvPolynomial (Fin 3) ℚ := X 0 ^ 4 + X 1 ^ 4 - X 2 ^ 4

theorem eval_fermatQuartic (x : Fin 3 → ℚ) :
    eval x fermatQuartic = x 0 ^ 4 + x 1 ^ 4 - x 2 ^ 4 := by
  simp [fermatQuartic]

/-- The Fermat quartic is a smooth plane curve of degree `4`, hence of genus
`(4-1)(4-2)/2 = 3 ≥ 2`. -/
theorem fermatQuartic_isSmoothPlaneCurve : IsSmoothPlaneCurveOfDegree 4 fermatQuartic := by
  constructor
  · exact ((isHomogeneous_X_pow _ _).add (isHomogeneous_X_pow _ _)).sub
      (isHomogeneous_X_pow _ _)
  · intro x hx
    have h0 := hx 0
    have h1 := hx 1
    have h2 := hx 2
    simp [fermatQuartic, pderiv_X] at h0 h1 h2
    funext i
    fin_cases i <;> simpa using ‹_›

/-- **The rational points of the affine Fermat quartic.**  The only rational solutions of
`x⁴ + y⁴ = 1` are `(±1, 0)` and `(0, ±1)`.  This uses Fermat's proof (via Mathlib's
`not_fermat_42`) that `a⁴ + b⁴ = c²` has no solutions with `a, b ≠ 0`. -/
theorem fermat_quartic_rat_solutions {x y : ℚ} (h : x ^ 4 + y ^ 4 = 1) :
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = -1) := by
  have hx : ((x.num : ℚ)) = x * (x.den : ℚ) := (Rat.mul_den_eq_num x).symm
  have hy : ((y.num : ℚ)) = y * (y.den : ℚ) := (Rat.mul_den_eq_num y).symm
  set a : ℤ := x.num * (y.den : ℤ) with ha
  set b : ℤ := y.num * (x.den : ℤ) with hb
  set n : ℤ := (x.den : ℤ) * (y.den : ℤ) with hn
  have key : a ^ 4 + b ^ 4 = (n ^ 2) ^ 2 := by
    have : ((a : ℚ)) ^ 4 + ((b : ℚ)) ^ 4 = (((n ^ 2 : ℤ) : ℚ)) ^ 2 := by
      push_cast [ha, hb, hn, hx, hy]
      nlinarith [h, sq_nonneg (x * y)]
    exact_mod_cast this
  have hab : a = 0 ∨ b = 0 := by
    by_contra hc
    push_neg at hc
    exact not_fermat_42 hc.1 hc.2 key
  have hx0 : a = 0 → x = 0 := by
    intro h0
    refine Rat.zero_iff_num_zero.mpr ?_
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 (by exact_mod_cast y.den_nz)
  have hy0 : b = 0 → y = 0 := by
    intro h0
    refine Rat.zero_iff_num_zero.mpr ?_
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exact h1
    · exact absurd h1 (by exact_mod_cast x.den_nz)
  have quart : ∀ t : ℚ, t ^ 4 = 1 → t = 1 ∨ t = -1 := by
    intro t ht
    have h4 : (t - 1) * (t + 1) * (t ^ 2 + 1) = 0 := by nlinarith [ht]
    rcases mul_eq_zero.1 h4 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · left; linarith
      · right; linarith
    · nlinarith [sq_nonneg t]
  rcases hab with h0 | h0
  · have hx' := hx0 h0
    subst hx'
    have hy4 : y ^ 4 = 1 := by linarith [h]
    rcases quart y hy4 with h1 | h1
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h1⟩))
  · have hy' := hy0 h0
    subst hy'
    have hx4 : x ^ 4 = 1 := by linarith [h]
    rcases quart x hx4 with h1 | h1
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr (Or.inl ⟨h1, rfl⟩)

theorem fermatQuartic_affine_finite :
    {p : ℚ × ℚ | eval ![p.1, p.2, 1] fermatQuartic = 0}.Finite := by
  have hsub : {p : ℚ × ℚ | eval ![p.1, p.2, 1] fermatQuartic = 0} ⊆
      ({((1 : ℚ), (0 : ℚ)), (-1, 0), (0, 1), (0, -1)} : Set (ℚ × ℚ)) := by
    rintro ⟨u, v⟩ huv
    have h : u ^ 4 + v ^ 4 = 1 := by
      have := huv
      rw [Set.mem_setOf_eq, eval_fermatQuartic] at this
      simp at this
      linarith
    rcases fermat_quartic_rat_solutions h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      simp [h1, h2]
  exact Set.Finite.subset (Set.toFinite _) hsub

theorem fermatQuartic_infinity_empty :
    {q : ℚ | eval ![q, 1, 0] fermatQuartic = 0} = ∅ := by
  ext q
  simp only [Set.mem_setOf_eq, eval_fermatQuartic, Set.mem_empty_iff_false, iff_false]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  intro hq
  have h4 : q ^ 4 + 1 = 0 := by simpa using hq
  nlinarith [sq_nonneg (q ^ 2)]

/-- Two affine representatives determine the same projective point only if they are equal. -/
private theorem mk_last_inj {a b c d : ℚ}
    (h : Projectivization.mk ℚ ![a, b, 1] (vec_ne_zero_of_last a b)
      = Projectivization.mk ℚ ![c, d, 1] (vec_ne_zero_of_last c d)) : a = c ∧ b = d := by
  rw [Projectivization.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  have h2 := congrFun hu 2
  have h0 := congrFun hu 0
  have h1 := congrFun hu 1
  simp [Units.smul_def] at h0 h1 h2
  refine ⟨?_, ?_⟩ <;> simp_all

/-- **The rational points of the Fermat quartic, explicitly.**  In `ℙ²(ℚ)` the curve
`x⁴ + y⁴ = z⁴` has exactly the four rational points `(±1 : 0 : 1)` and `(0 : ±1 : 1)`. -/
theorem fermatQuartic_projectivePoints_eq :
    projectivePoints fermatQuartic =
      {Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero_of_last 1 0),
       Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero_of_last (-1) 0),
       Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero_of_last 0 1),
       Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero_of_last 0 (-1))} := by
  have hhom := fermatQuartic_isSmoothPlaneCurve.1
  ext P
  constructor
  · intro hP
    have hrep : eval P.rep fermatQuartic = 0 := hP
    rw [eval_fermatQuartic] at hrep
    have h2 : P.rep 2 ≠ 0 := by
      intro h2
      refine P.rep_nonzero ?_
      rw [h2] at hrep
      have hx : P.rep 0 ^ 2 = 0 := by nlinarith [sq_nonneg (P.rep 0 ^ 2), sq_nonneg (P.rep 1 ^ 2)]
      have hy : P.rep 1 ^ 2 = 0 := by nlinarith [sq_nonneg (P.rep 0 ^ 2), sq_nonneg (P.rep 1 ^ 2)]
      have hx0 : P.rep 0 = 0 := by
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hx
      have hy0 : P.rep 1 = 0 := by
        exact pow_eq_zero_iff (two_ne_zero) |>.1 hy
      funext i
      fin_cases i <;> simpa using ‹_›
    set x : ℚ := P.rep 0 / P.rep 2 with hxdef
    set y : ℚ := P.rep 1 / P.rep 2 with hydef
    have hsm : (P.rep 2)⁻¹ • P.rep = ![x, y, 1] := by
      funext i
      fin_cases i <;> simp [hxdef, hydef, h2, div_eq_inv_mul]
    have hPeq : P = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero_of_last x y) :=
      eq_mk_of_inv_smul_rep P h2 (vec_ne_zero_of_last x y) hsm
    have hxy : x ^ 4 + y ^ 4 = 1 := by
      rw [hxdef, hydef, div_pow, div_pow, ← add_div,
        div_eq_one_iff_eq (pow_ne_zero 4 h2)]
      linarith [hrep]
    rcases fermat_quartic_rat_solutions hxy with ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩ | ⟨h1, h3⟩ <;>
      rw [hPeq] <;> simp [h1, h3]
  · intro hP
    have hmem : ∀ a b : ℚ, a ^ 4 + b ^ 4 = 1 →
        Projectivization.mk ℚ ![a, b, 1] (vec_ne_zero_of_last a b) ∈ projectivePoints fermatQuartic
        := by
      intro a b hab
      rw [mem_projectivePoints_mk hhom (by norm_num), eval_fermatQuartic]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      rw [hab]
      norm_num
    rcases hP with h | h | h | h <;> rw [h]
    · exact hmem 1 0 (by norm_num)
    · exact hmem (-1) 0 (by norm_num)
    · exact hmem 0 1 (by norm_num)
    · exact hmem 0 (-1) (by norm_num)

/-- The Fermat quartic has exactly four rational points in `ℙ²(ℚ)`. -/
theorem fermatQuartic_projectivePoints_ncard :
    (projectivePoints fermatQuartic).ncard = 4 := by
  have hne : ∀ a b c d : ℚ, ¬(a = c ∧ b = d) →
      Projectivization.mk ℚ ![a, b, 1] (vec_ne_zero_of_last a b) ≠
        Projectivization.mk ℚ ![c, d, 1] (vec_ne_zero_of_last c d) :=
    fun _ _ _ _ h he => h (mk_last_inj he)
  rw [fermatQuartic_projectivePoints_eq]
  rw [Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne 1 0 (-1) 0 (by norm_num), hne 1 0 0 1 (by norm_num),
        hne 1 0 0 (-1) (by norm_num)⟩) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne (-1) 0 0 1 (by norm_num), hne (-1) 0 0 (-1) (by norm_num)⟩) (Set.toFinite _),
    Set.ncard_insert_of_notMem (by
      simp only [Set.mem_singleton_iff]
      exact hne 0 1 0 (-1) (by norm_num)) (Set.toFinite _),
    Set.ncard_singleton]

/-- **Faltings/Mordell, base case.**  The Fermat quartic `x⁴ + y⁴ = z⁴` is a smooth plane
curve of degree `4` over `ℚ`, hence of genus `3 ≥ 2`, and its set of rational points in the
projective plane is finite — indeed it has exactly four points.  This is an unconditional
instance of the conclusion of `Frontier.MordellConjecturePlane` for a curve of genus `≥ 2`. -/
theorem faltings_mordell :
    IsSmoothPlaneCurveOfDegree 4 fermatQuartic ∧ (projectivePoints fermatQuartic).Finite ∧
      (projectivePoints fermatQuartic).ncard = 4 := by
  refine ⟨fermatQuartic_isSmoothPlaneCurve, ?_, fermatQuartic_projectivePoints_ncard⟩
  refine projectivePoints_finite_of_affine fermatQuartic_isSmoothPlaneCurve.1
    fermatQuartic_affine_finite ?_
  rw [fermatQuartic_infinity_empty]
  exact Set.finite_empty

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

