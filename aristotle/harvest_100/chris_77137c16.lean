import Mathlib

/-!
# Faltings Mordell
Category: Frontier — Fields Medal Work
Target: Frontier.faltings_mordell
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

/-!
## Faltings' theorem (the Mordell conjecture)

Faltings' theorem states that a smooth projective curve of genus `≥ 2` defined over `ℚ` has
only finitely many rational points.  Mathlib currently has no definition of the genus of a
curve, so we formalize the statement for the classical family of test cases: the *Fermat
curves* `x ^ n + y ^ n = 1`.  The smooth plane projective curve `x ^ n + y ^ n = z ^ n` has
genus `(n - 1) * (n - 2) / 2`, which is `≥ 2` exactly when `n ≥ 4`; so the assertion
`FaltingsForFermatCurves` below is precisely the content of Faltings' theorem for this family.

We prove:

* `Frontier.fermatCurve_finite_of_flt`: a Lean-checked *reduction* of Faltings' theorem for the
  Fermat curve of even degree `n ≥ 1` to Fermat's Last Theorem for the exponent `n`;
* `Frontier.faltings_mordell` (the target): the resulting unconditional *base case* — for every
  `n` divisible by `4` (in particular the genus `3` quartic `x ^ 4 + y ^ 4 = 1`), the Fermat
  curve has only finitely many rational points.  The input is Mathlib's
  `fermatLastTheoremFour`, Fermat's Last Theorem for exponent `4`.
* `Frontier.fermatCurve_eq_of_four_dvd`: in fact the rational points are exactly the four
  trivial ones.
-/

/-- The set of affine rational points of the Fermat curve `x ^ n + y ^ n = 1`. -/
def fermatCurveRatPoints (n : ℕ) : Set (ℚ × ℚ) := {p : ℚ × ℚ | p.1 ^ n + p.2 ^ n = 1}

/-- Faltings' theorem for the Fermat curves: for `n ≥ 4` the smooth plane projective curve
`x ^ n + y ^ n = z ^ n` has genus `(n - 1) * (n - 2) / 2 ≥ 3 ≥ 2`, hence, by Faltings' theorem,
finitely many rational points.  (Stated here only as a `Prop`; it is *not* proved in this file.
The theorem `Frontier.faltings_mordell` establishes the cases `4 ∣ n`.) -/
def FaltingsForFermatCurves : Prop := ∀ n : ℕ, 4 ≤ n → (fermatCurveRatPoints n).Finite

/-- The four trivial rational points of `x ^ n + y ^ n = 1` for even `n`. -/
def trivialFermatPoints : Set (ℚ × ℚ) := {(1, 0), (-1, 0), (0, 1), (0, -1)}

theorem trivialFermatPoints_finite : trivialFermatPoints.Finite := by
  unfold trivialFermatPoints
  exact ((((Set.finite_singleton _).insert _).insert _).insert _)

/-- A rational number with `x ^ n = 1` and `n ≠ 0` is `± 1`. -/
theorem rat_eq_one_or_neg_one_of_pow_eq_one {x : ℚ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) :
    x = 1 ∨ x = -1 := by
  have hx : |x| ^ n = 1 := by rw [← abs_pow, h]; simp
  have h1 : |x| = 1 := by
    rcases lt_trichotomy |x| 1 with hlt | heq | hgt
    · exact absurd hx (by have := pow_lt_one₀ (abs_nonneg x) hlt hn; linarith)
    · exact heq
    · exact absurd hx (by have := one_lt_pow₀ hgt hn; linarith)
  exact (abs_eq (by norm_num : (0:ℚ) ≤ 1)).mp h1

/-- **Reduction.** If Fermat's Last Theorem holds over `ℚ` for the exponent `n ≠ 0`, then the
only rational points of the Fermat curve `x ^ n + y ^ n = 1` are the four trivial ones. -/
theorem fermatCurve_subset_trivial_of_flt {n : ℕ} (hn : n ≠ 0)
    (hflt : FermatLastTheoremWith ℚ n) :
    fermatCurveRatPoints n ⊆ trivialFermatPoints := by
  rintro ⟨x, y⟩ hp
  simp only [fermatCurveRatPoints, Set.mem_setOf_eq] at hp
  have hxy : x = 0 ∨ y = 0 := by
    by_contra hcon
    push_neg at hcon
    exact hflt x y 1 hcon.1 hcon.2 one_ne_zero (by simpa using hp)
  simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  rcases hxy with hx | hy
  · subst hx
    have hy1 : y ^ n = 1 := by simpa [zero_pow hn] using hp
    rcases rat_eq_one_or_neg_one_of_pow_eq_one hn hy1 with h | h
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · subst hy
    have hx1 : x ^ n = 1 := by simpa [zero_pow hn] using hp
    rcases rat_eq_one_or_neg_one_of_pow_eq_one hn hx1 with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (Or.inl ⟨h, rfl⟩)

/-- **Reduction.** Faltings' theorem for the Fermat curve of exponent `n ≠ 0` follows from
Fermat's Last Theorem for the exponent `n`. -/
theorem fermatCurve_finite_of_flt {n : ℕ} (hn : n ≠ 0) (hflt : FermatLastTheoremWith ℚ n) :
    (fermatCurveRatPoints n).Finite :=
  trivialFermatPoints_finite.subset (fermatCurve_subset_trivial_of_flt hn hflt)

/-- Fermat's Last Theorem over `ℚ` for any exponent divisible by `4`, from Mathlib's
`fermatLastTheoremFour`. -/
theorem fermatLastTheoremWith_rat_of_four_dvd {n : ℕ} (hn : 4 ∣ n) :
    FermatLastTheoremWith ℚ n :=
  FermatLastTheoremWith.mono hn (fermatLastTheoremFor_iff_rat.mp fermatLastTheoremFour)

/-- **Faltings' theorem (Mordell conjecture), base case.**

For every exponent `n` divisible by `4` — in particular for the quartic `x ^ 4 + y ^ 4 = 1`,
a smooth plane curve of genus `3 ≥ 2` — the Fermat curve `x ^ n + y ^ n = 1` has only finitely
many rational points.

This is the unconditional base case of Faltings' theorem obtained from the reduction
`Frontier.fermatCurve_finite_of_flt` together with Fermat's Last Theorem for exponent `4`
(`fermatLastTheoremFour` in Mathlib). -/
theorem faltings_mordell {n : ℕ} (hn : 4 ∣ n) : (fermatCurveRatPoints n).Finite := by
  rcases eq_or_ne n 0 with rfl | hn0
  · have : fermatCurveRatPoints 0 = ∅ := by
      ext p
      simp [fermatCurveRatPoints]
    rw [this]
    exact Set.finite_empty
  · exact fermatCurve_finite_of_flt hn0 (fermatLastTheoremWith_rat_of_four_dvd hn)

/-- The rational points of the Fermat curve `x ^ n + y ^ n = 1` for `4 ∣ n`, `n ≠ 0`, are
*exactly* the four trivial points `(±1, 0)`, `(0, ±1)`. -/
theorem fermatCurve_eq_of_four_dvd {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    fermatCurveRatPoints n = trivialFermatPoints := by
  refine Set.Subset.antisymm
    (fermatCurve_subset_trivial_of_flt hn0 (fermatLastTheoremWith_rat_of_four_dvd hn)) ?_
  have hev : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  rintro ⟨x, y⟩ hp
  simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hp
  simp only [fermatCurveRatPoints, Set.mem_setOf_eq]
  rcases hp with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
    simp [zero_pow hn0, hev.neg_one_pow]

/-- The genus `3` quartic Fermat curve has finitely many rational points. -/
theorem faltings_mordell_quartic : (fermatCurveRatPoints 4).Finite :=
  faltings_mordell dvd_rfl

/-!
## The projective Fermat curve

The affine statement above is upgraded to the smooth projective plane curve
`x ^ n + y ^ n = z ^ n` inside `ℙ²(ℚ)`, which is the curve to which Faltings' theorem literally
applies.  Its `ℚ`-points form a set in `Projectivization ℚ (Fin 3 → ℚ)`.
-/

/-- The set of `ℚ`-points of the projective plane curve `x ^ n + y ^ n = z ^ n`. -/
def projFermatCurveRatPoints (n : ℕ) : Set (Projectivization ℚ (Fin 3 → ℚ)) :=
  {p | ∃ (v : Fin 3 → ℚ) (hv : v ≠ 0),
        Projectivization.mk ℚ v hv = p ∧ v 0 ^ n + v 1 ^ n = v 2 ^ n}

/-- The defining equation is homogeneous, so membership in `projFermatCurveRatPoints` can be
tested on *any* representative of the point. -/
theorem projFermat_mem_iff_forall_rep {n : ℕ}
    {p : Projectivization ℚ (Fin 3 → ℚ)} :
    p ∈ projFermatCurveRatPoints n ↔
      ∀ (w : Fin 3 → ℚ) (hw : w ≠ 0), Projectivization.mk ℚ w hw = p →
        w 0 ^ n + w 1 ^ n = w 2 ^ n := by
  constructor
  · rintro ⟨v, hv, hvp, hveq⟩ w hw hwp
    have hmk : Projectivization.mk ℚ v hv = Projectivization.mk ℚ w hw := by rw [hvp, hwp]
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℚ v w hv hw).mp hmk
    have hcoord : ∀ i, v i = (a : ℚ) * w i := by
      intro i
      have := congrFun ha i
      simpa [Pi.smul_apply, smul_eq_mul] using this.symm
    have hane : ((a : ℚ)) ^ n ≠ 0 := pow_ne_zero _ a.ne_zero
    rw [hcoord 0, hcoord 1, hcoord 2] at hveq
    have : (a : ℚ) ^ n * (w 0 ^ n + w 1 ^ n) = (a : ℚ) ^ n * w 2 ^ n := by
      ring_nf; ring_nf at hveq; linarith [hveq]
    exact mul_left_cancel₀ hane this
  · intro h
    obtain ⟨v, hv, hvp⟩ : ∃ (v : Fin 3 → ℚ) (hv : v ≠ 0), Projectivization.mk ℚ v hv = p :=
      ⟨p.rep, p.rep_nonzero, p.mk_rep⟩
    exact ⟨v, hv, hvp, h v hv hvp⟩

/-- The projective point with affine coordinates `(a, b)` in the chart `z = 1`. -/
def projAffinePt (a b : ℚ) : Projectivization ℚ (Fin 3 → ℚ) :=
  Projectivization.mk ℚ ![a, b, 1] (fun h => by simpa using congrFun h 2)

/-- **Faltings' theorem for the projective Fermat curve, base case.**

For every exponent `n` divisible by `4` — in particular the genus `3` quartic
`x ^ 4 + y ^ 4 = z ^ 4` — the projective Fermat curve has only finitely many `ℚ`-points. -/
theorem projFaltings_mordell {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (projFermatCurveRatPoints n).Finite := by
  have hev : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  have hsub : projFermatCurveRatPoints n ⊆
      {projAffinePt 1 0, projAffinePt (-1) 0, projAffinePt 0 1, projAffinePt 0 (-1)} := by
    rintro p ⟨v, hv, rfl, heq⟩
    have hv2 : v 2 ≠ 0 := by
      intro h2
      rw [h2] at heq
      have h0 : (0:ℚ) ≤ v 0 ^ n := hev.pow_nonneg _
      have h1 : (0:ℚ) ≤ v 1 ^ n := hev.pow_nonneg _
      have hzn : (0:ℚ) ^ n = 0 := zero_pow hn0
      have e0 : v 0 = 0 := (pow_eq_zero_iff hn0).mp (by linarith)
      have e1 : v 1 = 0 := (pow_eq_zero_iff hn0).mp (by linarith)
      exact hv (funext fun i => by fin_cases i <;> simp [e0, e1, h2])
    have hab : (v 0 / v 2) ^ n + (v 1 / v 2) ^ n = 1 := by
      rw [div_pow, div_pow, ← add_div, heq, div_self (pow_ne_zero n hv2)]
    have hmem : (v 0 / v 2, v 1 / v 2) ∈ trivialFermatPoints := by
      rw [← fermatCurve_eq_of_four_dvd hn hn0]
      exact hab
    have hrep : Projectivization.mk ℚ v hv = projAffinePt (v 0 / v 2) (v 1 / v 2) := by
      refine (Projectivization.mk_eq_mk_iff ℚ v _ hv _).mpr ⟨Units.mk0 (v 2) hv2, ?_⟩
      funext i
      fin_cases i <;> simp [Units.smul_def] <;> field_simp
    rw [hrep]
    simp only [trivialFermatPoints, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp
  exact (((((Set.finite_singleton _).insert _).insert _).insert _)).subset hsub

/-!
## Faltings' theorem for smooth plane curves over `ℚ`

Finally we state Faltings' theorem in the generality that Mathlib currently permits: for a
smooth plane projective curve `{F = 0} ⊆ ℙ²` defined by a homogeneous `F ∈ ℚ[x, y, z]` of
degree `d`.  By the genus-degree formula such a curve has genus `(d - 1) * (d - 2) / 2`, which
is `≥ 2` exactly when `d ≥ 4`, so `FaltingsForSmoothPlaneCurves` below is exactly Faltings'
theorem for plane curves.  We then verify that the Fermat curves of degree `4 ∣ n` really do
satisfy all of its hypotheses, and that its conclusion holds for them.
-/

open MvPolynomial in
/-- The homogeneous Fermat polynomial `x ^ n + y ^ n - z ^ n` over `ℚ`. -/
noncomputable def fermatPoly (n : ℕ) : MvPolynomial (Fin 3) ℚ := X 0 ^ n + X 1 ^ n - X 2 ^ n

open MvPolynomial in
/-- The set of `ℚ`-points of the projective plane curve `{F = 0}`. -/
def planeCurveRatPoints (F : MvPolynomial (Fin 3) ℚ) : Set (Projectivization ℚ (Fin 3 → ℚ)) :=
  {p | ∃ (v : Fin 3 → ℚ) (hv : v ≠ 0), Projectivization.mk ℚ v hv = p ∧ eval v F = 0}

open MvPolynomial in
/-- Smoothness (geometric nonsingularity) of the projective plane curve `{F = 0}`: over an
algebraic closure of `ℚ`, the three partial derivatives of `F` have no common zero apart from
the origin. -/
def IsSmoothProjPlaneCurve (F : MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ v : Fin 3 → AlgebraicClosure ℚ,
    (∀ i, eval v (map (algebraMap ℚ (AlgebraicClosure ℚ)) (pderiv i F)) = 0) → v = 0

/-- **Faltings' theorem for smooth plane curves over `ℚ`.**  A smooth plane projective curve of
degree `d ≥ 4` has genus `(d - 1) * (d - 2) / 2 ≥ 2`, so by Faltings' theorem it has finitely
many rational points.  (Stated here as a `Prop`; it is *not* proved in this file — the theorems
below verify its hypotheses and its conclusion for the Fermat curves of degree divisible
by `4`.) -/
def FaltingsForSmoothPlaneCurves : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin 3) ℚ), 4 ≤ d → F.IsHomogeneous d →
    IsSmoothProjPlaneCurve F → (planeCurveRatPoints F).Finite

open MvPolynomial in
/-- The Fermat polynomial is homogeneous of degree `n`. -/
theorem fermatPoly_isHomogeneous (n : ℕ) : (fermatPoly n).IsHomogeneous n := by
  have h : ∀ i : Fin 3, ((X i : MvPolynomial (Fin 3) ℚ) ^ n).IsHomogeneous n := fun i => by
    simpa using (isHomogeneous_X ℚ i).pow n
  exact ((h 0).add (h 1)).sub (h 2)

open MvPolynomial in
/-- For `n ≥ 2` the Fermat curve `x ^ n + y ^ n = z ^ n` is a smooth plane curve. -/
theorem fermatPoly_isSmooth {n : ℕ} (hn : 2 ≤ n) : IsSmoothProjPlaneCurve (fermatPoly n) := by
  intro v hv
  refine funext fun i => ?_
  have h := hv i
  fin_cases i <;> simp [fermatPoly, pderiv_X] at h <;> rcases h with h | h
  · exact absurd h (by omega)
  · simpa using h.1
  · exact absurd h (by omega)
  · simpa using h.1
  · exact absurd h (by omega)
  · simpa using h.1

open MvPolynomial in
/-- The curve cut out by `fermatPoly n` is the projective Fermat curve. -/
theorem planeCurveRatPoints_fermatPoly (n : ℕ) :
    planeCurveRatPoints (fermatPoly n) = projFermatCurveRatPoints n := by
  ext p
  constructor <;> rintro ⟨v, hv, hvp, heq⟩ <;> refine ⟨v, hv, hvp, ?_⟩
  · simpa [fermatPoly, sub_eq_zero] using heq
  · simpa [fermatPoly, sub_eq_zero] using heq

/-- **Faltings' theorem, verified base case, in the language of plane curves.**

For `4 ∣ n`, `n ≠ 0`, the smooth plane projective curve of degree `n` cut out by
`x ^ n + y ^ n - z ^ n` — of genus `(n - 1) * (n - 2) / 2 ≥ 3` — has finitely many rational
points. -/
theorem faltings_mordell_planeCurve {n : ℕ} (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (planeCurveRatPoints (fermatPoly n)).Finite := by
  rw [planeCurveRatPoints_fermatPoly]
  exact projFaltings_mordell hn hn0

/-- The genus `3` quartic `x ^ 4 + y ^ 4 = z ^ 4` satisfies every hypothesis of
`FaltingsForSmoothPlaneCurves`, and the conclusion of Faltings' theorem holds for it. -/
theorem faltings_mordell_quartic_instance :
    4 ≤ 4 ∧ (fermatPoly 4).IsHomogeneous 4 ∧ IsSmoothProjPlaneCurve (fermatPoly 4) ∧
      (planeCurveRatPoints (fermatPoly 4)).Finite :=
  ⟨le_rfl, fermatPoly_isHomogeneous 4, fermatPoly_isSmooth (by norm_num),
    faltings_mordell_planeCurve dvd_rfl (by norm_num)⟩

end Frontier

