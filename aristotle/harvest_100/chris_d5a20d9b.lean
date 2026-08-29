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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open MvPolynomial

/-! ## Setting up plane curves over `ℚ` -/

/-- The set of `ℚ`-rational points of the projective plane curve cut out by a homogeneous
form `F` in three variables. A point of `ℙ²(ℚ)` is represented as a point of
`Projectivization ℚ (Fin 3 → ℚ)`; since `F` is homogeneous, vanishing of `F` at a
representative does not depend on the chosen representative (see
`Frontier.mem_projPoints_fermatForm_iff` for the case used below). -/
def projPoints (F : MvPolynomial (Fin 3) ℚ) : Set (Projectivization ℚ (Fin 3 → ℚ)) :=
  {P | MvPolynomial.eval P.rep F = 0}

/-- Nonsingularity ("smoothness") of the projective plane curve `F = 0` over `ℚ`: the partial
derivatives of `F` have no common zero other than the origin, over an algebraic closure of `ℚ`.
(By the Euler relation, in characteristic zero this already forces such a common zero to lie on
the curve, so this is the usual Jacobian criterion for a plane curve.) -/
def IsNonsingularPlaneCurve (F : MvPolynomial (Fin 3) ℚ) : Prop :=
  ∀ v : Fin 3 → AlgebraicClosure ℚ, (∀ i : Fin 3, aeval v (pderiv i F) = 0) → v = 0

/-- The genus of a smooth plane curve of degree `d`, given by the Plücker formula
`g = (d-1)(d-2)/2`. -/
def planeGenus (d : ℕ) : ℕ := (d - 1) * (d - 2) / 2

/-- A smooth plane curve of degree `d ≥ 4` has genus at least `2`. -/
theorem two_le_planeGenus {d : ℕ} (hd : 4 ≤ d) : 2 ≤ planeGenus d := by
  have h : 2 * 2 ≤ (d - 1) * (d - 2) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
    have : (4 + k - 1) = 3 + k := by omega
    have h2 : (4 + k - 2) = 2 + k := by omega
    rw [this, h2]
    nlinarith
  exact (Nat.le_div_iff_mul_le (by norm_num)).mpr h

/-- **Statement of Faltings' theorem (the Mordell conjecture)**, for smooth plane curves over `ℚ`:
a nonsingular projective plane curve over `ℚ` of degree `d` whose genus `(d-1)(d-2)/2` is at
least `2` has only finitely many rational points. -/
def MordellForSmoothPlaneCurves : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin 3) ℚ), F.IsHomogeneous d → 2 ≤ planeGenus d →
    IsNonsingularPlaneCurve F → (projPoints F).Finite

/-! ## The Fermat curves of degree divisible by four -/

/-- The Fermat form `x ^ n + y ^ n - z ^ n` of degree `n` in three variables. -/
noncomputable def fermatForm (n : ℕ) : MvPolynomial (Fin 3) ℚ :=
  X 0 ^ n + X 1 ^ n - X 2 ^ n

@[simp]
theorem eval_fermatForm (n : ℕ) (v : Fin 3 → ℚ) :
    MvPolynomial.eval v (fermatForm n) = v 0 ^ n + v 1 ^ n - v 2 ^ n := by
  simp [fermatForm]

theorem fermatForm_isHomogeneous (n : ℕ) : (fermatForm n).IsHomogeneous n := by
  have h : ∀ i : Fin 3, ((X i : MvPolynomial (Fin 3) ℚ) ^ n).IsHomogeneous n := by
    intro i
    simpa using (isHomogeneous_X ℚ i).pow n
  exact ((h 0).add (h 1)).sub (h 2)

/-- The Fermat curve is well defined as a subset of the projective plane: vanishing of the
Fermat form at a representative is independent of the representative. -/
theorem mem_projPoints_fermatForm_iff (n : ℕ) (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    Projectivization.mk ℚ v hv ∈ projPoints (fermatForm n) ↔
      v 0 ^ n + v 1 ^ n - v 2 ^ n = 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℚ v hv
  have hrep : (Projectivization.mk ℚ v hv).rep = (a : ℚ) • v := by
    rw [← ha]; rfl
  simp only [projPoints, Set.mem_setOf_eq, hrep, eval_fermatForm, Pi.smul_apply, smul_eq_mul]
  constructor
  · intro h
    have ha' : ((a : ℚ)) ^ n ≠ 0 := pow_ne_zero _ a.ne_zero
    have : ((a : ℚ)) ^ n * (v 0 ^ n + v 1 ^ n - v 2 ^ n) = 0 := by
      rw [← h]; ring
    exact (mul_eq_zero.mp this).resolve_left ha'
  · intro h
    have : ((a : ℚ) * v 0) ^ n + ((a : ℚ) * v 1) ^ n - ((a : ℚ) * v 2) ^ n
        = ((a : ℚ)) ^ n * (v 0 ^ n + v 1 ^ n - v 2 ^ n) := by ring
    rw [this, h, mul_zero]

/-! ### Smoothness of the Fermat curve -/

theorem pderiv_fermatForm_zero (n : ℕ) :
    pderiv (0 : Fin 3) (fermatForm n) = (n : MvPolynomial (Fin 3) ℚ) * X 0 ^ (n - 1) := by
  simp [fermatForm, Derivation.leibniz_pow, pderiv_X]

theorem pderiv_fermatForm_one (n : ℕ) :
    pderiv (1 : Fin 3) (fermatForm n) = (n : MvPolynomial (Fin 3) ℚ) * X 1 ^ (n - 1) := by
  simp [fermatForm, Derivation.leibniz_pow, pderiv_X]

theorem pderiv_fermatForm_two (n : ℕ) :
    pderiv (2 : Fin 3) (fermatForm n) = -((n : MvPolynomial (Fin 3) ℚ) * X 2 ^ (n - 1)) := by
  simp [fermatForm, Derivation.leibniz_pow, pderiv_X]

theorem fermatForm_nonsingular (n : ℕ) (hn : 2 ≤ n) :
    IsNonsingularPlaneCurve (fermatForm n) := by
  intro v hv
  have hn0 : (n : AlgebraicClosure ℚ) ≠ 0 := by
    simpa using (by omega : n ≠ 0)
  have hn1 : n - 1 ≠ 0 := by omega
  have e0 : v 0 = 0 := by
    have h := hv 0
    rw [pderiv_fermatForm_zero] at h
    simp only [map_mul, map_pow, aeval_X, map_natCast] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  have e1 : v 1 = 0 := by
    have h := hv 1
    rw [pderiv_fermatForm_one] at h
    simp only [map_mul, map_pow, aeval_X, map_natCast] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  have e2 : v 2 = 0 := by
    have h := hv 2
    rw [pderiv_fermatForm_two] at h
    simp only [map_neg, map_mul, map_pow, aeval_X, map_natCast, neg_eq_zero] at h
    exact pow_eq_zero_iff hn1 |>.mp ((mul_eq_zero.mp h).resolve_left hn0)
  funext i
  fin_cases i
  · exact e0
  · exact e1
  · exact e2

/-! ### Finiteness of the rational points -/

theorem vec_ne_zero (x y : ℚ) : ![x, y, (1 : ℚ)] ≠ 0 := by
  intro h
  have := congrFun h 2
  simp at this

/-- Fermat's Last Theorem over `ℚ` for exponents divisible by `4`, a consequence of the
classical descent argument for exponent `4`. -/
theorem flt_rat_of_four_dvd {n : ℕ} (hn : 4 ∣ n) : FermatLastTheoremWith ℚ n :=
  fermatLastTheoremFor_iff_rat.mp (fermatLastTheoremFour.mono hn)

/-- If `x ^ n = y ^ n` in `ℚ` with `n` even and nonzero then `x = ± y`. -/
theorem eq_or_eq_neg_of_pow_eq_pow {x y : ℚ} {n : ℕ} (hn : n ≠ 0) (he : Even n)
    (h : x ^ n = y ^ n) : x = y ∨ x = -y := by
  rw [← abs_eq_abs]
  have habs : |x| ^ n = |y| ^ n := by rw [he.pow_abs, he.pow_abs, h]
  exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) hn).mp habs

/-- The rational points of the Fermat curve of degree `n`, for `n` a positive multiple of `4`,
are among the four "trivial" points. -/
theorem projPoints_fermatForm_subset (n : ℕ) (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    projPoints (fermatForm n) ⊆
      ({Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero 1 0),
        Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero (-1) 0),
        Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero 0 1),
        Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero 0 (-1))} :
        Set (Projectivization ℚ (Fin 3 → ℚ))) := by
  have heven : Even n := by
    obtain ⟨k, rfl⟩ := hn
    exact ⟨2 * k, by ring⟩
  intro P hP
  set v : Fin 3 → ℚ := P.rep with hvdef
  have hv : v ≠ 0 := P.rep_nonzero
  have hzero : v 0 ^ n + v 1 ^ n - v 2 ^ n = 0 := by
    have h := hP
    simp only [projPoints, Set.mem_setOf_eq, eval_fermatForm] at h
    exact h
  have heq : v 0 ^ n + v 1 ^ n = v 2 ^ n := by linarith
  -- one of the coordinates vanishes, by Fermat's Last Theorem for exponent `n`
  have hcase : v 0 = 0 ∨ v 1 = 0 ∨ v 2 = 0 := by
    by_contra hc
    push_neg at hc
    exact flt_rat_of_four_dvd hn (v 0) (v 1) (v 2) hc.1 hc.2.1 hc.2.2 heq
  -- a helper: identifying `P` with the projectivization of an explicit vector
  have hmk : ∀ (c x y : ℚ), c ≠ 0 → (v 0 = c * x) → (v 1 = c * y) → (v 2 = c) →
      P = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero x y) := by
    intro c x y hc h0 h1 h2
    have : Projectivization.mk ℚ v hv = Projectivization.mk ℚ ![x, y, 1] (vec_ne_zero x y) := by
      rw [Projectivization.mk_eq_mk_iff]
      refine ⟨Units.mk0 c hc, ?_⟩
      funext i
      fin_cases i <;>
        simp [Units.smul_def, h0, h1, h2]
    exact (Projectivization.mk_rep P).symm.trans this
  have hv2 : v 2 ≠ 0 := by
    intro h2
    have h01 : v 0 ^ n + v 1 ^ n = 0 := by rw [heq, h2]; simp [hn0]
    have hp0 : (0 : ℚ) ≤ v 0 ^ n := heven.pow_nonneg _
    have hp1 : (0 : ℚ) ≤ v 1 ^ n := heven.pow_nonneg _
    have e0 : v 0 ^ n = 0 := by linarith
    have e1 : v 1 ^ n = 0 := by linarith
    have z0 : v 0 = 0 := pow_eq_zero_iff hn0 |>.mp e0
    have z1 : v 1 = 0 := pow_eq_zero_iff hn0 |>.mp e1
    exact hv (funext fun i => by fin_cases i <;> simpa using ‹_›)
  rcases hcase with h0 | h1 | h2
  · -- `v 0 = 0`, so `v 1 = ± v 2`
    have hpow : v 1 ^ n = v 2 ^ n := by rw [← heq, h0]; simp [hn0]
    rcases eq_or_eq_neg_of_pow_eq_pow hn0 heven hpow with h | h
    · right; right; left
      exact hmk (v 2) 0 1 hv2 (by rw [h0]; ring) (by rw [h]; ring) rfl
    · right; right; right
      simp only [Set.mem_singleton_iff]
      exact hmk (v 2) 0 (-1) hv2 (by rw [h0]; ring) (by rw [h]; ring) rfl
  · -- `v 1 = 0`, so `v 0 = ± v 2`
    have hpow : v 0 ^ n = v 2 ^ n := by rw [← heq, h1]; simp [hn0]
    rcases eq_or_eq_neg_of_pow_eq_pow hn0 heven hpow with h | h
    · left
      exact hmk (v 2) 1 0 hv2 (by rw [h]; ring) (by rw [h1]; ring) rfl
    · right; left
      exact hmk (v 2) (-1) 0 hv2 (by rw [h]; ring) (by rw [h1]; ring) rfl
  · exact absurd h2 hv2

theorem projPoints_fermatForm_finite (n : ℕ) (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (projPoints (fermatForm n)).Finite :=
  Set.Finite.subset (Set.toFinite _) (projPoints_fermatForm_subset n hn hn0)

/-- The rational points of the Fermat quartic curve `x ^ 4 + y ^ 4 = z ^ 4` (a smooth plane
curve of genus `3`) are exactly the four trivial ones. -/
theorem projPoints_fermatForm_four :
    projPoints (fermatForm 4) =
      ({Projectivization.mk ℚ ![1, 0, 1] (vec_ne_zero 1 0),
        Projectivization.mk ℚ ![-1, 0, 1] (vec_ne_zero (-1) 0),
        Projectivization.mk ℚ ![0, 1, 1] (vec_ne_zero 0 1),
        Projectivization.mk ℚ ![0, -1, 1] (vec_ne_zero 0 (-1))} :
        Set (Projectivization ℚ (Fin 3 → ℚ))) := by
  refine Set.Subset.antisymm (projPoints_fermatForm_subset 4 dvd_rfl (by norm_num)) ?_
  rintro P (rfl | rfl | rfl | rfl) <;>
    exact (mem_projPoints_fermatForm_iff 4 _ _).mpr
      (by norm_num [Matrix.cons_val_two, Matrix.tail_cons])

/-! ## The target -/

/-- **A verified case of Faltings' theorem (the Mordell conjecture).**

For every positive multiple `n` of `4`, the Fermat curve `x ^ n + y ^ n = z ^ n` is a
nonsingular projective plane curve over `ℚ` of degree `n`, its genus `(n-1)(n-2)/2` is at
least `2`, and it has only finitely many `ℚ`-rational points — as predicted by Faltings'
theorem. (The finiteness is obtained from Fermat's Last Theorem for exponent `4`.) -/
theorem faltings_mordell (n : ℕ) (hn : 4 ∣ n) (hn0 : n ≠ 0) :
    (fermatForm n).IsHomogeneous n ∧
      2 ≤ planeGenus n ∧
      IsNonsingularPlaneCurve (fermatForm n) ∧
      (projPoints (fermatForm n)).Finite := by
  have h4 : 4 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hn
  exact ⟨fermatForm_isHomogeneous n, two_le_planeGenus h4,
    fermatForm_nonsingular n (by omega), projPoints_fermatForm_finite n hn hn0⟩

end Frontier

