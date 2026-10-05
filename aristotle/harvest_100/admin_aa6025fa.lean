/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Math2

/-- The standard symplectic form on `ℝ^{2n}`, with coordinates indexed by
`Fin n × Fin 2` (the pair `(i, 0)`, `(i, 1)` being the `i`-th conjugate pair). -/
def symplecticForm {n : ℕ} (u v : Fin n × Fin 2 → ℝ) : ℝ :=
  ∑ i : Fin n, (u (i, 0) * v (i, 1) - u (i, 1) * v (i, 0))

/-- The squared euclidean norm on `ℝ^{2n}`. -/
def sqNorm {n : ℕ} (v : Fin n × Fin 2 → ℝ) : ℝ := ∑ p : Fin n × Fin 2, (v p) ^ 2

/-- The open euclidean ball of radius `r` centred at the origin. -/
def ball {n : ℕ} (r : ℝ) : Set (Fin n × Fin 2 → ℝ) := {v | sqNorm v < r ^ 2}

/-- The open symplectic cylinder of radius `R`: the set of points whose first
conjugate pair of coordinates lies in the open disc of radius `R`. -/
def cylinder {n : ℕ} (R : ℝ) : Set (Fin (n + 1) × Fin 2 → ℝ) :=
  {w | (w (0, 0)) ^ 2 + (w (0, 1)) ^ 2 < R ^ 2}

/-- A linear map is symplectic if it preserves the standard symplectic form. -/
def IsSymplectic {n : ℕ}
    (Φ : (Fin n × Fin 2 → ℝ) →ₗ[ℝ] (Fin n × Fin 2 → ℝ)) : Prop :=
  ∀ u v, symplecticForm (Φ u) (Φ v) = symplecticForm u v

/-- The standard complex structure `J`. -/
def jvec {n : ℕ} (u : Fin n × Fin 2 → ℝ) : Fin n × Fin 2 → ℝ :=
  fun p => if p.2 = 0 then -u (p.1, 1) else u (p.1, 0)

lemma sqNorm_eq {n : ℕ} (v : Fin n × Fin 2 → ℝ) :
    sqNorm v = ∑ i : Fin n, ((v (i, 0)) ^ 2 + (v (i, 1)) ^ 2) := by
  simp [sqNorm, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma sqNorm_nonneg {n : ℕ} (v : Fin n × Fin 2 → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma eq_zero_of_sqNorm_eq_zero {n : ℕ} {v : Fin n × Fin 2 → ℝ} (h : sqNorm v = 0) :
    v = 0 := by
  funext p
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun q (_ : q ∈ Finset.univ) => sq_nonneg (v q))).1 h
      p (Finset.mem_univ p)
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this

lemma symplecticForm_eq_dot {n : ℕ} (u v : Fin n × Fin 2 → ℝ) :
    symplecticForm u v = ∑ p : Fin n × Fin 2, jvec u p * v p := by
  rw [symplecticForm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h0 : jvec u (i, 0) = -u (i, 1) := by simp [jvec]
  have h1 : jvec u (i, 1) = u (i, 0) := by simp [jvec]
  rw [Fin.sum_univ_two, h0, h1]
  ring

lemma sqNorm_jvec {n : ℕ} (u : Fin n × Fin 2 → ℝ) : sqNorm (jvec u) = sqNorm u := by
  rw [sqNorm_eq, sqNorm_eq]
  refine Finset.sum_congr rfl fun i _ => by simp [jvec]; ring

lemma symplecticForm_self_jvec {n : ℕ} (u : Fin n × Fin 2 → ℝ) :
    symplecticForm u (jvec u) = sqNorm u := by
  rw [sqNorm_eq, symplecticForm]
  refine Finset.sum_congr rfl fun i _ => by simp [jvec]; ring

lemma symplecticForm_smul_right {n : ℕ} (c : ℝ) (u v : Fin n × Fin 2 → ℝ) :
    symplecticForm u (c • v) = c * symplecticForm u v := by
  simp only [symplecticForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma sqNorm_smul {n : ℕ} (c : ℝ) (v : Fin n × Fin 2 → ℝ) :
    sqNorm (c • v) = c ^ 2 * sqNorm v := by
  simp only [sqNorm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => by ring

/-- Cauchy–Schwarz for the symplectic form. -/
lemma symplecticForm_sq_le {n : ℕ} (u v : Fin n × Fin 2 → ℝ) :
    (symplecticForm u v) ^ 2 ≤ sqNorm u * sqNorm v := by
  rw [symplecticForm_eq_dot]
  calc (∑ p : Fin n × Fin 2, jvec u p * v p) ^ 2
      ≤ (∑ p : Fin n × Fin 2, (jvec u p) ^ 2) * ∑ p : Fin n × Fin 2, (v p) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = sqNorm u * sqNorm v := by rw [← sqNorm, ← sqNorm, sqNorm_jvec]

/-- Key quantitative step: if two vectors `p`, `q` control the two cylinder
coordinates and one of them has squared norm at least one, the ball cannot be
squeezed. -/
lemma radius_le_of_one_le_sqNorm {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (p q : Fin n × Fin 2 → ℝ) (hp : 1 ≤ sqNorm p)
    (h : ∀ v : Fin n × Fin 2 → ℝ, sqNorm v < r ^ 2 →
      (symplecticForm p v) ^ 2 + (symplecticForm q v) ^ 2 < R ^ 2) :
    r ≤ R := by
  by_contra hlt
  push_neg at hlt
  have hs : (0 : ℝ) < sqNorm p := lt_of_lt_of_le zero_lt_one hp
  set s : ℝ := Real.sqrt (sqNorm p) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.mpr hs
  have hs2 : s ^ 2 = sqNorm p := Real.sq_sqrt hs.le
  set v : Fin n × Fin 2 → ℝ := (R / s) • jvec p with hv
  have hnv : sqNorm v = R ^ 2 := by
    rw [hv, sqNorm_smul, sqNorm_jvec, div_pow, ← hs2]
    field_simp
  have hball : sqNorm v < r ^ 2 := by
    rw [hnv]
    exact sq_lt_sq' (by linarith) hlt
  have hpv : symplecticForm p v = R * s := by
    rw [hv, symplecticForm_smul_right, symplecticForm_self_jvec, ← hs2]
    field_simp
  have hR2 : R ^ 2 ≤ (symplecticForm p v) ^ 2 := by
    rw [hpv]
    have h1 : 1 ≤ s := by
      nlinarith [hspos, hs2]
    nlinarith [hR, hspos]
  have := h v hball
  nlinarith [sq_nonneg (symplecticForm q v)]

lemma symplecticForm_single_fst {n : ℕ} (w : Fin (n + 1) × Fin 2 → ℝ) :
    symplecticForm (Pi.single ((0 : Fin (n + 1)), (0 : Fin 2)) (1 : ℝ)) w = w (0, 1) := by
  rw [symplecticForm]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro b _ hb
    simp [Prod.ext_iff, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma symplecticForm_single_snd {n : ℕ} (w : Fin (n + 1) × Fin 2 → ℝ) :
    symplecticForm (Pi.single ((0 : Fin (n + 1)), (1 : Fin 2)) (1 : ℝ)) w = -w (0, 0) := by
  rw [symplecticForm]
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp
  · intro b _ hb
    simp [Prod.ext_iff, hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma injective_of_isSymplectic {n : ℕ}
    {Φ : (Fin n × Fin 2 → ℝ) →ₗ[ℝ] (Fin n × Fin 2 → ℝ)} (hΦ : IsSymplectic Φ) :
    Function.Injective Φ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro u hu
  have h0 : symplecticForm u (jvec u) = 0 := by
    rw [← hΦ u (jvec u), hu]
    simp [symplecticForm]
  exact eq_zero_of_sqNorm_eq_zero (by rw [← symplecticForm_self_jvec, h0])

/-- **Gromov's nonsqueezing theorem** (linear case).

If a linear symplectomorphism of `ℝ^{2(n+1)}` maps the open ball of radius `r > 0`
into the open symplectic cylinder of radius `R ≥ 0` (the cylinder over the first
conjugate coordinate plane), then `r ≤ R`. -/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (Φ : (Fin (n + 1) × Fin 2 → ℝ) →ₗ[ℝ] (Fin (n + 1) × Fin 2 → ℝ))
    (hΦ : IsSymplectic Φ) (hmap : Φ '' ball r ⊆ cylinder R) :
    r ≤ R := by
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective).1 (injective_of_isSymplectic hΦ)
  obtain ⟨p, hp⟩ := hsurj (Pi.single ((0 : Fin (n + 1)), (0 : Fin 2)) (1 : ℝ))
  obtain ⟨q, hq⟩ := hsurj (Pi.single ((0 : Fin (n + 1)), (1 : Fin 2)) (1 : ℝ))
  -- the two cylinder coordinates of `Φ v` are given by the symplectic products with `p`, `q`
  have hpv : ∀ v, symplecticForm p v = (Φ v) (0, 1) := by
    intro v
    rw [← hΦ p v, hp, symplecticForm_single_fst]
  have hqv : ∀ v, symplecticForm q v = -(Φ v) (0, 0) := by
    intro v
    rw [← hΦ q v, hq, symplecticForm_single_snd]
  have hbound : ∀ v : Fin (n + 1) × Fin 2 → ℝ, sqNorm v < r ^ 2 →
      (symplecticForm p v) ^ 2 + (symplecticForm q v) ^ 2 < R ^ 2 := by
    intro v hv
    have : Φ v ∈ cylinder R := hmap ⟨v, hv, rfl⟩
    have hc : (Φ v (0, 0)) ^ 2 + (Φ v (0, 1)) ^ 2 < R ^ 2 := this
    rw [hpv v, hqv v, neg_sq]
    linarith
  -- `p` and `q` are symplectically dual, so one of them has norm at least one
  have hpq : symplecticForm p q = 1 := by
    rw [hpv q, hq]
    simp
  have hcs : (1 : ℝ) ≤ sqNorm p * sqNorm q := by
    have := symplecticForm_sq_le p q
    rw [hpq] at this
    simpa using this
  rcases le_or_gt 1 (sqNorm p) with h | h
  · exact radius_le_of_one_le_sqNorm hR p q h hbound
  · have hq1 : 1 ≤ sqNorm q := by
      nlinarith [sqNorm_nonneg p, sqNorm_nonneg q]
    refine radius_le_of_one_le_sqNorm hR q p hq1 ?_
    intro v hv
    have := hbound v hv
    linarith

/-- The hypotheses of `gromov_nonsqueezing` are not vacuous: the identity is a linear
symplectomorphism, and it does squeeze the ball of radius `r` into the cylinder of
radius `R` whenever `r ≤ R`.  Together with `gromov_nonsqueezing` this shows that the
ball of radius `r` embeds linearly symplectically into the cylinder of radius `R`
if and only if `r ≤ R`. -/
theorem id_isSymplectic {n : ℕ} : IsSymplectic (LinearMap.id (R := ℝ)
    (M := (Fin n × Fin 2 → ℝ))) := fun _ _ => rfl

theorem ball_subset_cylinder_of_le {n : ℕ} {r R : ℝ} (h : r ≤ R) (hr : 0 ≤ r) :
    (LinearMap.id (R := ℝ) (M := (Fin (n + 1) × Fin 2 → ℝ))) '' ball r ⊆ cylinder R := by
  rintro w ⟨v, hv, rfl⟩
  have hle : (v (0, 0)) ^ 2 + (v (0, 1)) ^ 2 ≤ sqNorm v := by
    rw [sqNorm_eq]
    exact Finset.single_le_sum
      (f := fun i : Fin (n + 1) => (v (i, 0)) ^ 2 + (v (i, 1)) ^ 2)
      (fun i _ => by positivity) (Finset.mem_univ 0)
  have hlt : sqNorm v < r ^ 2 := hv
  have : r ^ 2 ≤ R ^ 2 := by nlinarith
  exact lt_of_le_of_lt hle (by simpa using lt_of_lt_of_le hlt this)

end Math2

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

