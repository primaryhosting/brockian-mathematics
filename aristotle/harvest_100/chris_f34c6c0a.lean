/-
# Gauss Bonnet Polygon
Category: Pure Mathematics
Target: Math.gauss_bonnet_polygon
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.SphericalWedge

/-!
# Gauss Bonnet Polygon

Category: Pure Mathematics.  Target: `Math.gauss_bonnet_polygon`.

## Overview

We prove Girard's theorem (the Gauss–Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the three interior angles of a spherical triangle equals `π` plus the
area of the triangle.

The area of a region `S` of the unit sphere in `ℝ³` is defined as three times the Lebesgue
volume of the cone over `S` with apex the origin (this is the standard normalisation: the
cone over the whole sphere is the unit ball, of volume `4π/3`, giving total area `4π`).

The proof is the classical "lune" argument.  The three great circles through the pairs of
vertices cut the sphere into eight triangles; each of the three lunes containing the
triangle `T` decomposes as `T` together with one of the neighbouring triangles.
-/

open MeasureTheory Metric Real Set InnerProductGeometry Pointwise

noncomputable section

namespace GaussBonnet

/-! ### Step 4: the normals to the sides of a spherical triangle -/

/-- The interior angle at the vertex `u` of the spherical triangle with vertices `u`, `v`, `w`:
the angle between the tangent directions at `u` of the two geodesics from `u` to `v` and
from `u` to `w`. -/
def sphericalAngle (u v w : E3) : ℝ :=
  angle (v - (inner ℝ u v : ℝ) • u) (w - (inner ℝ u w : ℝ) • u)

lemma indep_coeffs {u v w : E3} (hind : LinearIndependent ℝ ![u, v, w]) {a b c : ℝ}
    (h : a • u + b • v + c • w = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [Fintype.linearIndependent_iff] at hind
  have h2 := hind ![a, b, c] (by rw [Fin.sum_univ_three]; simpa using h)
  exact ⟨h2 0, h2 1, h2 2⟩

/-- A vector of `ℝ³` is determined by its inner products with a basis. -/
lemma eq_of_inner_eq {u v w y y' : E3} (hind : LinearIndependent ℝ ![u, v, w])
    (h1 : inner ℝ y u = (inner ℝ y' u : ℝ)) (h2 : inner ℝ y v = (inner ℝ y' v : ℝ))
    (h3 : inner ℝ y w = (inner ℝ y' w : ℝ)) : y = y' := by
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by simp
  have hbas : ⇑(basisOfLinearIndependentOfCardEqFinrank hind hcard) = ![u, v, w] :=
    coe_basisOfLinearIndependentOfCardEqFinrank hind hcard
  set bas := basisOfLinearIndependentOfCardEqFinrank hind hcard with hbasdef
  have hz : ∀ i, inner ℝ (y - y') (bas i) = (0 : ℝ) := by
    intro i
    fin_cases i <;> simp [hbas, inner_sub_left, h1, h2, h3]
  have key : inner ℝ (y - y') (y - y') = (0 : ℝ) := by
    nth_rewrite 2 [show y - y' = ∑ i, bas.repr (y - y') i • bas i from (bas.sum_repr _).symm]
    rw [inner_sum]
    simp [real_inner_smul_right, hz]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp key)

/-- The angle between the two dual vectors `Q p - R q` and `P q - R p` is the supplement of
the angle between `p` and `q`. -/
lemma lune_angle_aux (p q : E3) (P Q R D : ℝ)
    (hPdef : P = inner ℝ p p) (hQdef : Q = inner ℝ q q) (hRdef : R = inner ℝ p q)
    (hnp : ‖p‖ ^ 2 = P) (hnq : ‖q‖ ^ 2 = Q)
    (hPpos : 0 < P) (hQpos : 0 < Q) (hD : D = P * Q - R ^ 2) (hDpos : 0 < D)
    (hm0sq : ‖Q • p - R • q‖ ^ 2 = Q * D) :
    angle (D⁻¹ • (Q • p - R • q)) (D⁻¹ • (P • q - R • p)) = π - angle p q := by
  have hn0sq : ‖P • q - R • p‖ ^ 2 = P * D := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hnp, hnq, hD, real_inner_comm p q, ← hRdef]
    ring
  have hinner : inner ℝ (Q • p - R • q) (P • q - R • p) = -R * D := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_comm p q, ← hRdef, ← hPdef, ← hQdef, hD]
    ring
  have hppos : 0 < ‖p‖ := by nlinarith [norm_nonneg p]
  have hqpos : 0 < ‖q‖ := by nlinarith [norm_nonneg q]
  have hnormprod : ‖Q • p - R • q‖ * ‖P • q - R • p‖ = D * (‖p‖ * ‖q‖) := by
    have h1 : (0 : ℝ) ≤ ‖Q • p - R • q‖ * ‖P • q - R • p‖ := by positivity
    have h2 : (0 : ℝ) ≤ D * (‖p‖ * ‖q‖) := by positivity
    have hsq : (‖Q • p - R • q‖ * ‖P • q - R • p‖) ^ 2 = (D * (‖p‖ * ‖q‖)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, hm0sq, hn0sq, hnp, hnq]; ring
    calc ‖Q • p - R • q‖ * ‖P • q - R • p‖
        = √((‖Q • p - R • q‖ * ‖P • q - R • p‖) ^ 2) := (Real.sqrt_sq h1).symm
      _ = √((D * (‖p‖ * ‖q‖)) ^ 2) := by rw [hsq]
      _ = D * (‖p‖ * ‖q‖) := Real.sqrt_sq h2
  rw [angle_smul_left_of_pos _ _ (by positivity), angle_smul_right_of_pos _ _ (by positivity)]
  show Real.arccos _ = π - Real.arccos _
  rw [hinner, hnormprod, ← hRdef, ← Real.arccos_neg]
  congr 1
  field_simp

/-- **The lune at a vertex.**  For a nondegenerate spherical triangle `u v w`, there are
vectors `m`, `n` dual to `v` and `w` (in the basis `u, v, w`), and the angle between them is
the supplement of the interior angle of the triangle at `u`.  The corresponding lune is
`{x | 0 ≤ ⟪m, x⟫ ∧ 0 ≤ ⟪n, x⟫}`. -/
theorem exists_lune_normals (u v w : E3) (hu : ‖u‖ = 1) (hind : LinearIndependent ℝ ![u, v, w]) :
    (0 < sphericalAngle u v w ∧ sphericalAngle u v w < π) ∧
    ∃ m n : E3,
      (inner ℝ m u = (0 : ℝ) ∧ inner ℝ m v = (1 : ℝ) ∧ inner ℝ m w = (0 : ℝ)) ∧
      (inner ℝ n u = (0 : ℝ) ∧ inner ℝ n v = (0 : ℝ) ∧ inner ℝ n w = (1 : ℝ)) ∧
      angle m n = π - sphericalAngle u v w := by
  have huu : inner ℝ u u = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  obtain ⟨p, hp⟩ : ∃ p : E3, p = v - (inner ℝ u v : ℝ) • u := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : E3, q = w - (inner ℝ u w : ℝ) • u := ⟨_, rfl⟩
  have hsa : sphericalAngle u v w = angle p q := by rw [sphericalAngle, hp, hq]
  have hv : v = p + (inner ℝ u v : ℝ) • u := by rw [hp]; abel
  have hw : w = q + (inner ℝ u w : ℝ) • u := by rw [hq]; abel
  have hpu : inner ℝ p u = (0 : ℝ) := by
    rw [hp, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
  have hqu : inner ℝ q u = (0 : ℝ) := by
    rw [hq, inner_sub_left, real_inner_smul_left, huu, real_inner_comm]; ring
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ, P = inner ℝ p p := ⟨_, rfl⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = inner ℝ q q := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = inner ℝ p q := ⟨_, rfl⟩
  have hpv : inner ℝ p v = P := by
    nth_rewrite 1 [hv]; rw [inner_add_right, real_inner_smul_right, hpu, hPdef]; ring
  have hpw : inner ℝ p w = R := by
    nth_rewrite 1 [hw]; rw [inner_add_right, real_inner_smul_right, hpu, hRdef]; ring
  have hqv : inner ℝ q v = R := by
    nth_rewrite 1 [hv]
    rw [inner_add_right, real_inner_smul_right, hqu, hRdef, real_inner_comm p q]; ring
  have hqw : inner ℝ q w = Q := by
    nth_rewrite 1 [hw]; rw [inner_add_right, real_inner_smul_right, hqu, hQdef]; ring
  have hnp : ‖p‖ ^ 2 = P := by rw [hPdef, real_inner_self_eq_norm_sq]
  have hnq : ‖q‖ ^ 2 = Q := by rw [hQdef, real_inner_self_eq_norm_sq]
  have hnotmul : ∀ r : ℝ, q ≠ r • p := by
    intro r hr
    have h2 : (r * (inner ℝ u v : ℝ) - (inner ℝ u w : ℝ)) • u + (-r) • v + (1 : ℝ) • w = 0 := by
      rw [show (r * (inner ℝ u v : ℝ) - (inner ℝ u w : ℝ)) • u + (-r) • v + (1 : ℝ) • w
        = (w - (inner ℝ u w : ℝ) • u) - r • (v - (inner ℝ u v : ℝ) • u) from by module,
        ← hp, ← hq, hr, sub_self]
    exact one_ne_zero (indep_coeffs hind h2).2.2
  have hPpos : 0 < P := by
    rw [hPdef, real_inner_self_pos]
    intro h0
    have h1 : v - (inner ℝ u v : ℝ) • u = 0 := by rw [← hp]; exact h0
    have h2 : (-(inner ℝ u v : ℝ)) • u + (1 : ℝ) • v + (0 : ℝ) • w = 0 := by
      rw [show (-(inner ℝ u v : ℝ)) • u + (1 : ℝ) • v + (0 : ℝ) • w
        = v - (inner ℝ u v : ℝ) • u from by module]
      exact h1
    exact one_ne_zero (indep_coeffs hind h2).2.1
  have hQpos : 0 < Q := by
    rw [hQdef, real_inner_self_pos]
    intro h0
    exact hnotmul 0 (by rw [h0, zero_smul])
  have hangle_pos : 0 < angle p q := by
    rcases eq_or_lt_of_le (angle_nonneg p q) with h | h
    · exact absurd (angle_eq_zero_iff.mp h.symm)
        (by rintro ⟨-, r, -, hr⟩; exact hnotmul r hr)
    · exact h
  have hangle_lt : angle p q < π := by
    rcases eq_or_lt_of_le (angle_le_pi p q) with h | h
    · exact absurd (angle_eq_pi_iff.mp h) (by rintro ⟨-, r, -, hr⟩; exact hnotmul r hr)
    · exact h
  have hm0sq : ‖Q • p - R • q‖ ^ 2 = Q * (P * Q - R ^ 2) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, mul_pow, sq_abs, sq_abs, hnp, hnq, ← hRdef]
    ring
  have hDpos : 0 < P * Q - R ^ 2 := by
    rcases lt_or_eq_of_le (by nlinarith [sq_nonneg ‖Q • p - R • q‖, norm_nonneg (Q • p - R • q)] :
        (0 : ℝ) ≤ P * Q - R ^ 2) with h | h
    · exact h
    · exfalso
      have hz : ‖Q • p - R • q‖ = 0 := by nlinarith [norm_nonneg (Q • p - R • q)]
      have hz2 : Q • p - R • q = 0 := norm_eq_zero.mp hz
      have h2 : (-(Q * (inner ℝ u v : ℝ)) + R * (inner ℝ u w : ℝ)) • u + Q • v + (-R) • w = 0 := by
        rw [← hz2, hp, hq]; module
      exact absurd (indep_coeffs hind h2).2.1 hQpos.ne'
  have hne : P * Q - R ^ 2 ≠ 0 := hDpos.ne'
  refine ⟨⟨hsa ▸ hangle_pos, hsa ▸ hangle_lt⟩,
    (P * Q - R ^ 2)⁻¹ • (Q • p - R • q), (P * Q - R ^ 2)⁻¹ • (P • q - R • p),
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · simp only [real_inner_smul_left, inner_sub_left, hpu, hqu]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpv, hqv]; field_simp
  · simp only [real_inner_smul_left, inner_sub_left, hpw, hqw]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpu, hqu]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpv, hqv]; ring
  · simp only [real_inner_smul_left, inner_sub_left, hpw, hqw]; field_simp
  rw [hsa]
  exact lune_angle_aux p q P Q R (P * Q - R ^ 2) hPdef hQdef hRdef hnp hnq hPpos hQpos rfl
    hDpos hm0sq

/-! ### Step 5: the eight sectors -/

/-- The sign of a boolean, as a real number. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

lemma sgn_pos_eq {a b : Bool} {r : ℝ} (ha : 0 < sgn a * r) (hb : 0 < sgn b * r) : a = b := by
  cases a <;> cases b <;> simp only [sgn] at ha hb <;> norm_num at ha hb ⊢ <;> linarith

lemma sgn_decide {r : ℝ} (hr : r ≠ 0) : 0 < sgn (decide (0 < r)) * r := by
  by_cases hp : 0 < r
  · rw [decide_eq_true hp]; simpa [sgn] using hp
  · have h : r < 0 := lt_of_le_of_ne (not_lt.1 hp) hr
    rw [decide_eq_false hp]
    have hs : sgn false = -1 := by simp [sgn]
    rw [hs]
    linarith

/-- A hyperplane through the origin is null. -/
lemma volume_hyperplane (c : E3) (hc : c ≠ 0) : volume {x : E3 | inner ℝ c x = (0 : ℝ)} = 0 := by
  have h : {x : E3 | inner ℝ c x = (0 : ℝ)}
      = (LinearMap.ker ((innerSL ℝ c : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) : Submodule ℝ E3) := by
    ext x; simp [LinearMap.mem_ker]
  rw [h]
  apply Measure.addHaar_submodule
  intro htop
  have hcc : ((innerSL ℝ c : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) c = 0 := by
    rw [← LinearMap.mem_ker, htop]; trivial
  exact hc (by simpa using hcc)

/-- The eight open sectors of the unit ball cut out by three linear functionals. -/
def osec (cu cv cw : E3) (s : Bool × Bool × Bool) : Set E3 :=
  {x | ‖x‖ ≤ 1 ∧ 0 < sgn s.1 * inner ℝ cu x ∧ 0 < sgn s.2.1 * inner ℝ cv x ∧
    0 < sgn s.2.2 * inner ℝ cw x}

lemma measurableSet_osec (cu cv cw : E3) (s : Bool × Bool × Bool) :
    MeasurableSet (osec cu cv cw s) := by
  have e : osec cu cv cw s = ({x : E3 | ‖x‖ ≤ 1} ∩ {x : E3 | 0 < sgn s.1 * inner ℝ cu x} ∩
      {x : E3 | 0 < sgn s.2.1 * inner ℝ cv x}) ∩ {x : E3 | 0 < sgn s.2.2 * inner ℝ cw x} := by
    ext x; simp only [osec, mem_setOf_eq, mem_inter_iff]; tauto
  rw [e]
  exact (((measurableSet_le (by fun_prop) measurable_const).inter
    (measurableSet_lt measurable_const (by fun_prop))).inter
    (measurableSet_lt measurable_const (by fun_prop))).inter
    (measurableSet_lt measurable_const (by fun_prop))

lemma osec_subset_ball (cu cv cw : E3) (s : Bool × Bool × Bool) :
    osec cu cv cw s ⊆ closedBall (0 : E3) 1 := by
  intro x hx
  simpa [mem_closedBall_zero_iff] using hx.1

lemma volume_osec_ne_top (cu cv cw : E3) (s : Bool × Bool × Bool) :
    volume (osec cu cv cw s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (osec_subset_ball cu cv cw s))
  rw [EuclideanSpace.volume_closedBall_fin_three]
  simp

lemma osec_disjoint (cu cv cw : E3) :
    Pairwise (Function.onFun Disjoint (osec cu cv cw)) := by
  rintro ⟨s1, s2, s3⟩ ⟨t1, t2, t3⟩ hst
  rw [Function.onFun, Set.disjoint_left]
  rintro x hxs hxt
  have e1 : s1 = t1 := sgn_pos_eq hxs.2.1 hxt.2.1
  have e2 : s2 = t2 := sgn_pos_eq hxs.2.2.1 hxt.2.2.1
  have e3 : s3 = t3 := sgn_pos_eq hxs.2.2.2 hxt.2.2.2
  exact hst (by rw [e1, e2, e3])

lemma osec_rot1 (cu cv cw : E3) (a b c : Bool) :
    osec cv cw cu (a, b, c) = osec cu cv cw (c, a, b) := by
  ext x; simp only [osec, mem_setOf_eq]; tauto

lemma osec_rot2 (cu cv cw : E3) (a b c : Bool) :
    osec cw cu cv (a, b, c) = osec cu cv cw (b, c, a) := by
  ext x; simp only [osec, mem_setOf_eq]; tauto

lemma volume_osec_neg (cu cv cw : E3) (s : Bool × Bool × Bool) :
    volume (osec cu cv cw (!s.1, !s.2.1, !s.2.2)) = volume (osec cu cv cw s) := by
  have hset : osec cu cv cw (!s.1, !s.2.1, !s.2.2) = (fun x : E3 => -x) ⁻¹' osec cu cv cw s := by
    ext x
    simp only [osec, mem_setOf_eq, mem_preimage, norm_neg, inner_neg_right, sgn_not]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨h1, by linarith, by linarith, by linarith⟩
  rw [hset, (Measure.measurePreserving_neg volume).measure_preimage
    (measurableSet_osec cu cv cw s).nullMeasurableSet]

/-- If `B ⊆ A ⊆ B ∪ N` with `N` null, then `A` and `B` have the same volume. -/
lemma volume_eq_of_sandwich {A B N : Set E3} (hN : volume N = 0) (h1 : B ⊆ A)
    (h2 : A ⊆ B ∪ N) : volume A = volume B := by
  refine le_antisymm ?_ (measure_mono h1)
  calc volume A ≤ volume (B ∪ N) := measure_mono h2
    _ ≤ volume B + volume N := measure_union_le _ _
    _ = volume B := by rw [hN, add_zero]

/-- The union of the three coordinate hyperplanes; a null set. -/
lemma volume_triple_hyperplane (cu cv cw : E3) (hcu : cu ≠ 0) (hcv : cv ≠ 0) (hcw : cw ≠ 0) :
    volume ({x : E3 | inner ℝ cu x = (0 : ℝ)} ∪ {x : E3 | inner ℝ cv x = (0 : ℝ)} ∪
      {x : E3 | inner ℝ cw x = (0 : ℝ)}) = 0 := by
  refine measure_union_null (measure_union_null ?_ ?_) ?_
  · exact volume_hyperplane cu hcu
  · exact volume_hyperplane cv hcv
  · exact volume_hyperplane cw hcw

lemma sum_volume_osec (cu cv cw : E3) (hcu : cu ≠ 0) (hcv : cv ≠ 0) (hcw : cw ≠ 0) :
    ∑ s : Bool × Bool × Bool, volume (osec cu cv cw s) = ENNReal.ofReal (π * 4 / 3) := by
  have hball : volume (⋃ s, osec cu cv cw s) = volume (closedBall (0 : E3) 1) := by
    refine (volume_eq_of_sandwich (volume_triple_hyperplane cu cv cw hcu hcv hcw) ?_ ?_).symm
    · exact iUnion_subset fun s => osec_subset_ball cu cv cw s
    · intro x hx
      rw [mem_closedBall_zero_iff] at hx
      by_cases h1 : inner ℝ cu x = (0 : ℝ)
      · exact Or.inr (Or.inl (Or.inl h1))
      by_cases h2 : inner ℝ cv x = (0 : ℝ)
      · exact Or.inr (Or.inl (Or.inr h2))
      by_cases h3 : inner ℝ cw x = (0 : ℝ)
      · exact Or.inr (Or.inr h3)
      exact Or.inl (mem_iUnion.2 ⟨(decide (0 < inner ℝ cu x), decide (0 < inner ℝ cv x),
        decide (0 < inner ℝ cw x)), hx, sgn_decide h1, sgn_decide h2, sgn_decide h3⟩)
  rw [measure_iUnion (osec_disjoint cu cv cw) (measurableSet_osec cu cv cw),
    tsum_fintype] at hball
  rw [hball, EuclideanSpace.volume_closedBall_fin_three]
  simp

/-- The lune obtained by dropping the first constraint splits into two sectors. -/
lemma volume_lune_eq (cu cv cw : E3) (hcu : cu ≠ 0) (hcv : cv ≠ 0) (hcw : cw ≠ 0) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ (inner ℝ cv x : ℝ) ∧ 0 ≤ (inner ℝ cw x : ℝ)}
      = volume (osec cu cv cw (true, true, true)) + volume (osec cu cv cw (false, true, true)) := by
  have hdisj : Disjoint (osec cu cv cw (true, true, true)) (osec cu cv cw (false, true, true)) :=
    osec_disjoint cu cv cw (by simp)
  rw [← measure_union hdisj (measurableSet_osec _ _ _ _)]
  refine volume_eq_of_sandwich (volume_triple_hyperplane cu cv cw hcu hcv hcw) ?_ ?_
  · rintro x (hx | hx) <;>
      exact ⟨hx.1, by simpa [sgn] using hx.2.2.1.le, by simpa [sgn] using hx.2.2.2.le⟩
  · rintro x ⟨hn, h2, h3⟩
    by_cases h1 : inner ℝ cu x = (0 : ℝ)
    · exact Or.inr (Or.inl (Or.inl h1))
    by_cases h2' : inner ℝ cv x = (0 : ℝ)
    · exact Or.inr (Or.inl (Or.inr h2'))
    by_cases h3' : inner ℝ cw x = (0 : ℝ)
    · exact Or.inr (Or.inr h3')
    have hp2 : 0 < (inner ℝ cv x : ℝ) := lt_of_le_of_ne h2 (Ne.symm h2')
    have hp3 : 0 < (inner ℝ cw x : ℝ) := lt_of_le_of_ne h3 (Ne.symm h3')
    rcases lt_or_gt_of_ne h1 with h | h
    · exact Or.inl (Or.inr ⟨hn, by simp [sgn]; linarith, by simpa [sgn] using hp2,
        by simpa [sgn] using hp3⟩)
    · exact Or.inl (Or.inl ⟨hn, by simpa [sgn] using h, by simpa [sgn] using hp2,
        by simpa [sgn] using hp3⟩)

end GaussBonnet

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

import Mathlib

/-!
# Spherical wedges

Supporting material for the Gauss-Bonnet theorem for spherical polygons.

## Overview

We prove Girard's theorem (the Gauss–Bonnet theorem for a geodesic triangle on the unit
sphere): the sum of the three interior angles of a spherical triangle equals `π` plus the
area of the triangle.

The area of a region `S` of the unit sphere in `ℝ³` is defined as three times the Lebesgue
volume of the cone over `S` with apex the origin (this is the standard normalisation:
the cone over the whole sphere is the unit ball, of volume `4π/3`, giving total area `4π`).

The proof is the classical "lune" argument.  The three great circles through the pairs of
vertices cut the sphere into eight triangles; each of the three lunes containing the
triangle `T` decomposes as `T` together with one of the neighbouring triangles.
-/

open MeasureTheory Metric Real Set InnerProductGeometry Pointwise

noncomputable section

namespace GaussBonnet

/-- Euclidean three-space, the ambient space for the unit sphere. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### Step 1: the area of a planar circular sector -/

/-- The planar sector of the closed unit disc cut out by the two half-planes
`0 ≤ x` and `0 ≤ x cos φ + y sin φ`.  For `0 < φ < π` this is a sector of angle `π - φ`. -/
def sector2 (φ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.1 ∧ 0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2}

lemma isClosed_sector2 (φ : ℝ) : IsClosed (sector2 φ) := by
  have h1 : IsClosed {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ 1} := isClosed_le (by fun_prop) (by fun_prop)
  have h2 : IsClosed {p : ℝ × ℝ | 0 ≤ p.1} := isClosed_le (by fun_prop) (by fun_prop)
  have h3 : IsClosed {p : ℝ × ℝ | 0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

lemma measurableSet_sector2 (φ : ℝ) : MeasurableSet (sector2 φ) :=
  (isClosed_sector2 φ).measurableSet

/-- The angular condition describing `sector2 φ` in polar coordinates. -/
lemma cos_cond (φ t : ℝ) (h0 : 0 < φ) (h1 : φ < π) (ht1 : -π < t) (ht2 : t < π) :
    (0 ≤ Real.cos t ∧ 0 ≤ Real.cos (t - φ)) ↔ (φ - π / 2 ≤ t ∧ t ≤ π / 2) := by
  constructor
  · rintro ⟨hc1, hc2⟩
    have hA : t ≤ π / 2 := by
      by_contra h
      push_neg at h
      have := Real.cos_neg_of_pi_div_two_lt_of_lt h (by linarith [Real.pi_pos])
      linarith
    have hB : -(π / 2) ≤ t := by
      by_contra h
      push_neg at h
      have : Real.cos (-t) < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [Real.pi_pos])
      rw [Real.cos_neg] at this; linarith
    refine ⟨?_, hA⟩
    by_contra h
    push_neg at h
    have : Real.cos (-(t - φ)) < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith)
    rw [Real.cos_neg] at this; linarith
  · rintro ⟨hA, hB⟩
    exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by linarith, hB⟩,
      Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩⟩

private lemma box_lint (a b : ℝ) :
    ∫⁻ p in (Ioc (0 : ℝ) 1) ×ˢ (Icc a b), ENNReal.ofReal p.1 = ENNReal.ofReal ((b - a) / 2) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc]
  rw [lintegral_mul_const _ (by fun_prop)]
  have h2 : ∫⁻ x in Ioc (0 : ℝ) 1, ENNReal.ofReal x = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [← intervalIntegral.integral_of_le (by norm_num)]
      simp
    · exact continuous_id.integrableOn_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using le_of_lt hx.1
  rw [h2, ← ENNReal.ofReal_mul (by norm_num)]
  rcases le_total a b with h | h
  · congr 1; ring
  · rw [ENNReal.ofReal_eq_zero.2 (by nlinarith), ENNReal.ofReal_eq_zero.2 (by linarith)]

/-- The area of the planar sector of angle `π - φ` in the unit disc is `(π - φ)/2`. -/
lemma volume_sector2 (φ : ℝ) (h0 : 0 < φ) (h1 : φ < π) :
    volume (sector2 φ) = ENNReal.ofReal ((π - φ) / 2) := by
  have hS := measurableSet_sector2 φ
  have key : volume (sector2 φ) =
      ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * (sector2 φ).indicator 1 (polarCoord.symm p) := by
    rw [← lintegral_indicator_one hS,
      ← lintegral_comp_polarCoord_symm (fun p => (sector2 φ).indicator 1 p)]
    simp [smul_eq_mul]
  set B : Set (ℝ × ℝ) := (Ioc (0 : ℝ) 1) ×ˢ (Icc (φ - π / 2) (π / 2)) with hB
  have hBmeas : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Icc
  have hBsub : B ⊆ polarCoord.target := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    simp only [mem_Icc] at ht
    exact ⟨hr.1, by constructor <;> [linarith [ht.1]; linarith [ht.2, Real.pi_pos]]⟩
  have hcongr : ∀ p ∈ polarCoord.target,
      ENNReal.ofReal p.1 * (sector2 φ).indicator 1 (polarCoord.symm p)
        = B.indicator (fun q : ℝ × ℝ => ENNReal.ofReal q.1) p := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    simp only [mem_Ioi] at hr
    simp only [mem_Ioo] at ht
    have hpyth := Real.sin_sq_add_cos_sq t
    have hmem : (polarCoord.symm (r, t)) ∈ sector2 φ ↔ (r, t) ∈ B := by
      simp only [polarCoord_symm_apply, sector2, mem_setOf_eq, hB, mem_prod, mem_Ioc, mem_Icc]
      have hcc := cos_cond φ t h0 h1 ht.1 ht.2
      have e : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by nlinarith
      constructor
      · rintro ⟨hn, hc1, hc2⟩
        rw [e] at hn
        have hr2 : r ≤ 1 := by nlinarith
        have hcos : 0 ≤ Real.cos t := by nlinarith
        have hcos2 : 0 ≤ Real.cos (t - φ) := by rw [Real.cos_sub]; nlinarith
        exact ⟨⟨hr, hr2⟩, hcc.1 ⟨hcos, hcos2⟩⟩
      · rintro ⟨⟨-, hr2⟩, hts⟩
        obtain ⟨hcos, hcos2⟩ := hcc.2 hts
        rw [Real.cos_sub] at hcos2
        exact ⟨by rw [e]; nlinarith, by nlinarith, by nlinarith⟩
    by_cases hin : (r, t) ∈ B
    · rw [indicator_of_mem (hmem.2 hin), indicator_of_mem hin]; simp
    · rw [indicator_of_notMem (fun h => hin (hmem.1 h)), indicator_of_notMem hin]; simp
  rw [key, setLIntegral_congr_fun polarCoord.open_target.measurableSet hcongr,
    lintegral_indicator hBmeas, Measure.restrict_restrict hBmeas,
    inter_eq_self_of_subset_left hBsub, box_lint]
  congr 1
  ring

lemma smul_sector2 (φ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    r • sector2 φ =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 ≤ r ^ 2 ∧ 0 ≤ p.1 ∧
        0 ≤ Real.cos φ * p.1 + Real.sin φ * p.2} := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · ext p
    simp only [zero_smul_set (⟨(0, 0), by simp [sector2]⟩ : (sector2 φ).Nonempty), mem_setOf_eq]
    constructor
    · rintro rfl; norm_num
    · rintro ⟨h1, h2, h3⟩
      have : p.1 = 0 ∧ p.2 = 0 := by constructor <;> nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      exact Prod.ext this.1 this.2
  · ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨h1, h2, h3⟩ := hq
      refine ⟨by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; nlinarith, ?_, ?_⟩
      · simp only [Prod.smul_fst, smul_eq_mul]; positivity
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨r⁻¹ • p, ⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        rw [mul_pow, mul_pow, ← mul_add]
        have h4 : (r⁻¹) ^ 2 * r ^ 2 = 1 := by field_simp
        nlinarith [sq_nonneg (r⁻¹), mul_le_mul_of_nonneg_left h1 (sq_nonneg r⁻¹)]
      · simp only [Prod.smul_fst, smul_eq_mul]; positivity
      · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        have h5 : Real.cos φ * (r⁻¹ * p.1) + Real.sin φ * (r⁻¹ * p.2)
            = r⁻¹ * (Real.cos φ * p.1 + Real.sin φ * p.2) := by ring
        rw [h5]; positivity
      · simp [smul_smul, mul_inv_cancel₀ hr'.ne']

/-! ### Step 2: the volume of a spherical wedge, in coordinates -/

/-- The wedge of the unit ball of `ℝ × (ℝ × ℝ)` cut out by the two half-spaces
`0 ≤ y` and `0 ≤ y cos φ + z sin φ`.  Its dihedral angle is `π - φ`. -/
def wedge3 (φ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {x | x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 ≤ 1 ∧ 0 ≤ x.2.1 ∧
    0 ≤ Real.cos φ * x.2.1 + Real.sin φ * x.2.2}

lemma isClosed_wedge3 (φ : ℝ) : IsClosed (wedge3 φ) := by
  have h1 : IsClosed {x : ℝ × (ℝ × ℝ) | x.1 ^ 2 + x.2.1 ^ 2 + x.2.2 ^ 2 ≤ 1} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have h2 : IsClosed {x : ℝ × (ℝ × ℝ) | 0 ≤ x.2.1} := isClosed_le (by fun_prop) (by fun_prop)
  have h3 : IsClosed {x : ℝ × (ℝ × ℝ) | 0 ≤ Real.cos φ * x.2.1 + Real.sin φ * x.2.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact h1.inter (h2.inter h3)

/-- The volume of the wedge of dihedral angle `π - φ` in the unit ball is `2(π - φ)/3`. -/
lemma volume_wedge3 (φ : ℝ) (h0 : 0 < φ) (h1 : φ < π) :
    volume (wedge3 φ) = ENNReal.ofReal (2 * (π - φ) / 3) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply (isClosed_wedge3 φ).measurableSet]
  have hslice : ∀ z : ℝ, volume (Prod.mk z ⁻¹' wedge3 φ)
      = ENNReal.ofReal (1 - z ^ 2) * ENNReal.ofReal ((π - φ) / 2) := by
    intro z
    rcases le_or_gt (z ^ 2) 1 with hz | hz
    · have hr : (0 : ℝ) ≤ √(1 - z ^ 2) := Real.sqrt_nonneg _
      have hr2 : (√(1 - z ^ 2)) ^ 2 = 1 - z ^ 2 := Real.sq_sqrt (by linarith)
      have hset : Prod.mk z ⁻¹' wedge3 φ = (√(1 - z ^ 2)) • sector2 φ := by
        rw [smul_sector2 φ hr, hr2]
        ext p
        simp only [wedge3, mem_preimage, mem_setOf_eq]
        constructor
        · rintro ⟨a, b, c⟩; exact ⟨by linarith, b, c⟩
        · rintro ⟨a, b, c⟩; exact ⟨by linarith, b, c⟩
      rw [hset, Measure.addHaar_smul, volume_sector2 φ h0 h1]
      congr 2
      have h6 : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
      rw [h6, hr2, abs_of_nonneg (by linarith)]
    · have h7 : Prod.mk z ⁻¹' wedge3 φ = ∅ := by
        ext p
        simp only [wedge3, mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨a, b, c⟩
        nlinarith [sq_nonneg p.1, sq_nonneg p.2]
      rw [h7, measure_empty, ENNReal.ofReal_eq_zero.2 (by linarith), zero_mul]
  simp_rw [hslice]
  rw [lintegral_mul_const _ (by fun_prop)]
  have hint : ∫⁻ z : ℝ, ENNReal.ofReal (1 - z ^ 2) = ENNReal.ofReal (4 / 3) := by
    have hsupp : (fun z : ℝ => ENNReal.ofReal (1 - z ^ 2))
        = (Icc (-1 : ℝ) 1).indicator (fun z => ENNReal.ofReal (1 - z ^ 2)) := by
      ext z
      by_cases hz : z ∈ Icc (-1 : ℝ) 1
      · simp [hz]
      · rw [indicator_of_notMem hz, ENNReal.ofReal_eq_zero]
        simp only [mem_Icc, not_and_or, not_le] at hz
        rcases hz with h | h <;> nlinarith
    rw [hsupp, lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
    · congr 1
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num),
        intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
          ((continuous_pow 2).intervalIntegrable _ _)]
      norm_num
    · exact (Continuous.integrableOn_Icc (by fun_prop))
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      simp only [mem_Icc, Pi.zero_apply] at hz ⊢; nlinarith [hz.1, hz.2]
  rw [hint, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1
  ring

/-! ### Step 3: the volume of an intersection of two half-spaces with the unit ball -/

/-- The measurable identification of `ℝ³` with `ℝ × (ℝ × ℝ)` used to apply `volume_wedge3`. -/
def coordEquiv : (Fin 3 → ℝ) → ℝ × (ℝ × ℝ) :=
  (Prod.map id (MeasurableEquiv.finTwoArrow)) ∘ (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 2)

lemma measurePreserving_coordEquiv :
    MeasurePreserving coordEquiv (volume : Measure (Fin 3 → ℝ)) volume := by
  have h1 := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
  have h2 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) → ℝ × ℝ))
      volume volume := by
    rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
  exact h2.comp h1

lemma coordEquiv_apply (f : Fin 3 → ℝ) : coordEquiv f = (f 2, (f 0, f 1)) := by
  simp only [coordEquiv, Function.comp_apply, MeasurableEquiv.piFinSuccAbove,
    MeasurableEquiv.finTwoArrow, Prod.map]
  simp [Fin.removeNth, Fin.succAbove]

/-- Any pair of orthonormal vectors in `E3` extends to an orthonormal basis. -/
lemma exists_onb (e1 e2 : E3) (h1 : ‖e1‖ = 1) (h2 : ‖e2‖ = 1) (h12 : inner ℝ e1 e2 = (0 : ℝ)) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ E3, B 0 = e1 ∧ B 1 = e2 := by
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have h21 : inner ℝ e2 e1 = (0 : ℝ) := by rw [real_inner_comm]; exact h12
  have hon : Orthonormal ℝ (({0, 1} : Set (Fin 3)).restrict ![e1, e2, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    simp only [Set.restrict_apply]
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp [h1, h2, h12, h21]
  obtain ⟨B, hB⟩ := hon.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨B, hB 0 (by simp), hB 1 (by simp)⟩

/-- An orthonormal frame adapted to a pair of vectors spanning a plane. -/
lemma exists_frame (a b : E3) (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : 0 < angle a b) (h1 : angle a b < π) :
    ∃ e1 e2 : E3, ‖e1‖ = 1 ∧ ‖e2‖ = 1 ∧ inner ℝ e1 e2 = (0 : ℝ) ∧
      a = ‖a‖ • e1 ∧
      b = (‖b‖ * Real.cos (angle a b)) • e1 + (‖b‖ * Real.sin (angle a b)) • e2 := by
  have hA : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hBn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hsinpos : 0 < Real.sin (angle a b) := Real.sin_pos_of_pos_of_lt_pi h0 h1
  obtain ⟨e1, he1⟩ : ∃ e1 : E3, e1 = ‖a‖⁻¹ • a := ⟨_, rfl⟩
  have hne1 : ‖e1‖ = 1 := by rw [he1, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hA.ne']
  have hadec : a = ‖a‖ • e1 := by rw [he1, smul_smul, mul_inv_cancel₀ hA.ne', one_smul]
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = inner ℝ e1 b := ⟨_, rfl⟩
  have hcval : c = ‖b‖ * Real.cos (angle a b) := by
    rw [hc, he1, real_inner_smul_left, cos_angle]; field_simp
  obtain ⟨b', hb'⟩ : ∃ b' : E3, b' = b - c • e1 := ⟨_, rfl⟩
  have hperp : inner ℝ e1 b' = (0 : ℝ) := by
    rw [hb', inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hne1, ← hc]; ring
  have hcb : inner ℝ b e1 = c := by rw [hc, real_inner_comm]
  have hnb' : ‖b'‖ = ‖b‖ * Real.sin (angle a b) := by
    have hsq : ‖b'‖ ^ 2 = (‖b‖ * Real.sin (angle a b)) ^ 2 := by
      rw [hb', norm_sub_sq_real, real_inner_smul_right, hcb, norm_smul, hne1]
      simp only [Real.norm_eq_abs, mul_one]
      rw [sq_abs, hcval]
      linear_combination (-(‖b‖ ^ 2)) * (Real.sin_sq_add_cos_sq (angle a b))
    nlinarith [norm_nonneg b', mul_pos hBn hsinpos]
  have hnb'pos : 0 < ‖b'‖ := by rw [hnb']; positivity
  obtain ⟨e2, he2⟩ : ∃ e2 : E3, e2 = ‖b'‖⁻¹ • b' := ⟨_, rfl⟩
  have hne2 : ‖e2‖ = 1 := by
    rw [he2, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnb'pos.ne']
  have h12 : inner ℝ e1 e2 = (0 : ℝ) := by rw [he2, real_inner_smul_right, hperp, mul_zero]
  refine ⟨e1, e2, hne1, hne2, h12, hadec, ?_⟩
  have hb'e2 : ‖b'‖ • e2 = b' := by
    rw [he2, smul_smul, mul_inv_cancel₀ hnb'pos.ne', one_smul]
  rw [← hcval, ← hnb', hb'e2, hb']
  abel

/-- **Volume of a spherical wedge.**  For two nonzero vectors `a`, `b` of `ℝ³` spanning a plane,
the part of the unit ball on the positive side of both `a` and `b` has volume
`2(π - angle a b)/3`; equivalently the corresponding lune on the unit sphere has area
`2(π - angle a b)`. -/
lemma volume_halfspaces (a b : E3) (ha : a ≠ 0) (hb : b ≠ 0)
    (h0 : 0 < angle a b) (h1 : angle a b < π) :
    volume {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ inner ℝ a x ∧ 0 ≤ inner ℝ b x}
      = ENNReal.ofReal (2 * (π - angle a b) / 3) := by
  obtain ⟨e1, e2, hne1, hne2, h12, hadec, hbdec⟩ := exists_frame a b ha hb h0 h1
  obtain ⟨B, hB0, hB1⟩ := exists_onb e1 e2 hne1 hne2 h12
  have hA : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hBn : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hFmp : MeasurePreserving (fun x : E3 => coordEquiv (WithLp.ofLp (B.repr x)))
      volume volume :=
    measurePreserving_coordEquiv.comp
      ((PiLp.volume_preserving_ofLp (Fin 3)).comp B.measurePreserving_repr)
  have hset : {x : E3 | ‖x‖ ≤ 1 ∧ 0 ≤ inner ℝ a x ∧ 0 ≤ inner ℝ b x}
      = (fun x : E3 => coordEquiv (WithLp.ofLp (B.repr x))) ⁻¹' wedge3 (angle a b) := by
    ext x
    have hxi : ∀ i, (WithLp.ofLp (B.repr x)) i = inner ℝ (B i) x := fun i =>
      B.repr_apply_apply x i
    have hnorm : ‖x‖ = √ ((inner ℝ (B 0) x) ^ 2 + (inner ℝ (B 1) x) ^ 2
        + (inner ℝ (B 2) x) ^ 2) := by
      rw [← B.repr.norm_map x, EuclideanSpace.norm_eq]
      congr 1
      rw [Fin.sum_univ_three]
      simp [hxi, Real.norm_eq_abs, sq_abs]
    have hax : inner ℝ a x = ‖a‖ * inner ℝ (B 0) x := by
      rw [hB0]; nth_rewrite 1 [hadec]; rw [real_inner_smul_left]
    have hbx : inner ℝ b x = ‖b‖ * (Real.cos (angle a b) * inner ℝ (B 0) x
        + Real.sin (angle a b) * inner ℝ (B 1) x) := by
      rw [hB0, hB1]; nth_rewrite 1 [hbdec]
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]; ring
    simp only [mem_setOf_eq, mem_preimage, wedge3, coordEquiv_apply, hxi]
    rw [hnorm, hax, hbx, Real.sqrt_le_one]
    constructor
    · rintro ⟨hn, hp, hq⟩
      exact ⟨by linarith, by nlinarith, by nlinarith⟩
    · rintro ⟨hn, hp, hq⟩
      exact ⟨by linarith, by nlinarith, by nlinarith⟩
  rw [hset, hFmp.measure_preimage (isClosed_wedge3 _).measurableSet.nullMeasurableSet,
    volume_wedge3 _ h0 h1]

end GaussBonnet

