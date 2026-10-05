import Mathlib

/-!
# Additive monotone functions on an interval are linear

An elementary Cauchy-functional-equation argument: a nonnegative function on `[0, π]` which is
additive there is determined by its value at `π`.
-/

open scoped Real

namespace Math

variable {W : ℝ → ℝ}

/-- An additive nonnegative function is monotone. -/
lemma additive_mono (hnn : ∀ θ, 0 ≤ W θ) (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ π) : W x ≤ W y := by
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_refl _
  rcases eq_or_lt_of_le hx with rfl | hx'
  · rw [hzero]; exact hnn y
  · have h := hadd x (y - x) hx' (by linarith) (by linarith)
    rw [show x + (y - x) = y by ring] at h
    rw [h]
    linarith [hnn (y - x)]

/-- Additivity for natural multiples. -/
lemma additive_nsmul (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y) :
    ∀ (n : ℕ) (x : ℝ), 0 < x → (n : ℝ) * x ≤ π → W ((n : ℝ) * x) = n * W x := by
  intro n
  induction n with
  | zero => intro x _ _; simpa using hzero
  | succ n ih =>
    intro x hx hle
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnx : (0 : ℝ) < (n : ℝ) * x := by positivity
      have hcast : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by push_cast; ring
      rw [hcast] at hle ⊢
      rw [hadd ((n : ℝ) * x) x hnx hx hle, ih x hx (by linarith)]
      push_cast
      ring

/-- A nonnegative additive function on `[0, π]` with `W π = 2π/3` is `θ ↦ 2θ/3`. -/
theorem additive_linear (hnn : ∀ θ, 0 ≤ W θ) (hzero : W 0 = 0)
    (hadd : ∀ x y : ℝ, 0 < x → 0 < y → x + y ≤ π → W (x + y) = W x + W y)
    (hpi : W π = 2 * π / 3) {θ : ℝ} (h0 : 0 ≤ θ) (hp : θ ≤ π) :
    W θ = 2 * θ / 3 := by
  rcases eq_or_lt_of_le hp with rfl | hlt
  · exact hpi
  -- the value at `π / n`
  have hdiv : ∀ n : ℕ, 0 < n → W (π / n) = 2 * π / 3 / n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hx : 0 < π / n := by positivity
    have hkey := additive_nsmul hzero hadd n (π / n) hx (le_of_eq (by field_simp))
    rw [show (n : ℝ) * (π / n) = π by field_simp] at hkey
    rw [hpi] at hkey
    exact (eq_div_iff (ne_of_gt hnpos)).2 (by rw [mul_comm]; linarith)
  -- the squeeze
  have hbound : ∀ n : ℕ, 0 < n → |W θ - 2 * θ / 3| ≤ 2 * π / 3 / n := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    set m : ℕ := ⌊θ * n / π⌋₊ with hm
    have hzpos : 0 ≤ θ * n / π := by positivity
    have hmle : (m : ℝ) ≤ θ * n / π := Nat.floor_le hzpos
    have hmlt : θ * n / π < m + 1 := Nat.lt_floor_add_one _
    have hmn : (m : ℝ) < n := by
      have : θ * n / π < n := by
        rw [div_lt_iff₀ Real.pi_pos]
        nlinarith [Real.pi_pos]
      linarith
    have hm1n : (m : ℝ) + 1 ≤ n := by
      have : m < n := by exact_mod_cast hmn
      have : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
      exact this
    -- the two comparison points
    have hlow : (m : ℝ) * (π / n) ≤ θ := by
      have := mul_le_mul_of_nonneg_right hmle (le_of_lt (by positivity : (0:ℝ) < π / n))
      calc (m : ℝ) * (π / n) ≤ (θ * n / π) * (π / n) := this
        _ = θ := by field_simp
    have hhigh : θ ≤ ((m : ℝ) + 1) * (π / n) := by
      have := mul_le_mul_of_nonneg_right hmlt.le (le_of_lt (by positivity : (0:ℝ) < π / n))
      calc θ = (θ * n / π) * (π / n) := by field_simp
        _ ≤ ((m : ℝ) + 1) * (π / n) := this
    have hWlow : W ((m : ℝ) * (π / n)) = (m : ℝ) * (2 * π / 3 / n) := by
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · simp [hm0, hzero]
      · have := additive_nsmul hzero hadd m (π / n) (by positivity) (by
          rw [show (m : ℝ) * (π / n) = (m : ℝ) / n * π by ring]
          nlinarith [Real.pi_pos, (div_le_one hnpos).2 hmn.le])
        rw [this, hdiv n hn]
    have hWhigh : W (((m : ℝ) + 1) * (π / n)) = ((m : ℝ) + 1) * (2 * π / 3 / n) := by
      have hcast : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      have := additive_nsmul hzero hadd (m + 1) (π / n) (by positivity) (by
        rw [show ((m + 1 : ℕ) : ℝ) * (π / n) = ((m + 1 : ℕ) : ℝ) / n * π by ring]
        have : ((m + 1 : ℕ) : ℝ) / n ≤ 1 := by
          rw [div_le_one hnpos]
          push_cast
          exact hm1n
        nlinarith [Real.pi_pos])
      rw [this, hdiv n hn]
    have h1 : W ((m : ℝ) * (π / n)) ≤ W θ :=
      additive_mono hnn hzero hadd (by positivity) hlow hp
    have h2 : W θ ≤ W (((m : ℝ) + 1) * (π / n)) := by
      refine additive_mono hnn hzero hadd h0 hhigh ?_
      rw [show ((m : ℝ) + 1) * (π / n) = (((m : ℝ) + 1) / n) * π by ring]
      have : ((m : ℝ) + 1) / n ≤ 1 := (div_le_one hnpos).2 hm1n
      nlinarith [Real.pi_pos]
    rw [hWlow] at h1
    rw [hWhigh] at h2
    have hθlow : (m : ℝ) * (2 * π / 3 / n) ≤ 2 * θ / 3 := by
      have he : (m : ℝ) * (2 * π / 3 / n) = 2 / 3 * ((m : ℝ) * (π / n)) := by ring
      rw [he]
      linarith
    have hθhigh : 2 * θ / 3 ≤ ((m : ℝ) + 1) * (2 * π / 3 / n) := by
      have he : ((m : ℝ) + 1) * (2 * π / 3 / n) = 2 / 3 * (((m : ℝ) + 1) * (π / n)) := by ring
      rw [he]
      linarith
    have hexp : ((m : ℝ) + 1) * (2 * π / 3 / n) = (m : ℝ) * (2 * π / 3 / n) + 2 * π / 3 / n := by
      ring
    rw [abs_le]
    rw [hexp] at h2 hθhigh
    constructor <;> linarith
  by_contra hne
  have hd : 0 < |W θ - 2 * θ / 3| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 * π / 3) / |W θ - 2 * θ / 3|)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  have hn' : 0 < n := by exact_mod_cast hnpos
  have := hbound n hn'
  rw [div_lt_iff₀ hd] at hn
  rw [le_div_iff₀ hnpos] at this
  linarith

end Math

import Mathlib

/-!
# Basic measure-theoretic tools for solid angles in Euclidean 3-space
-/

open MeasureTheory Metric InnerProductGeometry
open scoped RealInnerProductSpace

noncomputable section

namespace Math

/-- Euclidean three-space. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

lemma finrank_E3 : Module.finrank ℝ E3 = 3 := by simp

/-- The closed half-space of vectors making a non-obtuse angle with the inner normal `n`. -/
def HS (n : E3) : Set E3 := {x : E3 | 0 ≤ ⟪x, n⟫}

lemma mem_HS {n x : E3} : x ∈ HS n ↔ 0 ≤ ⟪x, n⟫ := Iff.rfl

lemma isClosed_HS (n : E3) : IsClosed (HS n) := by
  exact isClosed_le continuous_const (continuous_id.inner continuous_const)

lemma measurableSet_HS (n : E3) : MeasurableSet (HS n) := (isClosed_HS n).measurableSet

/-- A hyperplane through the origin is Lebesgue-null. -/
lemma hyperplane_null {n : E3} (hn : n ≠ 0) : volume {x : E3 | ⟪x, n⟫ = 0} = 0 := by
  have hker : {x : E3 | ⟪x, n⟫ = 0} = ↑(LinearMap.ker ((innerSL ℝ n).toLinearMap)) := by
    ext x
    simp [LinearMap.mem_ker, real_inner_comm x n]
  rw [hker]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have : n ∈ LinearMap.ker ((innerSL ℝ n).toLinearMap) := by rw [htop]; trivial
  simp only [LinearMap.mem_ker] at this
  exact hn (by simpa using this)

/-- The (real-valued) volume of the part of the closed unit ball lying in `S`. -/
def bvol (S : Set E3) : ℝ := (volume (closedBall (0 : E3) 1 ∩ S)).toReal

lemma volume_ball_inter_ne_top (S : Set E3) :
    volume (closedBall (0 : E3) 1 ∩ S) ≠ ⊤ :=
  ((measure_mono Set.inter_subset_left).trans_lt
    (isCompact_closedBall _ _).measure_lt_top).ne

lemma bvol_nonneg (S : Set E3) : 0 ≤ bvol S := ENNReal.toReal_nonneg

lemma volume_closedBall_one : volume (closedBall (0 : E3) 1) = ENNReal.ofReal (4 / 3 * Real.pi) := by
  rw [EuclideanSpace.volume_closedBall]
  have h1 : Real.Gamma (5 / 2) = 3 / 4 * Real.sqrt Real.pi := by
    have h : (5 : ℝ) / 2 = 3 / 2 + 1 := by norm_num
    rw [h, Real.Gamma_add_one (by norm_num)]
    have h' : (3 : ℝ) / 2 = 1 / 2 + 1 := by norm_num
    rw [h', Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
    ring
  have hs : Real.sqrt Real.pi > 0 := Real.sqrt_pos.2 Real.pi_pos
  have h2 : Real.sqrt Real.pi ^ (3 : ℕ) / Real.Gamma (5 / 2) = 4 / 3 * Real.pi := by
    rw [h1, show Real.sqrt Real.pi ^ (3 : ℕ) = Real.pi * Real.sqrt Real.pi by
      rw [pow_succ, Real.sq_sqrt Real.pi_nonneg]]
    field_simp
  norm_num [h2]

lemma bvol_univ : bvol Set.univ = 4 / 3 * Real.pi := by
  rw [bvol, Set.inter_univ, volume_closedBall_one,
    ENNReal.toReal_ofReal (by positivity)]

/-- Splitting the ball along a hyperplane. -/
lemma bvol_split (S : Set E3) (hS : MeasurableSet S) {n : E3} (hn : n ≠ 0) :
    bvol S = bvol (S ∩ HS n) + bvol (S ∩ HS (-n)) := by
  set B := closedBall (0 : E3) 1 with hB
  have hmeas : MeasurableSet (B ∩ S ∩ HS (-n)) :=
    ((measurableSet_closedBall.inter hS).inter (measurableSet_HS _))
  have hunion : (B ∩ S ∩ HS n) ∪ (B ∩ S ∩ HS (-n)) = B ∩ S := by
    ext x
    simp only [Set.mem_union, Set.mem_inter_iff, mem_HS, inner_neg_right]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      rcases le_total 0 ⟪x, n⟫ with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, by linarith⟩
  have hinter : volume ((B ∩ S ∩ HS n) ∩ (B ∩ S ∩ HS (-n))) = 0 := by
    refine measure_mono_null ?_ (hyperplane_null hn)
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    simp only [mem_HS, inner_neg_right] at h1 h2
    exact le_antisymm (by linarith) h1
  have key := measure_union_add_inter (μ := volume) (B ∩ S ∩ HS n) hmeas
  rw [hunion, hinter, add_zero] at key
  have h1 := volume_ball_inter_ne_top (S ∩ HS n)
  have h2 := volume_ball_inter_ne_top (S ∩ HS (-n))
  simp only [bvol, ← Set.inter_assoc]
  rw [← ENNReal.toReal_add (by rw [Set.inter_assoc]; exact h1) (by rw [Set.inter_assoc]; exact h2),
    key]

lemma neg_HS (n : E3) : -(HS n) = HS (-n) := by
  ext x
  simp [HS]

lemma bvol_neg (S : Set E3) : bvol (-S) = bvol S := by
  have hb : closedBall (0 : E3) 1 ∩ (-S) = -(closedBall (0 : E3) 1 ∩ S) := by
    ext x
    simp
  rw [bvol, bvol, hb, Measure.measure_neg]

/-- Volume is invariant under linear isometries. -/
lemma bvol_image (L : E3 ≃ₗᵢ[ℝ] E3) (S : Set E3) : bvol (L '' S) = bvol S := by
  have himg : closedBall (0 : E3) 1 ∩ (L '' S) = L.symm ⁻¹' (closedBall (0 : E3) 1 ∩ S) := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, mem_closedBall_zero_iff]
    constructor
    · rintro ⟨hx, y, hy, rfl⟩
      simp only [LinearIsometryEquiv.symm_apply_apply]
      exact ⟨by simpa using hx, hy⟩
    · rintro ⟨hx1, hx2⟩
      refine ⟨by simpa using hx1, L.symm x, hx2, by simp⟩
  rw [bvol, bvol, himg]
  congr 1
  exact (L.symm.measurePreserving).measure_preimage_emb
    (L.symm.toMeasurableEquiv.measurableEmbedding) _

/-- An orthonormal pair in `E3` extends to an orthonormal basis. -/
lemma exists_onb_pair (e f : E3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e ∧ b 1 = f := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have horth : Orthonormal ℝ (Set.restrict ({0, 1} : Set (Fin 3)) ![e, f, 0]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.restrict, he, hf, hef, hfe, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp)⟩

/-- An orthonormal triple in `E3` is an orthonormal basis. -/
lemma exists_onb_triple (e f g : E3) (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hg : ‖g‖ = 1)
    (hef : ⟪e, f⟫ = 0) (heg : ⟪e, g⟫ = 0) (hfg : ⟪f, g⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = e ∧ b 1 = f ∧ b 2 = g := by
  have hfe : ⟪f, e⟫ = 0 := by rw [real_inner_comm]; exact hef
  have hge : ⟪g, e⟫ = 0 := by rw [real_inner_comm]; exact heg
  have hgf : ⟪g, f⟫ = 0 := by rw [real_inner_comm]; exact hfg
  have hcard : Module.finrank ℝ E3 = Fintype.card (Fin 3) := by simp
  have horth : Orthonormal ℝ (Set.restrict (Set.univ : Set (Fin 3)) ![e, f, g]) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp [Set.restrict, he, hf, hg, hef, heg, hfg, hfe, hge, hgf, Subtype.ext_iff]
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq hcard horth
  exact ⟨b, by simpa using hb 0 (by simp), by simpa using hb 1 (by simp),
    by simpa using hb 2 (by simp)⟩

/-- Any orthonormal pair can be mapped to any other by a linear isometry of `E3`. -/
lemma exists_isometry_pair {e f e' f' : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (he' : ‖e'‖ = 1) (hf' : ‖f'‖ = 1) (he'f' : ⟪e', f'⟫ = 0) :
    ∃ L : E3 ≃ₗᵢ[ℝ] E3, L e = e' ∧ L f = f' := by
  obtain ⟨b, hb0, hb1⟩ := exists_onb_pair e f he hf hef
  obtain ⟨b', hb'0, hb'1⟩ := exists_onb_pair e' f' he' hf' he'f'
  refine ⟨b.repr.trans b'.repr.symm, ?_, ?_⟩
  · rw [← hb0, ← hb'0]; simp
  · rw [← hb1, ← hb'1]; simp

lemma bvol_mono {A B : Set E3} (h : A ⊆ B) : bvol A ≤ bvol B :=
  ENNReal.toReal_le_toReal (volume_ball_inter_ne_top A) (volume_ball_inter_ne_top B) |>.2
    (measure_mono (Set.inter_subset_inter_right _ h))

lemma bvol_eq_zero_of_null {A : Set E3} (h : volume A = 0) : bvol A = 0 := by
  rw [bvol, measure_mono_null Set.inter_subset_right h, ENNReal.toReal_zero]

/-- Splitting off a null intersection. -/
lemma bvol_union (A B : Set E3) (hB : MeasurableSet B) (hnull : volume (A ∩ B) = 0) :
    bvol (A ∪ B) = bvol A + bvol B := by
  set C := closedBall (0 : E3) 1 with hC
  have h1 : C ∩ (A ∪ B) = (C ∩ A) ∪ (C ∩ B) := by
    rw [Set.inter_union_distrib_left]
  have h2 : volume ((C ∩ A) ∩ (C ∩ B)) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro x ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact ⟨h1, h2⟩
  have key := measure_union_add_inter (μ := volume) (s := C ∩ A) (t := C ∩ B)
    (measurableSet_closedBall.inter hB)
  rw [← h1, h2, add_zero] at key
  rw [bvol, bvol, bvol, ← ENNReal.toReal_add (volume_ball_inter_ne_top A)
    (volume_ball_inter_ne_top B), key]

lemma image_HS (L : E3 ≃ₗᵢ[ℝ] E3) (n : E3) : L '' (HS n) = HS (L n) := by
  ext x
  simp only [Set.mem_image, mem_HS]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [L.inner_map_map]
  · intro hx
    refine ⟨L.symm x, ?_, by simp⟩
    have : ⟪L (L.symm x), L n⟫ = ⟪L.symm x, n⟫ := L.inner_map_map _ _
    rw [L.apply_symm_apply] at this
    rw [← this]; exact hx

end Math

import RequestProject.Basic
import RequestProject.Cauchy

/-!
# The volume of a solid wedge of the unit ball

For two unit vectors `u`, `v` the set of points of the closed unit ball lying in both half-spaces
`⟪x, u⟫ ≥ 0` and `⟪x, v⟫ ≥ 0` is a wedge of dihedral angle `π - angle u v`; its volume is
`2/3 * (π - angle u v)`.
-/

open MeasureTheory Metric InnerProductGeometry
open scoped RealInnerProductSpace Real

noncomputable section

namespace Math

/-- The unit vector at angle `φ` in the plane spanned by the orthonormal pair `(e, f)`. -/
def dirv (e f : E3) (φ : ℝ) : E3 := Real.cos φ • e + Real.sin φ • f

/-- The volume of the part of the unit ball lying in the two half-spaces with inner normals
`u` and `v`. -/
def wvol (u v : E3) : ℝ := bvol (HS u ∩ HS v)

lemma wvol_comm (u v : E3) : wvol u v = wvol v u := by
  rw [wvol, wvol, Set.inter_comm]

section Orthonormal

variable {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
include he hf hef

lemma inner_dirv_dirv (α β : ℝ) : ⟪dirv e f α, dirv e f β⟫ = Real.cos (α - β) := by
  have hfe : ⟪f, e⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hef
  have hee : ⟪e, e⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hff : ⟪f, f⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hf]; norm_num
  simp only [dirv, inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hef, hfe, hee, hff, Real.cos_sub]
  ring

lemma norm_dirv (φ : ℝ) : ‖dirv e f φ‖ = 1 := by
  have h := inner_dirv_dirv he hf hef φ φ
  rw [real_inner_self_eq_norm_sq] at h
  simp only [sub_self, Real.cos_zero] at h
  nlinarith [norm_nonneg (dirv e f φ)]

lemma dirv_ne_zero (φ : ℝ) : dirv e f φ ≠ 0 := by
  intro h
  have := norm_dirv he hf hef φ
  rw [h] at this
  simp at this

end Orthonormal

/-- The rotated pair generates the same rotating family. -/
lemma dirv_shift (e f : E3) (s φ : ℝ) :
    dirv (dirv e f s) (dirv e f (s + π / 2)) φ = dirv e f (s + φ) := by
  simp only [dirv, Real.cos_add, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
  module

lemma inner_dirv_shift_pair {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (s : ℝ) :
    ⟪dirv e f s, dirv e f (s + π / 2)⟫ = 0 := by
  rw [inner_dirv_dirv he hf hef]
  simp [Real.cos_pi_div_two]

/-- The three-term positive combination identity for coplanar unit vectors. -/
lemma dirv_comb (e f : E3) (a b c : ℝ) :
    Real.sin (b - a) • dirv e f c
      = Real.sin (b - c) • dirv e f a + Real.sin (c - a) • dirv e f b := by
  simp only [dirv, Real.sin_sub, smul_add, smul_smul]
  rw [show (Real.sin b * Real.cos a - Real.cos b * Real.sin a) * Real.cos c
      = (Real.sin b * Real.cos c - Real.cos b * Real.sin c) * Real.cos a
        + (Real.sin c * Real.cos a - Real.cos c * Real.sin a) * Real.cos b by ring,
    show (Real.sin b * Real.cos a - Real.cos b * Real.sin a) * Real.sin c
      = (Real.sin b * Real.cos c - Real.cos b * Real.sin c) * Real.sin a
        + (Real.sin c * Real.cos a - Real.cos c * Real.sin a) * Real.sin b by ring]
  module

/-- If `x` is on the positive side of the half-spaces at angles `a` and `b`, it is on the
positive side of every intermediate one. -/
lemma HS_dirv_between {e f : E3} {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) (hab : b - a < π) :
    HS (dirv e f a) ∩ HS (dirv e f b) ⊆ HS (dirv e f c) := by
  rintro x ⟨hxa, hxb⟩
  simp only [mem_HS] at hxa hxb ⊢
  rcases eq_or_lt_of_le (hac.trans hcb) with hab' | hab'
  · -- degenerate: a = b, hence a = c = b
    have h1 : c = a := by linarith
    rw [h1]; exact hxa
  · have hsba : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) hab
    have hsbc : 0 ≤ Real.sin (b - c) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hsca : 0 ≤ Real.sin (c - a) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hid := dirv_comb e f a b c
    have : Real.sin (b - a) * ⟪x, dirv e f c⟫
        = Real.sin (b - c) * ⟪x, dirv e f a⟫ + Real.sin (c - a) * ⟪x, dirv e f b⟫ := by
      have := congrArg (fun y => ⟪x, y⟫) hid
      simpa [inner_add_right, real_inner_smul_right] using this
    nlinarith

lemma dirv_add_pi (e f : E3) (φ : ℝ) : dirv e f (φ + π) = -dirv e f φ := by
  simp only [dirv, Real.cos_add_pi, Real.sin_add_pi]
  module

/-! ### The standard wedge function -/

/-- The first standard basis vector of `E3`. -/
def e₀ : E3 := EuclideanSpace.single 0 1

/-- The second standard basis vector of `E3`. -/
def f₀ : E3 := EuclideanSpace.single 1 1

lemma norm_e₀ : ‖e₀‖ = 1 := by simp [e₀]

lemma norm_f₀ : ‖f₀‖ = 1 := by simp [f₀]

lemma inner_e₀_f₀ : ⟪e₀, f₀⟫ = 0 := by
  simp [e₀, f₀, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- `Wfun θ` is the volume of the wedge of the unit ball of dihedral angle `θ`. -/
def Wfun (θ : ℝ) : ℝ := wvol (dirv e₀ f₀ (π / 2)) (dirv e₀ f₀ (θ - π / 2))

lemma Wfun_nonneg (θ : ℝ) : 0 ≤ Wfun θ := bvol_nonneg _

/-- The wedge volume only depends on the two angles, not on the orthonormal frame. -/
lemma wvol_dirv_congr {e f e' f' : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    (he' : ‖e'‖ = 1) (hf' : ‖f'‖ = 1) (he'f' : ⟪e', f'⟫ = 0) (α β : ℝ) :
    wvol (dirv e f α) (dirv e f β) = wvol (dirv e' f' α) (dirv e' f' β) := by
  obtain ⟨L, hLe, hLf⟩ := exists_isometry_pair he hf hef he' hf' he'f'
  have hL : ∀ φ : ℝ, L (dirv e f φ) = dirv e' f' φ := by
    intro φ
    simp [dirv, hLe, hLf]
  rw [wvol, wvol, ← hL α, ← hL β, ← image_HS, ← image_HS, ← Set.image_inter L.injective,
    bvol_image]

/-- Every wedge cut out by two half-spaces in a common rotating family has the standard volume. -/
lemma wvol_dirv_eq_Wfun {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0) (s t : ℝ) :
    wvol (dirv e f (s + π / 2)) (dirv e f (t - π / 2)) = Wfun (t - s) := by
  have h1 : ‖dirv e f s‖ = 1 := norm_dirv he hf hef s
  have h2 : ‖dirv e f (s + π / 2)‖ = 1 := norm_dirv he hf hef _
  have h3 : ⟪dirv e f s, dirv e f (s + π / 2)⟫ = 0 := inner_dirv_shift_pair he hf hef s
  have k1 : dirv e f (s + π / 2) = dirv (dirv e f s) (dirv e f (s + π / 2)) (π / 2) := by
    rw [dirv_shift]
  have k2 : dirv e f (t - π / 2)
      = dirv (dirv e f s) (dirv e f (s + π / 2)) ((t - s) - π / 2) := by
    rw [dirv_shift]
    ring_nf
  rw [k1, k2, wvol_dirv_congr h1 h2 h3 norm_e₀ norm_f₀ inner_e₀_f₀]
  rfl

/-- Half of the unit ball. -/
lemma bvol_HS {n : E3} (hn : n ≠ 0) : bvol (HS n) = 2 * π / 3 := by
  have h := bvol_split Set.univ MeasurableSet.univ hn
  rw [bvol_univ, Set.univ_inter, Set.univ_inter, ← neg_HS, bvol_neg] at h
  linarith

lemma Wfun_pi : Wfun π = 2 * π / 3 := by
  have h : π - π / 2 = π / 2 := by ring
  rw [Wfun, h, wvol, Set.inter_self]
  exact bvol_HS (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ _)

lemma Wfun_zero : Wfun 0 = 0 := by
  set g := dirv e₀ f₀ (π / 2) with hg
  have hneg : dirv e₀ f₀ (0 - π / 2) = -g := by
    have hd := dirv_add_pi e₀ f₀ (0 - π / 2)
    rw [show (0 : ℝ) - π / 2 + π = π / 2 by ring] at hd
    rw [hg, hd, neg_neg]
  rw [Wfun, wvol, hneg]
  refine bvol_eq_zero_of_null (measure_mono_null ?_
    (hyperplane_null (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ (π / 2))))
  rintro x ⟨h1, h2⟩
  simp only [mem_HS, inner_neg_right] at h1 h2
  exact le_antisymm (by linarith) h1

lemma Wfun_add {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (h : θ₁ + θ₂ ≤ π) :
    Wfun (θ₁ + θ₂) = Wfun θ₁ + Wfun θ₂ := by
  set A := HS (dirv e₀ f₀ (0 + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ - π / 2)) with hA
  set B := HS (dirv e₀ f₀ (θ₁ + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ + θ₂ - π / 2)) with hB
  set C := HS (dirv e₀ f₀ (0 + π / 2)) ∩ HS (dirv e₀ f₀ (θ₁ + θ₂ - π / 2)) with hC
  have hAC : A ⊆ C := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨hx1, ?_⟩
    have := HS_dirv_between (e := e₀) (f := f₀) (a := θ₁ - π / 2) (b := 0 + π / 2)
      (c := θ₁ + θ₂ - π / 2) (by linarith) (by linarith) (by linarith)
    exact this ⟨hx2, hx1⟩
  have hBC : B ⊆ C := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    have := HS_dirv_between (e := e₀) (f := f₀) (a := θ₁ + θ₂ - π / 2) (b := θ₁ + π / 2)
      (c := 0 + π / 2) (by linarith) (by linarith) (by linarith)
    exact this ⟨hx2, hx1⟩
  have hflip : dirv e₀ f₀ (θ₁ + π / 2) = -dirv e₀ f₀ (θ₁ - π / 2) := by
    rw [← dirv_add_pi]
    ring_nf
  have hunion : A ∪ B = C := by
    refine Set.Subset.antisymm (Set.union_subset hAC hBC) ?_
    rintro x ⟨hx1, hx2⟩
    rcases le_or_gt 0 (⟪x, dirv e₀ f₀ (θ₁ - π / 2)⟫ : ℝ) with hpos | hneg
    · exact Or.inl ⟨hx1, hpos⟩
    · refine Or.inr ⟨?_, hx2⟩
      simp only [mem_HS, hflip, inner_neg_right]
      linarith
  have hnull : volume (A ∩ B) = 0 := by
    refine measure_mono_null ?_
      (hyperplane_null (dirv_ne_zero norm_e₀ norm_f₀ inner_e₀_f₀ (θ₁ - π / 2)))
    rintro x ⟨⟨-, hxa⟩, ⟨hxb, -⟩⟩
    simp only [mem_HS, hflip, inner_neg_right] at hxa hxb
    exact le_antisymm (by linarith) hxa
  have hmeasB : MeasurableSet B :=
    (measurableSet_HS _).inter (measurableSet_HS _)
  have hsum : bvol C = bvol A + bvol B := by
    rw [← hunion]
    exact bvol_union A B hmeasB hnull
  have eA : bvol A = Wfun θ₁ := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ 0 θ₁
    rw [sub_zero] at this
    exact this
  have eB : bvol B = Wfun θ₂ := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ θ₁ (θ₁ + θ₂)
    rw [show θ₁ + θ₂ - θ₁ = θ₂ by ring] at this
    exact this
  have eC : bvol C = Wfun (θ₁ + θ₂) := by
    have := wvol_dirv_eq_Wfun norm_e₀ norm_f₀ inner_e₀_f₀ 0 (θ₁ + θ₂)
    rw [sub_zero] at this
    exact this
  rw [← eA, ← eB, ← eC, hsum]

lemma Wfun_eq {θ : ℝ} (h0 : 0 ≤ θ) (hp : θ ≤ π) : Wfun θ = 2 * θ / 3 :=
  additive_linear Wfun_nonneg Wfun_zero (fun _ _ hx hy hxy => Wfun_add hx hy hxy) Wfun_pi h0 hp

lemma dirv_zero (e f : E3) : dirv e f 0 = e := by simp [dirv]

/-- The volume of the wedge cut out by two half-spaces whose inner normals make an angle `ψ`. -/
lemma wvol_dirv_formula {e f : E3} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫ = 0)
    {ψ : ℝ} (h0 : 0 ≤ ψ) (hp : ψ ≤ π) :
    wvol (dirv e f 0) (dirv e f ψ) = 2 / 3 * (π - ψ) := by
  have key := wvol_dirv_eq_Wfun he hf hef (ψ - π / 2) (π / 2)
  rw [show ψ - π / 2 + π / 2 = ψ by ring, show π / 2 - π / 2 = (0 : ℝ) by ring,
    show π / 2 - (ψ - π / 2) = π - ψ by ring, Wfun_eq (by linarith) (by linarith)] at key
  rw [wvol_comm, key]
  ring

/-- There is a unit vector orthogonal to any given unit vector. -/
lemma exists_unit_orthogonal {u : E3} (hu : ‖u‖ = 1) : ∃ f : E3, ‖f‖ = 1 ∧ ⟪u, f⟫ = 0 := by
  have hu0 : u ≠ 0 := by intro h; rw [h] at hu; simp at hu
  have h1 : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu0
  have h2 := Submodule.finrank_add_finrank_orthogonal (K := ℝ ∙ u) (𝕜 := ℝ)
  rw [h1] at h2
  simp only [show Module.finrank ℝ E3 = 3 from by simp] at h2
  have h3 : (ℝ ∙ u)ᴾ ≠ ⊥ := by
    intro h
    rw [h] at h2
    simp at h2
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h3
  refine ⟨‖v‖⁻¹ • v, by simp [norm_smul, hv0], ?_⟩
  rw [real_inner_smul_right]
  have huv : ⟪u, v⟫ = 0 := by
    have := (Submodule.mem_orthogonal _ _).1 hv u (Submodule.mem_span_singleton_self u)
    simpa [real_inner_comm] using this
  simp [huv]

/-- Any pair of unit vectors is a pair in a rotating family, at angles `0` and `angle u v`. -/
lemma exists_dirv_repr {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ∃ e f : E3, ‖e‖ = 1 ∧ ‖f‖ = 1 ∧ ⟪e, f⟫ = 0 ∧
      u = dirv e f 0 ∧ v = dirv e f (angle u v) := by
  set ψ := angle u v with hψ
  have hcos : Real.cos ψ = ⟪u, v⟫ := by
    rw [hψ, InnerProductGeometry.cos_angle, hu, hv]
    simp
  have hsin : Real.sin ψ = ‖v - ⟪v, u⟫ • u‖ := by
    have hnn : 0 ≤ Real.sin ψ :=
      Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg u v) (angle_le_pi u v)
    have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
    have hvv : ⟪v, v⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    have hnorm : ‖v - ⟪v, u⟫ • u‖ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        huu, hvv, real_inner_comm v u]
      ring
    have hs2 : Real.sin ψ ^ 2 = 1 - ⟪u, v⟫ ^ 2 := by
      have := Real.sin_sq_add_cos_sq ψ
      rw [hcos] at this
      linarith
    nlinarith [norm_nonneg (v - ⟪v, u⟫ • u)]
  by_cases hw : v - ⟪v, u⟫ • u = 0
  · obtain ⟨f, hf, huf⟩ := exists_unit_orthogonal hu
    refine ⟨u, f, hu, hf, huf, (dirv_zero u f).symm, ?_⟩
    have hs0 : Real.sin ψ = 0 := by rw [hsin, hw, norm_zero]
    have hvu : v = ⟪v, u⟫ • u := by
      have := sub_eq_zero.1 hw
      exact this
    rw [dirv, hs0, hcos, real_inner_comm u v, ← hvu]
    simp
  · set w := v - ⟪v, u⟫ • u with hwdef
    have hwn : ‖w‖ ≠ 0 := by simpa using hw
    refine ⟨u, ‖w‖⁻¹ • w, hu, by simp [norm_smul, hwn], ?_, (dirv_zero _ _).symm, ?_⟩
    · have huu : ⟪u, u⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
      rw [real_inner_smul_right, hwdef, inner_sub_right, real_inner_smul_right, huu,
        real_inner_comm u v]
      ring
    · rw [dirv, hcos, hsin, real_inner_comm u v, smul_smul, mul_inv_cancel₀ hwn, one_smul,
        hwdef]
      abel

/-- **The wedge volume formula**: the part of the unit ball lying in the two half-spaces with
unit inner normals `u` and `v` has volume `2/3 * (π - angle u v)`. -/
theorem wvol_eq {u v : E3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    wvol u v = 2 / 3 * (π - angle u v) := by
  obtain ⟨e, f, he, hf, hef, hu', hv'⟩ := exists_dirv_repr hu hv
  rw [hu', hv']
  exact wvol_dirv_formula he hf hef (angle_nonneg u v) (angle_le_pi u v)

end Math

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

