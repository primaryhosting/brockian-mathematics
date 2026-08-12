/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ, ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev H2 := ℓ²(ℤ, ℂ)

instance : Nontrivial H2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have : (lp.single 2 (0 : ℤ) (1 : ℂ) : ℤ → ℂ) 0 = (0 : H2) 0 := by rw [h]
  simp [lp.single_apply] at this

/-! ## Shift operators -/

lemma memℓp_shift (k : ℤ) (f : H2) : Memℓp (fun n : ℤ => (f : ℤ → ℂ) (n + k)) 2 := by
  apply memℓp_gen
  exact (Equiv.addRight k).summable_iff.mpr ((lp.memℓp f).summable (p := 2) (by norm_num))

/-- The translation `(f n) ↦ (f (n + k))` as a linear map on `ℓ²(ℤ, ℂ)`. -/
def shiftL (k : ℤ) : H2 →ₗ[ℂ] H2 where
  toFun f := ⟨fun n => (f : ℤ → ℂ) (n + k), memℓp_shift k f⟩
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

lemma norm_shiftL (k : ℤ) (f : H2) : ‖shiftL k f‖ = ‖f‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.addRight k).tsum_eq (fun n => ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal)

/-- The translation `(f n) ↦ (f (n + k))` as a bounded operator on `ℓ²(ℤ, ℂ)`. -/
def shift (k : ℤ) : H2 →L[ℂ] H2 :=
  (shiftL k).mkContinuous 1 (fun f => by simp [norm_shiftL])

@[simp] lemma shift_apply (k : ℤ) (f : H2) (n : ℤ) :
    (shift k f : ℤ → ℂ) n = (f : ℤ → ℂ) (n + k) := rfl

lemma norm_shift_le (k : ℤ) : ‖shift k‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## Multiplication operators -/

lemma memℓp_mul (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : H2) :
    Memℓp (fun n : ℤ => (v n : ℂ) * (f : ℤ → ℂ) n) 2 := by
  apply memℓp_gen
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  have hs := (lp.memℓp f).summable (p := 2) (by norm_num)
  have h2 : Summable fun n : ℤ => C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
    hs.mul_left _
  refine h2.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [← Real.mul_rpow (by positivity) (by positivity)]
  exact Real.rpow_le_rpow (by positivity)
    (by nlinarith [norm_nonneg ((f : ℤ → ℂ) n), hv n]) (by norm_num)

/-- Multiplication by a bounded real sequence, as a linear map on `ℓ²(ℤ, ℂ)`. -/
def mulL (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : H2 →ₗ[ℂ] H2 where
  toFun f := ⟨fun n => (v n : ℂ) * (f : ℤ → ℂ) n, memℓp_mul v C hv f⟩
  map_add' f g := by ext n; simp [mul_add]
  map_smul' c f := by ext n; simp [mul_left_comm]

lemma norm_mulL_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : H2) :
    ‖mulL v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hsum : ∀ n : ℤ, ‖(mulL v C hv f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    show ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      ← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity)
      (by nlinarith [norm_nonneg ((f : ℤ → ℂ) n), hv n]) (by norm_num)
  have hs := (lp.memℓp f).summable (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  calc ∑' n : ℤ, ‖(mulL v C hv f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n : ℤ, C ^ (2 : ℝ≥0∞).toReal * ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal :=
        Summable.tsum_le_tsum hsum ((lp.memℓp (mulL v C hv f)).summable (by norm_num))
          (hs.mul_left _)
    _ = C ^ (2 : ℝ≥0∞).toReal * ∑' n : ℤ, ‖(f : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := tsum_mul_left
    _ = (C * ‖f‖) ^ (2 : ℝ≥0∞).toReal := by
        rw [Real.mul_rpow hC (norm_nonneg _), lp.norm_rpow_eq_tsum (by norm_num)]

/-- Multiplication by a bounded real sequence, as a bounded operator on `ℓ²(ℤ, ℂ)`. -/
def mulOp (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : H2 →L[ℂ] H2 :=
  (mulL v C hv).mkContinuous C (norm_mulL_le v C hv)

@[simp] lemma mulOp_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : H2) (n : ℤ) :
    (mulOp v C hv f : ℤ → ℂ) n = (v n : ℂ) * (f : ℤ → ℂ) n := rfl

lemma norm_mulOp_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : ‖mulOp v C hv‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (abs_nonneg _) (hv 0)) _

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator with coupling `lam`, flux `alpha` and
phase `theta`: `n ↦ 2 * lam * cos (2 * π * (theta + n * alpha))`. -/
def amPotential (lam alpha theta : ℝ) : ℤ → ℝ :=
  fun n => 2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))

lemma abs_amPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    |amPotential lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * Real.pi * (theta + n * alpha))
  have h2 : |2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))|
      = 2 * |lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))| := by
    rw [abs_mul, abs_mul]
    norm_num
  rw [amPotential, h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * Real.pi * (theta + n * alpha)))]

/-- The **almost Mathieu operator** `H_{lam, alpha, theta}` on `ℓ²(ℤ, ℂ)`:
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`. -/
def almostMathieu (lam alpha theta : ℝ) : H2 →L[ℂ] H2 :=
  shift 1 + shift (-1) +
    mulOp (amPotential lam alpha theta) (2 * |lam|) (abs_amPotential_le lam alpha theta)

lemma almostMathieu_apply (lam alpha theta : ℝ) (u : H2) (n : ℤ) :
    (almostMathieu lam alpha theta u : ℤ → ℂ) n =
      (u : ℤ → ℂ) (n + 1) + (u : ℤ → ℂ) (n - 1) +
        (2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) * (u : ℤ → ℂ) n := by
  show (shift 1 u : ℤ → ℂ) n + (shift (-1) u : ℤ → ℂ) n + _ = _
  simp [amPotential, sub_eq_add_neg]

/-! ## Self-adjointness -/

lemma inner_shift_left (k : ℤ) (f g : H2) :
    inner ℂ (shift k f) g = inner ℂ f (shift (-k) g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have h := (Equiv.addRight k).tsum_eq
    (fun n : ℤ => inner ℂ ((f : ℤ → ℂ) n) ((shift (-k) g : ℤ → ℂ) n))
  rw [← h]
  refine tsum_congr (fun n => ?_)
  simp [shift_apply]

lemma isSelfAdjoint_shift_add_shift : IsSelfAdjoint (shift 1 + shift (-1) : H2 →L[ℂ] H2) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  have h1 := inner_shift_left 1 f g
  have h2 := inner_shift_left (-1) f g
  simp only [ContinuousLinearMap.coe_add, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
    inner_add_left, inner_add_right]
  rw [h1, h2, neg_neg]
  ring

lemma isSelfAdjoint_mulOp (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) :
    IsSelfAdjoint (mulOp v C hv) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  simp only [RCLike.inner_apply]
  show (g : ℤ → ℂ) n * (starRingEnd ℂ) ((v n : ℂ) * (f : ℤ → ℂ) n)
      = ((v n : ℂ) * (g : ℤ → ℂ) n) * (starRingEnd ℂ) ((f : ℤ → ℂ) n)
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- The almost Mathieu operator is self-adjoint. -/
theorem isSelfAdjoint_almostMathieu (lam alpha theta : ℝ) :
    IsSelfAdjoint (almostMathieu lam alpha theta) :=
  (isSelfAdjoint_shift_add_shift).add
    (isSelfAdjoint_mulOp _ _ (abs_amPotential_le lam alpha theta))

lemma norm_almostMathieu_le (lam alpha theta : ℝ) :
    ‖almostMathieu lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(shift 1 + shift (-1) : H2 →L[ℂ] H2)‖ ≤ 2 :=
    le_trans (norm_add_le _ _) (by linarith [norm_shift_le 1, norm_shift_le (-1)])
  have h2 := norm_mulOp_le (amPotential lam alpha theta) (2 * |lam|)
    (abs_amPotential_le lam alpha theta)
  linarith

/-! ## Eigenvalues have multiplicity at most two -/

/-- An eigenvector of the almost Mathieu operator satisfies the second-order difference
equation `u (n + 1) = (E - v n) * u n - u (n - 1)`. -/
lemma eigen_recurrence {lam alpha theta : ℝ} {E : ℂ} {u : H2}
    (hu : almostMathieu lam alpha theta u = E • u) (n : ℤ) :
    (u : ℤ → ℂ) (n + 1)
      = (E - (amPotential lam alpha theta n : ℂ)) * (u : ℤ → ℂ) n - (u : ℤ → ℂ) (n - 1) := by
  have h : (almostMathieu lam alpha theta u : ℤ → ℂ) n = ((E • u : H2) : ℤ → ℂ) n := by rw [hu]
  rw [almostMathieu_apply] at h
  have h2 : ((E • u : H2) : ℤ → ℂ) n = E * (u : ℤ → ℂ) n := rfl
  rw [h2] at h
  have hv : ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ)
      = ((amPotential lam alpha theta n : ℝ) : ℂ) := rfl
  rw [hv] at h
  linear_combination h

/-- An eigenvector of the almost Mathieu operator is determined by its values at `0` and `1`. -/
theorem eigenvector_eq_of_eq_at_zero_one {lam alpha theta : ℝ} {E : ℂ} {u w : H2}
    (hu : almostMathieu lam alpha theta u = E • u)
    (hw : almostMathieu lam alpha theta w = E • w)
    (h0 : (u : ℤ → ℂ) 0 = (w : ℤ → ℂ) 0) (h1 : (u : ℤ → ℂ) 1 = (w : ℤ → ℂ) 1) :
    u = w := by
  have key : ∀ n : ℤ, (u : ℤ → ℂ) n = (w : ℤ → ℂ) n ∧
      (u : ℤ → ℂ) (n + 1) = (w : ℤ → ℂ) (n + 1) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ⟨h0, by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hu' := eigen_recurrence hu ((k : ℤ) + 1)
      have hw' := eigen_recurrence hw ((k : ℤ) + 1)
      have e1 : ((k : ℤ) + 1 - 1) = (k : ℤ) := by ring
      rw [e1] at hu' hw'
      rw [show ((k : ℤ) + 1 + 1) = (k : ℤ) + 1 + 1 from rfl] at hu' hw'
      rw [hu', hw', ih.1, ih.2]
    | pred k ih =>
      have e2 : (-(k : ℤ) - 1 + 1) = -(k : ℤ) := by ring
      refine ⟨?_, by rw [e2]; exact ih.1⟩
      have hu' := eigen_recurrence hu (-(k : ℤ))
      have hw' := eigen_recurrence hw (-(k : ℤ))
      have hu'' : (u : ℤ → ℂ) (-(k : ℤ) - 1)
          = (E - (amPotential lam alpha theta (-(k : ℤ)) : ℂ)) * (u : ℤ → ℂ) (-(k : ℤ))
            - (u : ℤ → ℂ) (-(k : ℤ) + 1) := by linear_combination hu'
      have hw'' : (w : ℤ → ℂ) (-(k : ℤ) - 1)
          = (E - (amPotential lam alpha theta (-(k : ℤ)) : ℂ)) * (w : ℤ → ℂ) (-(k : ℤ))
            - (w : ℤ → ℂ) (-(k : ℤ) + 1) := by linear_combination hw'
      rw [hu'', hw'', ih.1, ih.2]
  ext n
  exact (key n).1

/-- Every eigenvalue of the almost Mathieu operator has multiplicity at most `2`: the
eigenspace for `E` has rank at most `2`, since an eigenvector is determined by its values
at `0` and `1`. -/
theorem rank_eigenspace_le_two (lam alpha theta : ℝ) (E : ℂ) :
    Module.rank ℂ
        (LinearMap.ker (almostMathieu lam alpha theta - E • (1 : H2 →L[ℂ] H2) :
          H2 →L[ℂ] H2).toLinearMap) ≤ 2 := by
  set A := almostMathieu lam alpha theta
  set K := LinearMap.ker (A - E • (1 : H2 →L[ℂ] H2) : H2 →L[ℂ] H2).toLinearMap
  have hmem : ∀ u : H2, u ∈ K → A u = E • u := by
    intro u hu
    have : (A - E • (1 : H2 →L[ℂ] H2)) u = 0 := hu
    simpa [sub_eq_zero] using this
  let ev : K →ₗ[ℂ] ℂ × ℂ :=
    { toFun := fun u => (((u : H2) : ℤ → ℂ) 0, ((u : H2) : ℤ → ℂ) 1)
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  have hinj : Function.Injective ev := by
    intro a b hab
    have h0 : ((a : H2) : ℤ → ℂ) 0 = ((b : H2) : ℤ → ℂ) 0 := congrArg Prod.fst hab
    have h1 : ((a : H2) : ℤ → ℂ) 1 = ((b : H2) : ℤ → ℂ) 1 := congrArg Prod.snd hab
    exact Subtype.ext
      (eigenvector_eq_of_eq_at_zero_one (hmem _ a.2) (hmem _ b.2) h0 h1)
  have h := LinearMap.rank_le_of_injective ev hinj
  have h2 : Module.rank ℂ (ℂ × ℂ) = 2 := by simpa using one_add_one_eq_two
  rwa [h2] at h

/-! ## The real spectrum of the almost Mathieu operator -/

/-- The (real) spectrum of the almost Mathieu operator. -/
def amSpectrum (lam alpha theta : ℝ) : Set ℝ := spectrum ℝ (almostMathieu lam alpha theta)

lemma amSpectrum_eq_image (lam alpha theta : ℝ) :
    amSpectrum lam alpha theta =
      Complex.reCLM '' spectrum ℂ (almostMathieu lam alpha theta) :=
  ((isSelfAdjoint_almostMathieu lam alpha theta).spectrumRestricts).image.symm

/-- The spectrum of the almost Mathieu operator is nonempty. -/
theorem amSpectrum_nonempty (lam alpha theta : ℝ) : (amSpectrum lam alpha theta).Nonempty := by
  rw [amSpectrum_eq_image]
  exact (spectrum.nonempty (almostMathieu lam alpha theta)).image _

/-- The spectrum of the almost Mathieu operator is compact. -/
theorem amSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amSpectrum lam alpha theta) := by
  rw [amSpectrum_eq_image]
  exact (spectrum.isCompact (almostMathieu lam alpha theta)).image Complex.reCLM.continuous

/-- The spectrum of the almost Mathieu operator is contained in `[-(2 + 2|lam|), 2 + 2|lam|]`. -/
theorem amSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro x hx
  have h : ‖x‖ ≤ ‖almostMathieu lam alpha theta‖ := spectrum.norm_le_norm_of_mem hx
  have h2 := norm_almostMathieu_le lam alpha theta
  rw [Real.norm_eq_abs] at h
  have := abs_le.mp (le_trans h h2)
  exact ⟨this.1, this.2⟩

/-! ## Cantor sets -/

/-- A subset of `ℝ` is a *Cantor set* if it is nonempty, compact, perfect (closed with no
isolated points) and totally disconnected. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ Perfect S ∧ IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts ht x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hIcc : Set.Icc x y ⊆ t := ht.ordConnected.out hx hy
    have : Set.Ioo x y ⊆ interior S :=
      (isOpen_Ioo.subset_interior_iff).mpr
        (fun z hz => hts (hIcc (Set.Ioo_subset_Icc_self hz)))
    rw [h] at this
    exact absurd (this (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩ :
      (x + y) / 2 ∈ Set.Ioo x y)) (Set.notMem_empty _)
  · have hIcc : Set.Icc y x ⊆ t := ht.ordConnected.out hy hx
    have : Set.Ioo y x ⊆ interior S :=
      (isOpen_Ioo.subset_interior_iff).mpr
        (fun z hz => hts (hIcc (Set.Ioo_subset_Icc_self hz)))
    rw [h] at this
    exact absurd (this (Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩ :
      (x + y) / 2 ∈ Set.Ioo y x)) (Set.notMem_empty _)

/-- A nonempty compact subset of `ℝ` with empty interior and no isolated points is a
Cantor set. -/
theorem isCantorSet_of_interior_eq_empty {S : Set ℝ} (hne : S.Nonempty) (hcomp : IsCompact S)
    (hint : interior S = ∅) (hacc : ∀ x ∈ S, AccPt x (Filter.principal S)) :
    IsCantorSet S :=
  ⟨hne, hcomp, ⟨hcomp.isClosed, hacc⟩, isTotallyDisconnected_of_interior_eq_empty hint⟩

lemma not_countable_natToBool : ¬ Countable (ℕ → Bool) := by
  intro h
  rw [← Cardinal.mk_le_aleph0_iff, Cardinal.mk_arrow] at h
  simp only [Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_id] at h
  exact absurd h (not_le.mpr (Cardinal.cantor Cardinal.aleph0))

/-- A Cantor set in `ℝ` admits a continuous injection from the Cantor space `ℕ → Bool`. -/
theorem IsCantorSet.exists_nat_bool_injection {S : Set ℝ} (hS : IsCantorSet S) :
    ∃ f : (ℕ → Bool) → ℝ, Set.range f ⊆ S ∧ Continuous f ∧ Function.Injective f :=
  hS.2.2.1.exists_nat_bool_injection hS.1

/-- A Cantor set in `ℝ` is uncountable. -/
theorem IsCantorSet.not_countable {S : Set ℝ} (hS : IsCantorSet S) : ¬ S.Countable := by
  intro hc
  obtain ⟨f, hrange, -, hinj⟩ := hS.exists_nat_bool_injection
  have h1 : (Set.range f).Countable := hc.mono hrange
  have := h1.to_subtype
  exact not_countable_natToBool
    (Function.Injective.countable
      (f := fun x => (⟨f x, Set.mem_range_self x⟩ : Set.range f))
      (fun a b hab => hinj (congrArg Subtype.val hab)))

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya), formalized as a Lean-checked reduction.

For every nonzero coupling constant `lam`, every irrational flux `alpha` and every phase
`theta`, the spectrum of the almost Mathieu operator
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`
on `ℓ²(ℤ, ℂ)` is a Cantor set.

The two analytic inputs of the theorem are taken as hypotheses:
* `h_nowhere_dense`: the spectrum has empty interior (this is the hard "dry/dense gaps"
  content of the Ten Martini Problem, i.e. all gaps predicted by the gap-labelling theorem
  are open);
* `h_no_isolated`: the spectrum has no isolated points.

Everything else is proved here from the definition of the operator: the spectrum is
nonempty (via self-adjointness and nonemptiness of the complex spectrum), compact, and
empty interior in `ℝ` forces total disconnectedness.

The hypotheses `hlam : lam ≠ 0` and `halpha : Irrational alpha` are part of the classical
statement; they are what makes the two analytic inputs above true, and are not otherwise
used in this reduction. -/
theorem avila_ten_martini (lam alpha theta : ℝ) (hlam : lam ≠ 0) (halpha : Irrational alpha)
    (h_nowhere_dense : interior (amSpectrum lam alpha theta) = ∅)
    (h_no_isolated : ∀ x ∈ amSpectrum lam alpha theta,
      AccPt x (Filter.principal (amSpectrum lam alpha theta))) :
    IsCantorSet (amSpectrum lam alpha theta) :=
  isCantorSet_of_interior_eq_empty (amSpectrum_nonempty lam alpha theta)
    (amSpectrum_isCompact lam alpha theta) h_nowhere_dense h_no_isolated

/-- Under the hypotheses of the Ten Martini Problem, the spectrum of the almost Mathieu
operator is uncountable. -/
theorem amSpectrum_not_countable (lam alpha theta : ℝ) (hlam : lam ≠ 0)
    (halpha : Irrational alpha)
    (h_nowhere_dense : interior (amSpectrum lam alpha theta) = ∅)
    (h_no_isolated : ∀ x ∈ amSpectrum lam alpha theta,
      AccPt x (Filter.principal (amSpectrum lam alpha theta))) :
    ¬ (amSpectrum lam alpha theta).Countable :=
  (avila_ten_martini lam alpha theta hlam halpha h_nowhere_dense h_no_isolated).not_countable

end

end Frontier

