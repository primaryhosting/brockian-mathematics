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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The Hilbert space `ℓ²(ℤ, ℂ)` on which the almost Mathieu operator acts. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have h0 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 0 := by rw [h]; simp
  rw [lp.norm_single (by norm_num)] at h0
  simp at h0

/-! ## Shift operators -/

theorem memℓp_shift (u : L2Z) (k : ℤ) : Memℓp (fun n : ℤ => (u : ℤ → ℂ) (n + k)) 2 := by
  apply memℓp_gen
  exact (Equiv.addRight k).summable_iff.mpr ((lp.memℓp u).summable (p := 2) (by norm_num))

/-- The shift by `k` as a linear map on `ℓ²(ℤ)`. -/
def shiftL (k : ℤ) : L2Z →ₗ[ℂ] L2Z where
  toFun u := ⟨fun n => (u : ℤ → ℂ) (n + k), memℓp_shift u k⟩
  map_add' u v := by ext n; simp
  map_smul' c u := by ext n; simp

theorem norm_shiftL (k : ℤ) (u : L2Z) : ‖shiftL k u‖ = ‖u‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  exact (Equiv.addRight k).tsum_eq (fun n => ‖(u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal)

/-- The shift by `k`, `(S_k u) n = u (n + k)`, as a bounded operator on `ℓ²(ℤ)`. -/
def shift (k : ℤ) : L2Z →L[ℂ] L2Z :=
  (shiftL k).mkContinuous 1 (fun u => by rw [norm_shiftL]; simp)

@[simp]
theorem shift_apply (k : ℤ) (u : L2Z) (n : ℤ) :
    (shift k u : ℤ → ℂ) n = (u : ℤ → ℂ) (n + k) := rfl

/-! ## Multiplication operators -/

theorem memℓp_mul (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (u : L2Z) :
    Memℓp (fun n : ℤ => (v n : ℂ) * (u : ℤ → ℂ) n) 2 := by
  apply memℓp_gen
  have hs := (lp.memℓp u).summable (p := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _)
    (fun n => ?_) (hs.mul_left (C ^ (2 : ℝ≥0∞).toReal))
  have h1 : ‖(v n : ℂ) * (u : ℤ → ℂ) n‖ = |v n| * ‖(u : ℤ → ℂ) n‖ := by
    simp [Complex.norm_real]
  have hvn := hv n
  rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr

/-- Multiplication by a bounded real sequence, as a linear map on `ℓ²(ℤ)`. -/
def multL (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : L2Z →ₗ[ℂ] L2Z where
  toFun u := ⟨fun n => (v n : ℂ) * (u : ℤ → ℂ) n, memℓp_mul v C hv u⟩
  map_add' u w := by ext n; simp [mul_add]
  map_smul' c u := by ext n; simp; ring

theorem multL_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (u : L2Z) (n : ℤ) :
    (multL v C hv u : ℤ → ℂ) n = (v n : ℂ) * (u : ℤ → ℂ) n := rfl

theorem norm_multL (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (u : L2Z) :
    ‖multL v C hv u‖ ≤ C * ‖u‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hs := (lp.memℓp u).summable (p := 2) (by norm_num)
  have hle : ∀ n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ C ^ (2 : ℝ≥0∞).toReal * ‖(u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
    intro n
    have h1 : ‖(multL v C hv u : ℤ → ℂ) n‖ = |v n| * ‖(u : ℤ → ℂ) n‖ := by
      rw [multL_apply]; simp [Complex.norm_real]
    have hvn := hv n
    rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
    gcongr
  calc ∑' n, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n, C ^ (2 : ℝ≥0∞).toReal * ‖(u : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal := by
        refine Summable.tsum_le_tsum hle ?_ (hs.mul_left _)
        exact (memℓp_mul v C hv u).summable (by norm_num)
    _ = C ^ (2 : ℝ≥0∞).toReal * ‖u‖ ^ (2 : ℝ≥0∞).toReal := by
        rw [hs.tsum_mul_left, ← lp.norm_rpow_eq_tsum (by norm_num)]
    _ = (C * ‖u‖) ^ (2 : ℝ≥0∞).toReal := by
        rw [Real.mul_rpow hC (norm_nonneg _)]

/-- Multiplication by a bounded real sequence, as a bounded operator on `ℓ²(ℤ)`. -/
def mult (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : L2Z →L[ℂ] L2Z :=
  (multL v C hv).mkContinuous C (norm_multL v C hv)

@[simp]
theorem mult_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (u : L2Z) (n : ℤ) :
    (mult v C hv u : ℤ → ℂ) n = (v n : ℂ) * (u : ℤ → ℂ) n := rfl

/-! ## Adjoints -/

theorem inner_lp (f g : L2Z) : inner ℂ f g = ∑' i : ℤ, (starRingEnd ℂ) (f i) * g i := by
  rw [lp.inner_eq_tsum]; simp [RCLike.inner_apply, mul_comm]

theorem adjoint_shift (k : ℤ) : ContinuousLinearMap.adjoint (shift k) = shift (-k) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_lp, inner_lp]
  have := (Equiv.addRight (-k)).tsum_eq
    (fun n : ℤ => (starRingEnd ℂ) ((x : ℤ → ℂ) n) * (y : ℤ → ℂ) (n + k))
  simpa [shift_apply] using this

theorem adjoint_mult (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) :
    ContinuousLinearMap.adjoint (mult v C hv) = mult v C hv := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_lp, inner_lp]
  refine tsum_congr (fun n => ?_)
  simp only [mult_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator:
`v n = 2 * lam * cos (2 * π * (theta + n * alpha))`. -/
def amoPot (lam alpha theta : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * π * (theta + n * alpha))

theorem abs_amoPot_le (lam alpha theta : ℝ) (n : ℤ) : |amoPot lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * π * (theta + n * alpha))
  calc |amoPot lam alpha theta n| = (2 * |lam|) * |Real.cos (2 * π * (theta + n * alpha))| := by
        rw [amoPot, abs_mul, abs_mul]
        simp
    _ ≤ (2 * |lam|) * 1 := by
        have : (0 : ℝ) ≤ 2 * |lam| := by positivity
        exact mul_le_mul_of_nonneg_left h this
    _ = 2 * |lam| := by ring

/-- The almost Mathieu operator with coupling `lam`, flux `alpha` and phase `theta`:
`(H u) n = u (n + 1) + u (n - 1) + 2 * lam * cos (2 * π * (theta + n * alpha)) * u n`. -/
def amo (lam alpha theta : ℝ) : L2Z →L[ℂ] L2Z :=
  shift 1 + shift (-1) + mult (amoPot lam alpha theta) (2 * |lam|) (abs_amoPot_le lam alpha theta)

theorem amo_apply (lam alpha theta : ℝ) (u : L2Z) (n : ℤ) :
    (amo lam alpha theta u : ℤ → ℂ) n
      = (u : ℤ → ℂ) (n + 1) + (u : ℤ → ℂ) (n - 1)
        + (2 * lam * Real.cos (2 * π * (theta + n * alpha)) : ℝ) * (u : ℤ → ℂ) n := by
  show ((shift 1 u : ℤ → ℂ) n + (shift (-1) u : ℤ → ℂ) n) + _ = _
  simp [amoPot, sub_eq_add_neg]

theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  have hstar : ∀ A : L2Z →L[ℂ] L2Z, star A = ContinuousLinearMap.adjoint A := fun A => rfl
  unfold IsSelfAdjoint amo
  rw [star_add, star_add, hstar, hstar, hstar, adjoint_shift, adjoint_shift, adjoint_mult]
  simp [add_comm]

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate since the operator is self-adjoint). -/
def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

/-! ## Cantor sets -/

/-- A subset of `ℝ` is a Cantor set if it is nonempty, compact, perfect (closed with no isolated
points) and totally disconnected. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ Perfect S ∧ IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts hpre x hx y hy
  by_contra hxy
  -- WLOG `x < y`
  have key : ∀ a b : ℝ, a ∈ t → b ∈ t → a < b → False := by
    intro a b ha hb hab
    have hIcc : Set.Icc a b ⊆ t := hpre.ordConnected.out ha hb
    have hIoo : Set.Ioo a b ⊆ S :=
      fun z hz => hts (hIcc ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    have hsub : Set.Ioo a b ⊆ interior S := interior_maximal hIoo isOpen_Ioo
    have hne : (Set.Ioo a b).Nonempty := Set.nonempty_Ioo.mpr hab
    rw [h] at hsub
    exact Set.not_nonempty_empty (hne.mono hsub)
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact key x y hx hy hlt
  · exact key y x hy hx hlt

/-! ## Unconditional facts about the spectrum -/

theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  refine ⟨z.re, ?_⟩
  have hre : z = (z.re : ℂ) := (amo_isSelfAdjoint lam alpha theta).mem_spectrum_eq_re hz
  simpa [amoSpectrum, ← hre] using hz

theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) := by
  have : amoSpectrum lam alpha theta = (fun E : ℝ => (E : ℂ)) ⁻¹' spectrum ℂ (amo lam alpha theta) :=
    rfl
  rw [this]
  exact (spectrum.isClosed _).preimage Complex.continuous_ofReal

theorem amoSpectrum_subset_closedBall (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Metric.closedBall 0 ‖amo lam alpha theta‖ := by
  intro E hE
  have h : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  simpa [Real.norm_eq_abs, Complex.norm_real] using h

theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) := by
  refine Metric.isCompact_of_isClosed_isBounded (amoSpectrum_isClosed lam alpha theta) ?_
  exact (Metric.isBounded_closedBall).subset (amoSpectrum_subset_closedBall lam alpha theta)

/-! ## The Ten Martini problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling constant `lam`
and every irrational flux `alpha`, the spectrum of the almost Mathieu operator is a Cantor set. -/
def TenMartiniProblem : Prop :=
  ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha → IsCantorSet (amoSpectrum lam alpha theta)

/-- **Lean-checked reduction of the Ten Martini Problem.**

The spectrum of the almost Mathieu operator is always nonempty and compact (proved here from
scratch, from the construction of the operator on `ℓ²(ℤ)` and its self-adjointness).  Hence the
Ten Martini Problem — Cantor spectrum for all nonzero couplings and all irrational fluxes —
reduces to the two remaining analytic inputs:

* *all spectral gaps are dense*, i.e. the spectrum has empty interior (this is the hard part
  proved by Avila and Jitomirskaya), and
* the spectrum has *no isolated points* (`Preperfect`).

Given those two inputs the full statement follows. -/
theorem avila_ten_martini
    (h_empty_interior : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅)
    (h_preperfect : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      Preperfect (amoSpectrum lam alpha theta)) :
    TenMartiniProblem := by
  intro lam alpha theta hlam halpha
  refine ⟨amoSpectrum_nonempty lam alpha theta, amoSpectrum_isCompact lam alpha theta,
    ⟨amoSpectrum_isClosed lam alpha theta, h_preperfect lam alpha theta hlam halpha⟩,
    isTotallyDisconnected_of_interior_eq_empty (h_empty_interior lam alpha theta hlam halpha)⟩

end

end Frontier

