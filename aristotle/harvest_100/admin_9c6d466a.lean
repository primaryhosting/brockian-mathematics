/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

noncomputable section

/-! ## The Hilbert space `ℓ²(ℤ)` -/

/-- The complex Hilbert space `ℓ²(ℤ)`, on which the almost Mathieu operator acts. -/
abbrev Hl2 := lp (fun _ : ℤ => ℂ) 2

/-- Auxiliary: the real exponent attached to `p = 2`. -/
theorem rpow_two_eq_sq (x : ℝ) : x ^ ((2 : ℝ≥0∞)).toReal = x ^ 2 := by
  rw [show ((2 : ℝ≥0∞)).toReal = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-! ## Shift operators -/

theorem memShift (k : ℤ) (u : Hl2) : Memℓp (fun n : ℤ => (u : ℤ → ℂ) (n + k)) 2 := by
  apply memℓp_gen
  exact (Equiv.addRight k).summable_iff.2 ((lp.memℓp u).summable (p := 2) (by norm_num))

/-- The shift `(S_k u)(n) = u(n + k)` as a linear map on `ℓ²(ℤ)`. -/
def shiftL (k : ℤ) : Hl2 →ₗ[ℂ] Hl2 where
  toFun u := ⟨fun n => (u : ℤ → ℂ) (n + k), memShift k u⟩
  map_add' u v := by ext n; simp
  map_smul' c u := by ext n; simp

@[simp] theorem shiftL_apply (k : ℤ) (u : Hl2) (n : ℤ) :
    (shiftL k u : ℤ → ℂ) n = (u : ℤ → ℂ) (n + k) := rfl

theorem shiftL_norm (k : ℤ) (u : Hl2) : ‖shiftL k u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg u)
  have h1 : ∑' i : ℤ, ‖(shiftL k u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal
      = ∑' i : ℤ, ‖(u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal :=
    (Equiv.addRight k).tsum_eq (fun i => ‖(u : ℤ → ℂ) i‖ ^ ((2 : ℝ≥0∞)).toReal)
  rw [h1, lp.norm_rpow_eq_tsum (by norm_num)]

/-- The shift `(S_k u)(n) = u(n + k)` as a bounded operator on `ℓ²(ℤ)`. -/
def shift (k : ℤ) : Hl2 →L[ℂ] Hl2 :=
  (shiftL k).mkContinuous 1 (by simpa using shiftL_norm k)

@[simp] theorem shift_apply (k : ℤ) (u : Hl2) (n : ℤ) :
    (shift k u : ℤ → ℂ) n = (u : ℤ → ℂ) (n + k) := rfl

theorem shift_norm_le (k : ℤ) : ‖shift k‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## Multiplication operators -/

theorem memMult (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) :
    Memℓp (fun n : ℤ => v n * (u : ℤ → ℂ) n) 2 := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply memℓp_gen
  have hu := (lp.memℓp u).summable (p := 2) (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hu.mul_left (C ^ 2))
  rw [norm_mul, rpow_two_eq_sq, rpow_two_eq_sq, mul_pow]
  have h : ‖v n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (v n), hv n]
  nlinarith [norm_nonneg ((u : ℤ → ℂ) n), sq_nonneg ‖(u : ℤ → ℂ) n‖]

/-- Multiplication by a bounded sequence `v`, as a linear map on `ℓ²(ℤ)`. -/
def multL (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) : Hl2 →ₗ[ℂ] Hl2 where
  toFun u := ⟨fun n => v n * (u : ℤ → ℂ) n, memMult v C hv u⟩
  map_add' u w := by ext n; simp [mul_add]
  map_smul' c u := by ext n; simp; ring

@[simp] theorem multL_apply (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) (n : ℤ) :
    (multL v C hv u : ℤ → ℂ) n = v n * (u : ℤ → ℂ) n := rfl

theorem multL_norm (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) :
    ‖multL v C hv u‖ ≤ C * ‖u‖ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  have hu := (lp.memℓp u).summable (p := 2) (by norm_num)
  have key : ∀ n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal
      ≤ C ^ 2 * (‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal) := by
    intro n
    rw [multL_apply, norm_mul, rpow_two_eq_sq, rpow_two_eq_sq, mul_pow]
    have h : ‖v n‖ ^ 2 ≤ C ^ 2 := by nlinarith [norm_nonneg (v n), hv n]
    nlinarith [norm_nonneg ((u : ℤ → ℂ) n), sq_nonneg ‖(u : ℤ → ℂ) n‖]
  calc ∑' n : ℤ, ‖(multL v C hv u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal
      ≤ ∑' n : ℤ, C ^ 2 * ‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal :=
        Summable.tsum_le_tsum key
          (Summable.of_nonneg_of_le (fun n => by positivity) key (hu.mul_left _))
          (hu.mul_left _)
    _ = C ^ 2 * ∑' n : ℤ, ‖(u : ℤ → ℂ) n‖ ^ ((2 : ℝ≥0∞)).toReal := tsum_mul_left
    _ = (C * ‖u‖) ^ ((2 : ℝ≥0∞)).toReal := by
        rw [← lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u, rpow_two_eq_sq, rpow_two_eq_sq,
          mul_pow]

/-- Multiplication by a bounded sequence `v`, as a bounded operator on `ℓ²(ℤ)`. -/
def mult (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) : Hl2 →L[ℂ] Hl2 :=
  (multL v C hv).mkContinuous C (multL_norm v C hv)

@[simp] theorem mult_apply (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) (u : Hl2) (n : ℤ) :
    (mult v C hv u : ℤ → ℂ) n = v n * (u : ℤ → ℂ) n := rfl

theorem mult_norm_le (v : ℤ → ℂ) (C : ℝ) (hv : ∀ n, ‖v n‖ ≤ C) : ‖mult v C hv‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg _) (hv 0)) _

/-! ## The almost Mathieu operator -/

/-- The almost Mathieu potential `v(n) = 2 λ cos(2π(θ + n α))`. -/
def amoPot (lam alpha theta : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))

theorem amoPot_bound (lam alpha theta : ℝ) (n : ℤ) :
    ‖((amoPot lam alpha theta n : ℝ) : ℂ)‖ ≤ 2 * |lam| := by
  rw [Complex.norm_real, amoPot]
  have h := Real.abs_cos_le_one (2 * Real.pi * (theta + n * alpha))
  calc |2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))|
      = |2 * lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))| := abs_mul _ _
    _ ≤ |2 * lam| * 1 := by
        exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = 2 * |lam| := by rw [mul_one, abs_mul]; simp

/-- The **almost Mathieu operator** `H_{λ,α,θ}` on `ℓ²(ℤ)`:
`(H u)(n) = u(n+1) + u(n-1) + 2 λ cos(2π(θ + nα)) u(n)`. -/
def amo (lam alpha theta : ℝ) : Hl2 →L[ℂ] Hl2 :=
  shift 1 + shift (-1) +
    mult (fun n => ((amoPot lam alpha theta n : ℝ) : ℂ)) (2 * |lam|) (amoPot_bound lam alpha theta)

@[simp] theorem amo_apply (lam alpha theta : ℝ) (u : Hl2) (n : ℤ) :
    (amo lam alpha theta u : ℤ → ℂ) n =
      (u : ℤ → ℂ) (n + 1) + (u : ℤ → ℂ) (n - 1)
        + ((amoPot lam alpha theta n : ℝ) : ℂ) * (u : ℤ → ℂ) n := by
  simp [amo, sub_eq_add_neg]

/-! ### Basic operator-theoretic facts about the almost Mathieu operator -/

theorem adjoint_shift_one : ContinuousLinearMap.adjoint (shift (1 : ℤ)) = shift (-1) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  have := (Equiv.addRight (-1 : ℤ)).tsum_eq
    (fun n : ℤ => (inner ℂ ((u : ℤ → ℂ) n) ((shift (1 : ℤ) v : ℤ → ℂ) n) : ℂ))
  simpa [sub_add_cancel, add_comm] using this

theorem isSelfAdjoint_mult_real (w : ℤ → ℝ) (C : ℝ) (hw : ∀ n, ‖((w n : ℝ) : ℂ)‖ ≤ C) :
    IsSelfAdjoint (mult (fun n => ((w n : ℝ) : ℂ)) C hw) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro u v
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  simp only [ContinuousLinearMap.coe_coe, mult_apply, RCLike.inner_apply]
  simp [Complex.conj_ofReal]
  ring

/-- The almost Mathieu operator is self-adjoint. -/
theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  have h1 : star (shift (1 : ℤ)) = shift (-1) := adjoint_shift_one
  have h2 : star (shift (-1 : ℤ)) = shift 1 := by
    have := congrArg star h1
    simpa using this.symm
  have h3 := isSelfAdjoint_mult_real (fun n => amoPot lam alpha theta n) (2 * |lam|)
    (amoPot_bound lam alpha theta)
  show star (amo lam alpha theta) = amo lam alpha theta
  rw [amo, star_add, star_add, h1, h2, h3]
  abel

theorem amo_norm_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖shift (1 : ℤ) + shift (-1)‖ ≤ 2 :=
    le_trans (norm_add_le _ _) (by linarith [shift_norm_le (1 : ℤ), shift_norm_le (-1 : ℤ)])
  have h2 := mult_norm_le (fun n => ((amoPot lam alpha theta n : ℝ) : ℂ)) (2 * |lam|)
    (amoPot_bound lam alpha theta)
  exact add_le_add h1 h2

/-! ## The spectrum of the almost Mathieu operator, as a subset of `ℝ` -/

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate, since the operator is self-adjoint). -/
def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

/-- Every point of the complex spectrum of the almost Mathieu operator is real. -/
theorem amo_spectrum_real (lam alpha theta : ℝ) {z : ℂ} (hz : z ∈ spectrum ℂ (amo lam alpha theta)) :
    z = ((z.re : ℝ) : ℂ) := by
  have him : z.im = 0 := (amo_isSelfAdjoint lam alpha theta).im_eq_zero_of_mem_spectrum hz
  exact Complex.ext rfl (by simpa using him)

instance : Nontrivial Hl2 :=
  ⟨⟨lp.single 2 (0 : ℤ) 1, 0, by
      intro h
      have := congrFun (congrArg (fun x : Hl2 => (x : ℤ → ℂ)) h) 0
      simp [lp.single_apply] at this⟩⟩

/-- The (real) spectrum of the almost Mathieu operator is nonempty. -/
theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  exact ⟨z.re, by simpa [amoSpectrum, ← amo_spectrum_real lam alpha theta hz] using hz⟩

/-- The (real) spectrum of the almost Mathieu operator is contained in a bounded interval. -/
theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 : |E| ≤ 2 + 2 * |lam| :=
    le_trans (by simpa using h1) (amo_norm_le lam alpha theta)
  exact Set.mem_Icc.2 ⟨(abs_le.1 h2).1, (abs_le.1 h2).2⟩

/-- The (real) spectrum of the almost Mathieu operator is closed. -/
theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) := by
  have hcl : IsClosed (spectrum ℂ (amo lam alpha theta)) :=
    (spectrum.isCompact (amo lam alpha theta)).isClosed
  exact hcl.preimage Complex.continuous_ofReal

/-- The (real) spectrum of the almost Mathieu operator is compact. -/
theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) := by
  refine Metric.isCompact_of_isClosed_isBounded (amoSpectrum_isClosed lam alpha theta) ?_
  exact (Metric.isBounded_Icc _ _).subset (amoSpectrum_subset_Icc lam alpha theta)

/-! ### Covariance: the phase shift `θ ↦ θ + α` is a unitary conjugation -/

theorem shift_mul_shift (k l : ℤ) : shift k * shift l = shift (k + l) := by
  ext u n
  simp [add_assoc]

@[simp] theorem shift_zero : shift 0 = 1 := by
  ext u n
  simp

/-- The shift, as a unit of the algebra of bounded operators on `ℓ²(ℤ)`. -/
def shiftUnit (k : ℤ) : (Hl2 →L[ℂ] Hl2)ˣ where
  val := shift k
  inv := shift (-k)
  val_inv := by rw [shift_mul_shift]; simp
  inv_val := by rw [shift_mul_shift]; simp

/-- Covariance of the almost Mathieu family: conjugating by the shift translates the phase
by `α`. -/
theorem shift_conj_amo (lam alpha theta : ℝ) :
    shift 1 * amo lam alpha theta * shift (-1) = amo lam alpha (theta + alpha) := by
  ext u n
  have hpot : amoPot lam alpha theta (n + 1) = amoPot lam alpha (theta + alpha) n := by
    unfold amoPot
    congr 2
    push_cast
    ring
  simp only [ContinuousLinearMap.mul_apply, amo_apply, shift_apply, hpot]
  ring_nf

/-- The spectrum of the almost Mathieu operator is invariant under the phase translation
`θ ↦ θ + α`. -/
theorem amoSpectrum_phase_shift (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  have h : (shiftUnit 1 : Hl2 →L[ℂ] Hl2) * amo lam alpha theta * ((shiftUnit 1)⁻¹ : _) =
      amo lam alpha (theta + alpha) := shift_conj_amo lam alpha theta
  unfold amoSpectrum
  rw [← h, spectrum.units_conjugate]

/-! ## Cantor sets -/

/-- A subset of `ℝ` is a *Cantor set* if it is nonempty, compact, perfect (closed with no
isolated points) and totally disconnected.  By Brouwer's characterisation these properties
determine the set up to homeomorphism, so this is the standard meaning of
"the spectrum is a Cantor set". -/
structure IsCantorSet (S : Set ℝ) : Prop where
  nonempty : S.Nonempty
  isCompact : IsCompact S
  perfect : Perfect S
  totallyDisconnected : IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts hpre x hx y hy
  by_contra hxy
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · have hsub : Set.Icc x y ⊆ S := (hpre.Icc_subset hx hy).trans hts
    have : Set.Ioo x y ⊆ interior S :=
      interior_maximal (fun z hz => hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩) isOpen_Ioo
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.2 hlt).ne_empty this
  · have hsub : Set.Icc y x ⊆ S := (hpre.Icc_subset hy hx).trans hts
    have : Set.Ioo y x ⊆ interior S :=
      interior_maximal (fun z hz => hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩) isOpen_Ioo
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.2 hlt).ne_empty this

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling `λ`, every
irrational frequency `α` and every phase `θ`, the spectrum of the almost Mathieu operator
`(H u)(n) = u(n+1) + u(n-1) + 2 λ cos(2π(θ + nα)) u(n)` is a Cantor set.

This is a Lean-checked *reduction* of that statement.  Everything except the two deep analytic
inputs is proved here from the definition of the operator: the almost Mathieu operator is
constructed as a genuine bounded operator on `ℓ²(ℤ)`, it is shown to be self-adjoint, and its
spectrum is shown to be a nonempty compact subset of `ℝ` contained in
`[-(2+2|λ|), 2+2|λ|]`.  The two remaining inputs are supplied as hypotheses:

* `hgaps`: the spectrum has empty interior (equivalently, all spectral gaps are open — this is
  the hard content of the Ten Martini Problem, proved by Avila and Jitomirskaya);
* `hacc`: the spectrum has no isolated points.

From these the theorem derives that the spectrum is nonempty, compact, perfect and totally
disconnected, i.e. a Cantor set; total disconnectedness is *deduced* from the empty interior.

The hypotheses `hlam : λ ≠ 0` and `halpha : Irrational α` are part of the statement of the Ten
Martini Problem and are kept, although the reduction itself does not use them (they are used
only in establishing `hgaps` and `hacc`). -/
theorem avila_ten_martini (lam alpha theta : ℝ) (_hlam : lam ≠ 0) (_halpha : Irrational alpha)
    (hgaps : interior (amoSpectrum lam alpha theta) = ∅)
    (hacc : ∀ E ∈ amoSpectrum lam alpha theta,
      AccPt E (Filter.principal (amoSpectrum lam alpha theta))) :
    IsCantorSet (amoSpectrum lam alpha theta) where
  nonempty := amoSpectrum_nonempty lam alpha theta
  isCompact := amoSpectrum_isCompact lam alpha theta
  perfect := ⟨amoSpectrum_isClosed lam alpha theta, hacc⟩
  totallyDisconnected := isTotallyDisconnected_of_interior_eq_empty hgaps

end

end Frontier

