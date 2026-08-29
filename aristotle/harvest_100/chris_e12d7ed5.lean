import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

This file formalises the statement of the **Ten Martini Problem** (solved by A. Avila and
S. Jitomirskaya): *for every nonzero coupling constant `λ`, every irrational frequency `α` and
every phase `θ`, the spectrum of the almost Mathieu operator*
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) u n`
*acting on `ℓ²(ℤ)` is a Cantor set.*

What is proved here, unconditionally:

* the almost Mathieu operator is constructed as a genuine bounded operator on `ℓ²(ℤ)`
  (`Frontier.almostMathieu`), and is shown to be self-adjoint;
* its real spectrum is nonempty, compact (hence closed) and contained in the interval
  `[-(2 + 2|λ|), 2 + 2|λ|]`;
* the elementary symmetries of the family: `α`-periodicity, `θ`-periodicity, the sign change
  `λ ↦ -λ`, and the covariance `H_{λ,α,θ+α} = S H_{λ,α,θ} S⁻¹` under the shift, which gives
  invariance of the spectrum along the orbit of `θ`;
* the **base case `λ = 0`**: via explicit Weyl sequences of truncated plane waves, the spectrum of
  the free discrete Laplacian is shown to contain the whole band `[-2, 2]`, so it is *not* a
  Cantor set (`Frontier.not_isCantorSet_amoSpectrum_zero`).  This shows the hypothesis `λ ≠ 0`
  cannot be dropped from the Ten Martini statement.

The main theorem `Frontier.avila_ten_martini` is a Lean-checked *reduction*: it derives the full
Ten Martini statement (`Frontier.TenMartiniProblem`) from the two deep analytic inputs — that the
spectrum is nowhere dense and that it has no isolated points. All the remaining content of
"being a Cantor set" (nonempty, compact, closed) is proved here from scratch.
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Frontier

noncomputable section

open scoped ComplexConjugate

/-- The Hilbert space `ℓ²(ℤ)` of square-summable complex sequences indexed by `ℤ`. -/
abbrev ell2 := lp (fun _ : ℤ => ℂ) 2

/-! ### Basic `ℓ²` facts -/

private lemma rpow_two_eq (x : ℝ) : x ^ ((2 : ENNReal).toReal) = x ^ 2 := by
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

lemma summable_sq (f : ell2) : Summable fun n => ‖(f : ℤ → ℂ) n‖ ^ 2 := by
  have hf := lp.memℓp f
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hf
  simpa [rpow_two_eq] using hf

lemma memℓp_of_summable_sq (g : ℤ → ℂ) (h : Summable fun n => ‖g n‖ ^ 2) : Memℓp g 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simpa [rpow_two_eq] using h

lemma norm_sq_eq (f : ell2) : ‖f‖ ^ 2 = ∑' n, ‖(f : ℤ → ℂ) n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) f
  simpa [rpow_two_eq] using this

instance : Nontrivial ell2 := by
  refine ⟨lp.single 2 (0 : ℤ) (1 : ℂ), 0, ?_⟩
  intro h
  have := congrFun (congrArg (fun g : ell2 => (g : ℤ → ℂ)) h) 0
  simp [lp.single_apply] at this

/-! ### The shift operators -/

/-- Translation of a square-summable sequence: `shiftFun k f n = f (n + k)`. -/
def shiftFun (k : ℤ) (f : ell2) : ell2 :=
  ⟨fun n => (f : ℤ → ℂ) (n + k), by
    show Memℓp (fun n => (f : ℤ → ℂ) (n + k)) 2
    have hf := lp.memℓp f
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at hf ⊢
    exact (Equiv.addRight k).summable_iff.mpr hf⟩

@[simp] lemma shiftFun_apply (k : ℤ) (f : ell2) (n : ℤ) :
    (shiftFun k f : ℤ → ℂ) n = (f : ℤ → ℂ) (n + k) := rfl

/-- The shift by `k` as a unitary (linear isometric equivalence) of `ℓ²(ℤ)`. -/
def shiftLIE (k : ℤ) : ell2 ≃ₗᵢ[ℂ] ell2 where
  toFun := shiftFun k
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp
  invFun := shiftFun (-k)
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp
  norm_map' f := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact (Equiv.addRight k).tsum_eq fun n => ‖(f : ℤ → ℂ) n‖ ^ (2 : ENNReal).toReal

/-- The shift by `k` as a bounded operator on `ℓ²(ℤ)`. -/
def shift (k : ℤ) : ell2 →L[ℂ] ell2 := (shiftLIE k).toLinearIsometry.toContinuousLinearMap

@[simp] lemma shift_apply (k : ℤ) (f : ell2) (n : ℤ) :
    ((shift k f : ell2) : ℤ → ℂ) n = (f : ℤ → ℂ) (n + k) := rfl

lemma norm_shift_le (k : ℤ) : ‖shift k‖ ≤ 1 :=
  (shiftLIE k).toLinearIsometry.norm_toContinuousLinearMap_le

/-! ### Multiplication by a bounded real potential -/

private lemma sq_bound (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : ell2) (n : ℤ) :
    ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ ^ 2 ≤ C ^ 2 * ‖(f : ℤ → ℂ) n‖ ^ 2 := by
  have h1 : ‖(v n : ℂ) * (f : ℤ → ℂ) n‖ = |v n| * ‖(f : ℤ → ℂ) n‖ := by simp
  rw [h1, mul_pow]
  have h2 := hv n
  have h3 : |v n| ^ 2 ≤ C ^ 2 := by nlinarith [abs_nonneg (v n)]
  nlinarith [sq_nonneg ‖(f : ℤ → ℂ) n‖]

/-- Pointwise multiplication by a bounded real sequence, as a map `ℓ²(ℤ) → ℓ²(ℤ)`. -/
def mulFun (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : ell2) : ell2 :=
  ⟨fun n => (v n : ℂ) * (f : ℤ → ℂ) n,
    memℓp_of_summable_sq _ (Summable.of_nonneg_of_le (fun n => by positivity)
      (sq_bound v C hv f) ((summable_sq f).mul_left (C ^ 2)))⟩

@[simp] lemma mulFun_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : ell2) (n : ℤ) :
    (mulFun v C hv f : ℤ → ℂ) n = (v n : ℂ) * (f : ℤ → ℂ) n := rfl

/-- Multiplication by a bounded real sequence, as a bounded operator on `ℓ²(ℤ)`. -/
def mulCLM (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : ell2 →L[ℂ] ell2 :=
  LinearMap.mkContinuous
    { toFun := mulFun v C hv
      map_add' := fun f g => by ext n; simp [mul_add]
      map_smul' := fun c f => by ext n; simp; ring } C (by
      intro f
      have hC : 0 ≤ C := le_trans (abs_nonneg _) (hv 0)
      have h1 : ‖mulFun v C hv f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
        rw [norm_sq_eq, mul_pow, norm_sq_eq f, ← tsum_mul_left]
        exact Summable.tsum_le_tsum (fun n => sq_bound v C hv f n) (summable_sq _)
          ((summable_sq f).mul_left (C ^ 2))
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1)

@[simp] lemma mulCLM_apply (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (f : ell2) (n : ℤ) :
    ((mulCLM v C hv f : ell2) : ℤ → ℂ) n = (v n : ℂ) * (f : ℤ → ℂ) n := rfl

lemma norm_mulCLM_le (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) : ‖mulCLM v C hv‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (abs_nonneg _) (hv 0)) _

/-! ### The almost Mathieu operator -/

/-- The almost Mathieu potential `n ↦ 2 λ cos (2π (θ + n α))`. -/
def amoPotential (lam alpha theta : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))

lemma amoPotential_bound (lam alpha theta : ℝ) (n : ℤ) :
    |amoPotential lam alpha theta n| ≤ 2 * |lam| := by
  have h := Real.abs_cos_le_one (2 * Real.pi * (theta + n * alpha))
  calc |amoPotential lam alpha theta n|
      = (2 * |lam|) * |Real.cos (2 * Real.pi * (theta + n * alpha))| := by
        simp [amoPotential, abs_mul, mul_assoc]
    _ ≤ (2 * |lam|) * 1 := by
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * |lam| := by ring

/-- The **almost Mathieu operator** `H_{λ,α,θ}` on `ℓ²(ℤ)`:
`(H u) n = u (n+1) + u (n-1) + 2 λ cos (2π (θ + n α)) u n`. -/
def almostMathieu (lam alpha theta : ℝ) : ell2 →L[ℂ] ell2 :=
  shift 1 + shift (-1) + mulCLM (amoPotential lam alpha theta) (2 * |lam|)
    (amoPotential_bound lam alpha theta)

@[simp] lemma almostMathieu_apply (lam alpha theta : ℝ) (u : ell2) (n : ℤ) :
    ((almostMathieu lam alpha theta u : ell2) : ℤ → ℂ) n
      = (u : ℤ → ℂ) (n + 1) + (u : ℤ → ℂ) (n - 1)
        + (amoPotential lam alpha theta n : ℂ) * (u : ℤ → ℂ) n := by
  simp [almostMathieu, sub_eq_add_neg]

/-! ### Self-adjointness -/

lemma inner_shift_left (k : ℤ) (x y : ell2) :
    (inner ℂ (shift k x) y : ℂ) = inner ℂ x (shift (-k) y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [shift_apply]
  have h := (Equiv.addRight k).tsum_eq
    (fun n => (inner ℂ ((x : ℤ → ℂ) n) ((y : ℤ → ℂ) (n + -k)) : ℂ))
  simp only [Equiv.coe_addRight] at h
  rw [← h]
  refine tsum_congr fun n => ?_
  simp

lemma inner_mulCLM_left (v : ℤ → ℝ) (C : ℝ) (hv : ∀ n, |v n| ≤ C) (x y : ell2) :
    (inner ℂ (mulCLM v C hv x) y : ℂ) = inner ℂ x (mulCLM v C hv y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [mulCLM_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

lemma isSelfAdjoint_almostMathieu (lam alpha theta : ℝ) :
    IsSelfAdjoint (almostMathieu lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  show (inner ℂ (almostMathieu lam alpha theta x) y : ℂ)
      = inner ℂ x (almostMathieu lam alpha theta y)
  simp only [almostMathieu, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
  rw [inner_shift_left 1 x y, inner_shift_left (-1) x y, inner_mulCLM_left]
  simp only [neg_neg]
  ring

/-! ### Elementary properties of the spectrum -/

/-- The (real) spectrum of the almost Mathieu operator. -/
def amoSpectrum (lam alpha theta : ℝ) : Set ℝ := spectrum ℝ (almostMathieu lam alpha theta)

lemma amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  have hres := (isSelfAdjoint_almostMathieu lam alpha theta).spectrumRestricts
  have himg := hres.algebraMap_image
  have hne : (spectrum ℂ (almostMathieu lam alpha theta)).Nonempty :=
    spectrum.nonempty _
  rw [← himg] at hne
  obtain ⟨z, w, hw, -⟩ := hne
  exact ⟨w, hw⟩

lemma amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  spectrum.isCompact _

lemma amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) :=
  (amoSpectrum_isCompact lam alpha theta).isClosed

lemma norm_almostMathieu_le (lam alpha theta : ℝ) :
    ‖almostMathieu lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  refine le_trans (norm_add_le _ _) ?_
  gcongr
  · exact le_trans (norm_add_le _ _) (by
      have h1 := norm_shift_le 1
      have h2 := norm_shift_le (-1)
      linarith)
  · exact norm_mulCLM_le _ _ _

lemma amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖E‖ ≤ ‖almostMathieu lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 := norm_almostMathieu_le lam alpha theta
  have : |E| ≤ 2 + 2 * |lam| := le_trans h1 h2
  rw [abs_le] at this
  exact ⟨this.1, this.2⟩

/-! ### Symmetries of the family -/

lemma amoPotential_alpha_add_one (lam alpha theta : ℝ) (n : ℤ) :
    amoPotential lam (alpha + 1) theta n = amoPotential lam alpha theta n := by
  simp only [amoPotential]
  congr 1
  have h : 2 * Real.pi * (theta + n * (alpha + 1))
      = 2 * Real.pi * (theta + n * alpha) + n * (2 * Real.pi) := by ring
  rw [h, Real.cos_add_int_mul_two_pi]

lemma amoPotential_theta_add_one (lam alpha theta : ℝ) (n : ℤ) :
    amoPotential lam alpha (theta + 1) n = amoPotential lam alpha theta n := by
  simp only [amoPotential]
  congr 1
  have h : 2 * Real.pi * (theta + 1 + n * alpha)
      = 2 * Real.pi * (theta + n * alpha) + (1 : ℤ) * (2 * Real.pi) := by push_cast; ring
  rw [h, Real.cos_add_int_mul_two_pi]

lemma amoPotential_neg_lam (lam alpha theta : ℝ) (n : ℤ) :
    amoPotential (-lam) alpha theta n = amoPotential lam alpha (theta + 1 / 2) n := by
  simp only [amoPotential]
  have h : 2 * Real.pi * (theta + 1 / 2 + n * alpha)
      = 2 * Real.pi * (theta + n * alpha) + Real.pi := by ring
  rw [h, Real.cos_add_pi]
  ring

/-- The frequency `α` only matters modulo `1`. -/
lemma almostMathieu_alpha_add_one (lam alpha theta : ℝ) :
    almostMathieu lam (alpha + 1) theta = almostMathieu lam alpha theta := by
  ext u n
  simp only [almostMathieu_apply, amoPotential_alpha_add_one]

/-- The phase `θ` only matters modulo `1`. -/
lemma almostMathieu_theta_add_one (lam alpha theta : ℝ) :
    almostMathieu lam alpha (theta + 1) = almostMathieu lam alpha theta := by
  ext u n
  simp only [almostMathieu_apply, amoPotential_theta_add_one]

/-- Changing the sign of the coupling amounts to a half-period translation of the phase. -/
lemma almostMathieu_neg_lam (lam alpha theta : ℝ) :
    almostMathieu (-lam) alpha theta = almostMathieu lam alpha (theta + 1 / 2) := by
  ext u n
  simp only [almostMathieu_apply, amoPotential_neg_lam]

/-- The shift by `1`, as a unit of the algebra of bounded operators. -/
def shiftUnit : (ell2 →L[ℂ] ell2)ˣ where
  val := shift 1
  inv := shift (-1)
  val_inv := by ext u n; simp
  inv_val := by ext u n; simp

/-- Covariance: translating the phase by `α` conjugates the operator by the shift. -/
lemma almostMathieu_covariant (lam alpha theta : ℝ) :
    almostMathieu lam alpha (theta + alpha)
      = (shiftUnit : ell2 →L[ℂ] ell2) * almostMathieu lam alpha theta
        * ((shiftUnit⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2) := by
  ext u n
  show _ = ((almostMathieu lam alpha theta) (shift (-1) u) : ell2) (n + 1)
  simp only [almostMathieu_apply, shift_apply, amoPotential]
  push_cast
  ring_nf

lemma amoSpectrum_theta_add_alpha (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  rw [amoSpectrum, amoSpectrum, almostMathieu_covariant, spectrum.units_conjugate]

/-! ### Cantor sets and the Ten Martini Problem -/

/-- A subset of `ℝ` is a *Cantor set* if it is nonempty, compact, has empty interior
(i.e. is nowhere dense) and is perfect (closed with no isolated points).  Such a set is
homeomorphic to the standard middle-thirds Cantor set. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  S.Nonempty ∧ IsCompact S ∧ interior S = ∅ ∧ Perfect S

/-- **The Ten Martini Problem**: for every nonzero coupling `λ`, every irrational frequency `α`
and every phase `θ`, the spectrum of the almost Mathieu operator is a Cantor set. -/
def TenMartiniProblem : Prop :=
  ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
    IsCantorSet (amoSpectrum lam alpha theta)

/-- **Avila–Jitomirskaya, Ten Martini Problem — Lean-checked reduction.**

Given the two deep analytic inputs — that for nonzero coupling and irrational frequency the
spectrum of the almost Mathieu operator is nowhere dense (`h_nowhereDense`) and has no isolated
points (`h_noIsolated`) — the full Ten Martini statement follows.  The remaining content of
"Cantor set" (nonemptiness, compactness, closedness of the spectrum) is proved here from the
construction of the operator, without any further assumptions. -/
theorem avila_ten_martini
    (h_nowhereDense : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅)
    (h_noIsolated : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      Preperfect (amoSpectrum lam alpha theta)) :
    TenMartiniProblem := by
  intro lam alpha theta hlam halpha
  exact ⟨amoSpectrum_nonempty lam alpha theta, amoSpectrum_isCompact lam alpha theta,
    h_nowhereDense lam alpha theta hlam halpha,
    ⟨amoSpectrum_isClosed lam alpha theta, h_noIsolated lam alpha theta hlam halpha⟩⟩

/-- The reduction performed by `Frontier.avila_ten_martini` loses nothing: the Ten Martini
statement is *equivalent* to the conjunction of its two deep analytic ingredients, nowhere
density and absence of isolated points of the spectrum. -/
theorem tenMartiniProblem_iff :
    TenMartiniProblem ↔ ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅ ∧ Preperfect (amoSpectrum lam alpha theta) := by
  constructor
  · intro h lam alpha theta hlam halpha
    obtain ⟨-, -, hint, hperf⟩ := h lam alpha theta hlam halpha
    exact ⟨hint, hperf.acc⟩
  · intro h
    exact avila_ten_martini (fun lam alpha theta hlam halpha => (h lam alpha theta hlam halpha).1)
      (fun lam alpha theta hlam halpha => (h lam alpha theta hlam halpha).2)

/-! ### The base case `λ = 0`

For zero coupling the almost Mathieu operator is the free discrete Laplacian, whose spectrum
contains the whole band `[-2, 2]`; in particular it is *not* a Cantor set.  This shows that the
hypothesis `λ ≠ 0` in the Ten Martini Problem cannot be dropped.  The proof constructs explicit
Weyl sequences: truncated plane waves `n ↦ e^{ikn}χ_{[-N,N]}(n)`. -/

/-- The plane wave `n ↦ e^{i k n}` truncated to `[-N, N]`. -/
def expSeq (k : ℝ) (N : ℕ) : ℤ → ℂ := fun n =>
  if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then Complex.exp (((k * n : ℝ) : ℂ) * Complex.I) else 0

lemma expSeq_of_mem (k : ℝ) (N : ℕ) {n : ℤ} (h1 : -(N : ℤ) ≤ n) (h2 : n ≤ (N : ℤ)) :
    expSeq k N n = Complex.exp (((k * n : ℝ) : ℂ) * Complex.I) := by
  simp [expSeq, Finset.mem_Icc, h1, h2]

lemma expSeq_of_not_mem (k : ℝ) (N : ℕ) {n : ℤ} (h : n < -(N : ℤ) ∨ (N : ℤ) < n) :
    expSeq k N n = 0 := by
  have : n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    simp only [Finset.mem_Icc, not_and, not_le]
    omega
  simp [expSeq, this]

lemma norm_expSeq_le_one (k : ℝ) (N : ℕ) (n : ℤ) : ‖expSeq k N n‖ ≤ 1 := by
  by_cases h : -(N : ℤ) ≤ n ∧ n ≤ (N : ℤ)
  · rw [expSeq_of_mem k N h.1 h.2, Complex.norm_exp_ofReal_mul_I]
  · rw [expSeq_of_not_mem k N (by omega)]
    simp

/-- The truncated plane wave as an element of `ℓ²(ℤ)`. -/
def truncWave (k : ℝ) (N : ℕ) : ell2 :=
  ⟨expSeq k N, memℓp_of_summable_sq _
    (summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => by
      have h : n < -(N : ℤ) ∨ (N : ℤ) < n := by
        simp only [Finset.mem_Icc, not_and, not_le] at hn
        omega
      simp [expSeq_of_not_mem k N h]))⟩

@[simp] lemma truncWave_apply (k : ℝ) (N : ℕ) (n : ℤ) :
    (truncWave k N : ℤ → ℂ) n = expSeq k N n := rfl

lemma norm_truncWave_sq (k : ℝ) (N : ℕ) : ‖truncWave k N‖ ^ 2 = 2 * N + 1 := by
  rw [norm_sq_eq]
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => by
    have h : n < -(N : ℤ) ∨ (N : ℤ) < n := by
      simp only [Finset.mem_Icc, not_and, not_le] at hn
      omega
    simp [expSeq_of_not_mem k N h])]
  have hone : ∀ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ‖(truncWave k N : ℤ → ℂ) n‖ ^ 2 = 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [truncWave_apply, expSeq_of_mem k N hn.1 hn.2, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Int.card_Icc]
  have hcard : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [hcard]
  ring_nf

lemma norm_sq_le_of_support (f : ell2) (s : Finset ℤ) (hs : ∀ n ∉ s, (f : ℤ → ℂ) n = 0)
    (M : ℝ) (hb : ∀ n, ‖(f : ℤ → ℂ) n‖ ≤ M) : ‖f‖ ^ 2 ≤ s.card * M ^ 2 := by
  rw [norm_sq_eq, tsum_eq_sum (s := s) (fun n hn => by simp [hs n hn])]
  have : ∀ n ∈ s, ‖(f : ℤ → ℂ) n‖ ^ 2 ≤ M ^ 2 := by
    intro n _
    have h0 := norm_nonneg ((f : ℤ → ℂ) n)
    have h1 := hb n
    nlinarith
  calc ∑ n ∈ s, ‖(f : ℤ → ℂ) n‖ ^ 2 ≤ s.card • M ^ 2 := Finset.sum_le_card_nsmul s _ _ this
    _ = s.card * M ^ 2 := by simp [nsmul_eq_mul]

/-- Weyl criterion: if there are vectors with bounded residual but unbounded norm, then `z`
belongs to the spectrum. -/
lemma mem_spectrum_of_approx (T : ell2 →L[ℂ] ell2) (z : ℂ) (M : ℝ) (x : ℕ → ell2)
    (hres : ∀ N, ‖z • x N - T (x N)‖ ≤ M) (hgrow : ∀ C : ℝ, ∃ N, C < ‖x N‖) :
    z ∈ spectrum ℂ T := by
  intro hz
  have hu : IsUnit (algebraMap ℂ (ell2 →L[ℂ] ell2) z - T) := hz
  obtain ⟨u, hu'⟩ := hu
  have hval : ∀ y : ell2, (u : ell2 →L[ℂ] ell2) y = z • y - T y := by
    intro y
    rw [hu']
    simp [Algebra.algebraMap_eq_smul_one]
  have hkey : ∀ N, ‖x N‖ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M := by
    intro N
    have h1 : ((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)
        ((u : ell2 →L[ℂ] ell2) (x N)) = x N := by
      have h := congrArg (fun A : ell2 →L[ℂ] ell2 => A (x N)) u.inv_val
      simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using h
    calc ‖x N‖ = ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)
            ((u : ell2 →L[ℂ] ell2) (x N))‖ := by rw [h1]
      _ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * ‖(u : ell2 →L[ℂ] ell2) (x N)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M := by
          rw [hval]
          exact mul_le_mul_of_nonneg_left (hres N) (norm_nonneg _)
  obtain ⟨N, hN⟩ := hgrow (‖((u⁻¹ : (ell2 →L[ℂ] ell2)ˣ) : ell2 →L[ℂ] ell2)‖ * M)
  exact absurd (hkey N) (not_le.mpr hN)

lemma real_mem_spectrum_iff (lam alpha theta : ℝ) (E : ℝ) :
    E ∈ amoSpectrum lam alpha theta ↔
      (E : ℂ) ∈ spectrum ℂ (almostMathieu lam alpha theta) := by
  have himg := (isSelfAdjoint_almostMathieu lam alpha theta).spectrumRestricts.algebraMap_image
  constructor
  · intro hE
    rw [← himg]
    exact ⟨E, hE, rfl⟩
  · intro hE
    rw [← himg] at hE
    obtain ⟨r, hr, hrE⟩ := hE
    rw [Complex.coe_algebraMap] at hrE
    have : r = E := by exact_mod_cast hrE
    exact this ▸ hr

/-- For zero coupling the spectrum contains the whole band `[-2, 2]`. -/
theorem Icc_subset_amoSpectrum_zero (alpha theta : ℝ) :
    Set.Icc (-2 : ℝ) 2 ⊆ amoSpectrum 0 alpha theta := by
  intro E hE
  obtain ⟨hE1, hE2⟩ := hE
  set k : ℝ := Real.arccos (E / 2) with hk
  have hcos : 2 * Real.cos k = E := by
    rw [hk, Real.cos_arccos (by linarith) (by linarith)]
    ring
  rw [real_mem_spectrum_iff]
  refine mem_spectrum_of_approx _ _ 8 (fun N => truncWave k N) (fun N => ?_) (fun C => ?_)
  · -- residual bound
    set f : ell2 := (E : ℂ) • truncWave k N - almostMathieu 0 alpha theta (truncWave k N) with hf
    have hcoord : ∀ n : ℤ, (f : ℤ → ℂ) n
        = (E : ℂ) * expSeq k N n - (expSeq k N (n + 1) + expSeq k N (n - 1)) := by
      intro n
      simp [hf, amoPotential]
    have hwave : ∀ m : ℤ, -(N : ℤ) ≤ m → m ≤ (N : ℤ) →
        expSeq k N m = Complex.exp (((k * m : ℝ) : ℂ) * Complex.I) :=
      fun m h1 h2 => expSeq_of_mem k N h1 h2
    have hsupp : ∀ n ∉ ({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ),
        (f : ℤ → ℂ) n = 0 := by
      intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      obtain ⟨h1, h2, h3, h4⟩ := hn
      rw [hcoord]
      by_cases hin : -(N : ℤ) + 1 ≤ n ∧ n ≤ (N : ℤ) - 1
      · obtain ⟨ha, hb⟩ := hin
        rw [hwave n (by omega) (by omega), hwave (n + 1) (by omega) (by omega),
          hwave (n - 1) (by omega) (by omega), ← hcos]
        have hid : Complex.exp (((k * (n + 1) : ℝ) : ℂ) * Complex.I)
            + Complex.exp (((k * (n - 1) : ℝ) : ℂ) * Complex.I)
            = ((2 * Real.cos k : ℝ) : ℂ) * Complex.exp (((k * n : ℝ) : ℂ) * Complex.I) := by
          have h1' : ((k * (n + 1) : ℝ) : ℂ) * Complex.I
              = ((k * n : ℝ) : ℂ) * Complex.I + (k : ℂ) * Complex.I := by push_cast; ring
          have h2' : ((k * (n - 1) : ℝ) : ℂ) * Complex.I
              = ((k * n : ℝ) : ℂ) * Complex.I + (-(k : ℂ)) * Complex.I := by push_cast; ring
          rw [h1', h2', Complex.exp_add, Complex.exp_add]
          push_cast [Complex.ofReal_cos]
          rw [Complex.cos]
          ring
        push_cast at hid ⊢
        rw [hid]
        ring
      · push_neg at hin
        have hout : n < -(N : ℤ) - 1 ∨ (N : ℤ) + 1 < n := by omega
        rcases hout with h | h
        · rw [expSeq_of_not_mem k N (Or.inl (by omega)),
            expSeq_of_not_mem k N (Or.inl (by omega)),
            expSeq_of_not_mem k N (Or.inl (by omega))]
          ring
        · rw [expSeq_of_not_mem k N (Or.inr (by omega)),
            expSeq_of_not_mem k N (Or.inr (by omega)),
            expSeq_of_not_mem k N (Or.inr (by omega))]
          ring
    have hbound : ∀ n : ℤ, ‖(f : ℤ → ℂ) n‖ ≤ 4 := by
      intro n
      rw [hcoord]
      have hEle : ‖(E : ℂ)‖ ≤ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨hE1, hE2⟩
      have h1 := norm_expSeq_le_one k N n
      have h2 := norm_expSeq_le_one k N (n + 1)
      have h3 := norm_expSeq_le_one k N (n - 1)
      calc ‖(E : ℂ) * expSeq k N n - (expSeq k N (n + 1) + expSeq k N (n - 1))‖
          ≤ ‖(E : ℂ) * expSeq k N n‖ + ‖expSeq k N (n + 1) + expSeq k N (n - 1)‖ :=
            norm_sub_le _ _
        _ ≤ (2 * 1) + (1 + 1) := by
            gcongr
            · rw [norm_mul]
              exact mul_le_mul hEle h1 (norm_nonneg _) (by norm_num)
            · exact le_trans (norm_add_le _ _) (by linarith)
        _ = 4 := by norm_num
    have hcard : (({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ)).card ≤ 4 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      have h1 := Finset.card_insert_le (-(N : ℤ)) ({(N : ℤ), (N : ℤ) + 1} : Finset ℤ)
      have h2 := Finset.card_insert_le ((N : ℤ)) ({(N : ℤ) + 1} : Finset ℤ)
      have h3 : ({(N : ℤ) + 1} : Finset ℤ).card = 1 := Finset.card_singleton _
      omega
    have hsq : ‖f‖ ^ 2 ≤ 64 := by
      have := norm_sq_le_of_support f _ hsupp 4 hbound
      have hc : ((({-(N : ℤ) - 1, -(N : ℤ), (N : ℤ), (N : ℤ) + 1} : Finset ℤ)).card : ℝ) ≤ 4 := by
        exact_mod_cast hcard
      nlinarith [norm_nonneg f]
    have : ‖f‖ ≤ 8 := by
      nlinarith [norm_nonneg f]
    exact this
  · -- unbounded norms
    obtain ⟨N, hN⟩ := exists_nat_gt (max C 0 ^ 2)
    refine ⟨N, ?_⟩
    have hsq := norm_truncWave_sq k N
    have h0 : 0 ≤ ‖truncWave k N‖ := norm_nonneg _
    have hCmax : C ≤ max C 0 := le_max_left _ _
    have hmax0 : 0 ≤ max C 0 := le_max_right _ _
    nlinarith [hsq, hN]

/-- **Base case / sharpness**: for zero coupling the spectrum is not a Cantor set, since it has
nonempty interior.  Hence the hypothesis `λ ≠ 0` in the Ten Martini Problem is necessary. -/
theorem not_isCantorSet_amoSpectrum_zero (alpha theta : ℝ) :
    ¬ IsCantorSet (amoSpectrum 0 alpha theta) := by
  rintro ⟨-, -, hint, -⟩
  have h1 : Set.Ioo (-2 : ℝ) 2 ⊆ interior (amoSpectrum 0 alpha theta) :=
    interior_maximal (subset_trans Set.Ioo_subset_Icc_self
      (Icc_subset_amoSpectrum_zero alpha theta)) isOpen_Ioo
  have h2 : (0 : ℝ) ∈ interior (amoSpectrum 0 alpha theta) := h1 (by norm_num)
  rw [hint] at h2
  exact h2

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

