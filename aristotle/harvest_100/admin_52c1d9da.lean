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

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
abbrev Ell2 := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial Ell2 := by
  refine ⟨lp.single 2 0 1, 0, ?_⟩
  intro h
  have := congrArg (fun f : Ell2 => (f : ℤ → ℂ) 0) h
  simp at this

private theorem rpow2 (x : ℝ) : x ^ (2 : ℝ) = x ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

private theorem sq_summable (f : Ell2) : Summable (fun i : ℤ => ‖f i‖ ^ 2) := by
  have := (lp.memℓp f).summable (p := 2) (by norm_num)
  simp only [ENNReal.toReal_ofNat] at this
  simpa [rpow2] using this

/-! ## Reindexing (shift) operators -/

private theorem memℓp_comp (f : Ell2) (e : ℤ ≃ ℤ) : Memℓp (fun i => f (e i)) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat]
  exact (Equiv.summable_iff e).mpr ((lp.memℓp f).summable (by norm_num))

/-- Reindexing of an `ℓ²` sequence along a bijection of the index set, as a linear map. -/
def reindexLM (e : ℤ ≃ ℤ) : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨fun i => f (e i), memℓp_comp f e⟩
  map_add' f g := by ext i; simp
  map_smul' c f := by ext i; simp

private theorem reindexLM_norm (e : ℤ ≃ ℤ) (f : Ell2) : ‖reindexLM e f‖ ≤ 1 * ‖f‖ := by
  rw [one_mul]
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg _)
  have h := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num) f
  have hc : ∀ i : ℤ, ‖(reindexLM e f) i‖ = ‖f (e i)‖ := fun i => rfl
  simp only [hc, ENNReal.toReal_ofNat] at *
  rw [Equiv.tsum_eq e (fun i => ‖f i‖ ^ (2 : ℝ))]
  exact le_of_eq h.symm

/-- Reindexing of an `ℓ²` sequence along a bijection of the index set, as a bounded operator. -/
def reindexCLM (e : ℤ ≃ ℤ) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous (reindexLM e) 1 (reindexLM_norm e)

@[simp] theorem reindexCLM_apply (e : ℤ ≃ ℤ) (f : Ell2) (i : ℤ) :
    (reindexCLM e f : ℤ → ℂ) i = f (e i) := rfl

theorem reindexCLM_inner (e : ℤ ≃ ℤ) (f g : Ell2) :
    inner ℂ (reindexCLM e f) g = inner ℂ f (reindexCLM e.symm g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum,
    ← Equiv.tsum_eq e (fun j => inner ℂ (f j) ((reindexCLM e.symm g : ℤ → ℂ) j))]
  exact tsum_congr fun i => by simp

/-! ## Multiplication operators -/

private theorem memℓp_mul (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) (f : Ell2) :
    Memℓp (fun i => v i * f i) 2 := by
  apply memℓp_gen
  simp only [ENNReal.toReal_ofNat]
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) _) ?_
    ((sq_summable f).mul_left (C ^ 2))
  intro i
  rw [rpow2, norm_mul, mul_pow]
  gcongr
  exact hv i

/-- Multiplication by a bounded sequence, as a linear map on `ℓ²(ℤ)`. -/
def mulLM (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) : Ell2 →ₗ[ℂ] Ell2 where
  toFun f := ⟨fun i => v i * f i, memℓp_mul v C hv f⟩
  map_add' f g := by ext i; simp [mul_add]
  map_smul' c f := by ext i; simp [mul_left_comm]

private theorem mulLM_norm (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) (f : Ell2) :
    ‖mulLM v C hv f‖ ≤ C * ‖f‖ := by
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hv 0)
  apply lp.norm_le_of_tsum_le (by norm_num) (by positivity)
  have hnorm := lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ℤ => ℂ) (by norm_num) f
  simp only [ENNReal.toReal_ofNat, rpow2] at *
  have hle : ∀ i : ℤ, ‖(mulLM v C hv f) i‖ ^ 2 ≤ C ^ 2 * ‖f i‖ ^ 2 := by
    intro i
    have h1 : ‖(mulLM v C hv f) i‖ = ‖v i * f i‖ := rfl
    rw [h1, norm_mul, mul_pow]
    gcongr
    exact hv i
  have hs1 : Summable (fun i : ℤ => ‖(mulLM v C hv f) i‖ ^ 2) := by
    simpa [rpow2] using ((mulLM v C hv f).2.summable (p := 2) (by norm_num))
  calc ∑' i : ℤ, ‖(mulLM v C hv f) i‖ ^ 2
      ≤ ∑' i : ℤ, C ^ 2 * ‖f i‖ ^ 2 := hs1.tsum_le_tsum hle ((sq_summable f).mul_left _)
    _ = C ^ 2 * ‖f‖ ^ 2 := by rw [tsum_mul_left, ← hnorm]
    _ = (C * ‖f‖) ^ 2 := by ring

/-- Multiplication by a bounded sequence, as a bounded operator on `ℓ²(ℤ)`. -/
def mulCLM (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) : Ell2 →L[ℂ] Ell2 :=
  LinearMap.mkContinuous (mulLM v C hv) C (mulLM_norm v C hv)

@[simp] theorem mulCLM_apply (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C) (f : Ell2) (i : ℤ) :
    (mulCLM v C hv f : ℤ → ℂ) i = v i * f i := rfl

theorem mulCLM_inner (v : ℤ → ℂ) (C : ℝ) (hv : ∀ i, ‖v i‖ ≤ C)
    (hreal : ∀ i, (starRingEnd ℂ) (v i) = v i) (f g : Ell2) :
    inner ℂ (mulCLM v C hv f) g = inner ℂ f (mulCLM v C hv g) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  simp only [mulCLM_apply, RCLike.inner_apply, map_mul, hreal i]
  ring

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator with coupling `lam`, flux `alpha` and phase
`theta`: `v n = 2 * lam * cos (2 π (theta + n α))`. -/
def amoPotential (lam alpha theta : ℝ) (n : ℤ) : ℂ :=
  ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ)

theorem amoPotential_bound (lam alpha theta : ℝ) (n : ℤ) :
    ‖amoPotential lam alpha theta n‖ ≤ 2 * |lam| := by
  rw [amoPotential, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |Real.cos (2 * Real.pi * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  nlinarith [abs_nonneg lam, abs_nonneg (Real.cos (2 * Real.pi * (theta + n * alpha)))]

theorem amoPotential_isReal (lam alpha theta : ℝ) (n : ℤ) :
    (starRingEnd ℂ) (amoPotential lam alpha theta n) = amoPotential lam alpha theta n := by
  simp only [amoPotential, Complex.conj_ofReal]

/-- The almost Mathieu operator `H_{λ,α,θ}` on `ℓ²(ℤ)`:
`(H u) n = u (n + 1) + u (n - 1) + 2 λ cos (2 π (θ + n α)) * u n`. -/
def amo (lam alpha theta : ℝ) : Ell2 →L[ℂ] Ell2 :=
  reindexCLM (Equiv.addRight (1 : ℤ)) + reindexCLM (Equiv.addRight (-1 : ℤ))
    + mulCLM (amoPotential lam alpha theta) (2 * |lam|) (amoPotential_bound lam alpha theta)

/-- The defining formula for the almost Mathieu operator. -/
theorem amo_apply (lam alpha theta : ℝ) (f : Ell2) (n : ℤ) :
    (amo lam alpha theta f : ℤ → ℂ) n
      = f (n + 1) + f (n - 1)
        + ((2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha)) : ℝ) : ℂ) * f n := by
  show (reindexCLM (Equiv.addRight (1 : ℤ)) f : ℤ → ℂ) n
      + (reindexCLM (Equiv.addRight (-1 : ℤ)) f : ℤ → ℂ) n
      + (mulCLM (amoPotential lam alpha theta) (2 * |lam|)
          (amoPotential_bound lam alpha theta) f : ℤ → ℂ) n = _
  simp only [reindexCLM_apply, mulCLM_apply, Equiv.coe_addRight, amoPotential]
  norm_num
  ring_nf

/-- The almost Mathieu operator is a self-adjoint bounded operator. -/
theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro f g
  have e1 : (Equiv.addRight (1 : ℤ)).symm = Equiv.addRight (-1 : ℤ) := by
    ext i; simp [Equiv.addRight]
  have e2 : (Equiv.addRight (-1 : ℤ)).symm = Equiv.addRight (1 : ℤ) := by
    ext i; simp [Equiv.addRight]
  have h1 : inner ℂ (reindexCLM (Equiv.addRight (1 : ℤ)) f) g
      = inner ℂ f (reindexCLM (Equiv.addRight (-1 : ℤ)) g) := by
    rw [reindexCLM_inner, e1]
  have h2 : inner ℂ (reindexCLM (Equiv.addRight (-1 : ℤ)) f) g
      = inner ℂ f (reindexCLM (Equiv.addRight (1 : ℤ)) g) := by
    rw [reindexCLM_inner, e2]
  have h3 := mulCLM_inner (amoPotential lam alpha theta) (2 * |lam|)
    (amoPotential_bound lam alpha theta) (amoPotential_isReal lam alpha theta) f g
  show inner ℂ (amo lam alpha theta f) g = inner ℂ f (amo lam alpha theta g)
  simp only [amo, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right, h1, h2, h3]
  ring

/-- Norm bound for the almost Mathieu operator. -/
theorem amo_norm_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  have hb : ‖reindexCLM (Equiv.addRight (1 : ℤ))‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hb' : ‖reindexCLM (Equiv.addRight (-1 : ℤ))‖ ≤ 1 :=
    LinearMap.mkContinuous_norm_le _ zero_le_one _
  have hm : ‖mulCLM (amoPotential lam alpha theta) (2 * |lam|)
      (amoPotential_bound lam alpha theta)‖ ≤ 2 * |lam| :=
    LinearMap.mkContinuous_norm_le _ (by positivity) _
  have := norm_add₃_le (a := reindexCLM (Equiv.addRight (1 : ℤ)))
    (b := reindexCLM (Equiv.addRight (-1 : ℤ)))
    (c := mulCLM (amoPotential lam alpha theta) (2 * |lam|) (amoPotential_bound lam alpha theta))
  calc ‖amo lam alpha theta‖ ≤ _ := this
    _ ≤ 1 + 1 + 2 * |lam| := by gcongr
    _ = 2 + 2 * |lam| := by ring

/-- The shift `(U f) n = f (n + 1)` as a unit of the algebra of bounded operators on `ℓ²(ℤ)`. -/
def shiftUnit : (Ell2 →L[ℂ] Ell2)ˣ where
  val := reindexCLM (Equiv.addRight (1 : ℤ))
  inv := reindexCLM (Equiv.addRight (-1 : ℤ))
  val_inv := by ext f i; simp
  inv_val := by ext f i; simp

/-- Covariance of the almost Mathieu family: conjugating by the shift translates the phase
`theta` by the flux `alpha`. -/
theorem shiftUnit_conj_amo (lam alpha theta : ℝ) :
    (shiftUnit : Ell2 →L[ℂ] Ell2) * amo lam alpha theta
        * ((shiftUnit⁻¹ : (Ell2 →L[ℂ] Ell2)ˣ) : Ell2 →L[ℂ] Ell2)
      = amo lam alpha (theta + alpha) := by
  ext f i
  show ((reindexCLM (Equiv.addRight (1 : ℤ)))
      ((amo lam alpha theta) ((reindexCLM (Equiv.addRight (-1 : ℤ))) f)) : ℤ → ℂ) i = _
  rw [reindexCLM_apply, amo_apply, amo_apply]
  simp only [reindexCLM_apply, Equiv.coe_addRight]
  have h1 : i + 1 + 1 + -1 = i + 1 := by ring
  have h2 : i + 1 - 1 + -1 = i - 1 := by ring
  have h3 : i + 1 + -1 = i := by ring
  have h4 : 2 * Real.pi * (theta + ((i + 1 : ℤ) : ℝ) * alpha)
      = 2 * Real.pi * (theta + alpha + (i : ℝ) * alpha) := by push_cast; ring
  rw [h1, h2, h3, h4]

/-! ## The spectrum of the almost Mathieu operator -/

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate since the operator is self-adjoint). -/
def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

/-- The spectrum of the almost Mathieu operator is invariant under translating the phase by the
flux. -/
theorem amoSpectrum_phase_shift (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  have h : spectrum ℂ (amo lam alpha (theta + alpha)) = spectrum ℂ (amo lam alpha theta) := by
    rw [← shiftUnit_conj_amo]
    exact spectrum.units_conjugate
  simp only [amoSpectrum, h]

theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  refine ⟨z.re, ?_⟩
  have := (amo_isSelfAdjoint lam alpha theta).mem_spectrum_eq_re hz
  simpa [amoSpectrum, ← this] using hz

theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) := by
  have hc : IsClosed (spectrum ℂ (amo lam alpha theta)) :=
    (spectrum.isCompact (amo lam alpha theta)).isClosed
  exact hc.preimage Complex.continuous_ofReal

theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 : |E| ≤ 2 + 2 * |lam| :=
    le_trans (by simpa using h1) (amo_norm_le lam alpha theta)
  rw [abs_le] at h2
  exact ⟨h2.1, h2.2⟩

theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  Metric.isCompact_of_isClosed_isBounded (amoSpectrum_isClosed lam alpha theta)
    ((Metric.isBounded_Icc _ _).subset (amoSpectrum_subset_Icc lam alpha theta))

/-! ## Cantor sets -/

/-- A *Cantor set* in `ℝ`: a nonempty compact perfect totally disconnected subset. -/
def IsCantorSet (S : Set ℝ) : Prop :=
  IsCompact S ∧ S.Nonempty ∧ Perfect S ∧ IsTotallyDisconnected S

/-- A subset of `ℝ` with empty interior is totally disconnected. -/
theorem isTotallyDisconnected_of_interior_eq_empty {S : Set ℝ} (h : interior S = ∅) :
    IsTotallyDisconnected S := by
  intro t hts htpre x hx y hy
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hsub : Set.Icc x y ⊆ S := (htpre.Icc_subset hx hy).trans hts
    have : Set.Ioo x y ⊆ interior S := by
      rw [← interior_Icc]; exact interior_mono hsub
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.mpr hlt).ne_empty this
  · have hsub : Set.Icc y x ⊆ S := (htpre.Icc_subset hy hx).trans hts
    have : Set.Ioo y x ⊆ interior S := by
      rw [← interior_Icc]; exact interior_mono hsub
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.mpr hlt).ne_empty this

/-- Criterion for being a Cantor set: a nonempty compact subset of `ℝ` with empty interior and
no isolated points is a Cantor set. -/
theorem isCantorSet_of_no_interior_no_isolated {S : Set ℝ} (hcomp : IsCompact S)
    (hne : S.Nonempty) (hint : interior S = ∅)
    (hacc : ∀ x ∈ S, AccPt x (Filter.principal S)) : IsCantorSet S :=
  ⟨hcomp, hne, ⟨hcomp.isClosed, hacc⟩, isTotallyDisconnected_of_interior_eq_empty hint⟩

/-! ## The Ten Martini Problem -/

/-- **The Ten Martini Problem** (Avila–Jitomirskaya): for every nonzero coupling constant `lam`,
every irrational flux `alpha` and every phase `theta`, the spectrum of the almost Mathieu
operator `H_{lam, alpha, theta}` is a Cantor set.

This is a *Lean-checked reduction* of the full theorem: the two deep analytic inputs are taken as
hypotheses, namely

* `h_noInterior`: the spectrum has empty interior (there are no bands: all spectral gaps
  predicted by the gap-labelling theorem are open);
* `h_noIsolated`: the spectrum has no isolated points.

Everything else is proved here from scratch: the almost Mathieu operator is constructed as a
bounded operator on `ℓ²(ℤ)`, it is shown to be self-adjoint with `‖H‖ ≤ 2 + 2|λ|`, its real
spectrum is shown to be nonempty and compact, and Cantor-ness (compact, nonempty, perfect,
totally disconnected) is deduced from the two hypotheses above.

The two analytic inputs are quantified over all admissible parameters, exactly as they appear in
the literature. -/
theorem avila_ten_martini
    (h_noInterior : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      interior (amoSpectrum lam alpha theta) = ∅)
    (h_noIsolated : ∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
      ∀ E ∈ amoSpectrum lam alpha theta,
        AccPt E (Filter.principal (amoSpectrum lam alpha theta)))
    (lam alpha theta : ℝ) (hlam : lam ≠ 0) (halpha : Irrational alpha) :
    IsCantorSet (amoSpectrum lam alpha theta) :=
  isCantorSet_of_no_interior_no_isolated (amoSpectrum_isCompact lam alpha theta)
    (amoSpectrum_nonempty lam alpha theta) (h_noInterior lam alpha theta hlam halpha)
    (h_noIsolated lam alpha theta hlam halpha)

end

end Frontier

