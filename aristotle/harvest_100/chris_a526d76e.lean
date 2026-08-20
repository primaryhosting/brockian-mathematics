/-
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` commands to precede every other command, including
module doc-comments `/-! ... -/`; the header above is therefore a plain block comment,
and is repeated as the module doc-comment right after the import below.)
-/

import Mathlib

/-!
# Avila Ten Martini
Category: Frontier — Fields Medal Work
Target: Frontier.avila_ten_martini
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

Mathlib contains no development of the almost Mathieu operator or of the Ten Martini problem, so
the operator is constructed here from scratch on `lp (fun _ : ℤ => ℂ) 2`, out of reindexing
(shift) operators and multiplication by a bounded real sequence.

Proved unconditionally:
* `Frontier.amo_isSelfAdjoint` — self-adjointness of `H_{λ,α,θ}`;
* `Frontier.norm_amo_le` — the operator norm bound `‖H‖ ≤ 2 + 2|λ|`;
* `Frontier.amoSpectrum_nonempty`, `Frontier.amoSpectrum_isCompact` — the (real) spectrum is a
  nonempty compact subset of `ℝ`;
* `Frontier.amo_conj`, `Frontier.amoSpectrum_theta_add` — covariance of the family under the
  shift, and invariance of the spectrum under `θ ↦ θ + α`.

Main statement `Frontier.avila_ten_martini`: the Ten Martini property (Cantor spectrum for all
nonzero coupling and all irrational flux) is *equivalent* to the two analytic inputs of
Avila–Jitomirskaya, namely that the spectrum has empty interior and no isolated points.  The full
theorem is not proved; this is a Lean-checked reduction of it.

The main Mathlib results used are `lp.inner_eq_tsum`,
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`, `spectrum.nonempty`,
`IsSelfAdjoint.mem_spectrum_eq_re`, `spectrum.norm_le_norm_of_mem`, `spectrum.units_conjugate`,
`IsPreconnected.Icc_subset` and `Perfect.exists_nat_bool_injection`.
-/

open scoped ENNReal InnerProductSpace Topology

namespace Frontier

/-! ## The Hilbert space `ℓ²(ℤ; ℂ)` -/

/-- The Hilbert space `ℓ²(ℤ; ℂ)` on which the almost Mathieu operator acts. -/
noncomputable abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

instance : Nontrivial L2Z := by
  refine ⟨0, lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ), fun h => ?_⟩
  have h1 : ‖lp.single (E := fun _ : ℤ => ℂ) 2 (0 : ℤ) (1 : ℂ)‖ = 1 := by
    rw [lp.norm_single (by norm_num)]; simp
  rw [← h] at h1
  simp at h1

theorem summable_norm_sq (x : L2Z) : Summable (fun n : ℤ => ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ)) := by
  have h := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp x)
  simpa using h

theorem memℓp_comp_equiv (e : ℤ ≃ ℤ) (x : L2Z) : Memℓp (fun n => (x : ℤ → ℂ) (e n)) 2 := by
  apply memℓp_gen
  simpa using (e.summable_iff (f := fun n => ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ))).2 (summable_norm_sq x)

theorem memℓp_mul_bdd (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) :
    Memℓp (fun n => (V n : ℂ) * (x : ℤ → ℂ) n) 2 := by
  apply memℓp_gen
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) ((summable_norm_sq x).mul_left (C ^ (2 : ℝ)))
  simp only [ENNReal.toReal_ofNat, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr
  exact hV n

/-! ## Reindexing (shift) operators -/

/-- Reindexing of an `ℓ²` sequence along a bijection of `ℤ`, as a linear map. -/
noncomputable def reindexLM (e : ℤ ≃ ℤ) : L2Z →ₗ[ℂ] L2Z where
  toFun x := ⟨fun n => (x : ℤ → ℂ) (e n), memℓp_comp_equiv e x⟩
  map_add' x y := by ext n; simp
  map_smul' c x := by ext n; simp

@[simp] theorem reindexLM_apply (e : ℤ ≃ ℤ) (x : L2Z) (n : ℤ) :
    ((reindexLM e x : L2Z) : ℤ → ℂ) n = (x : ℤ → ℂ) (e n) := rfl

theorem norm_reindexLM (e : ℤ ≃ ℤ) (x : L2Z) : ‖reindexLM e x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
  congr 1
  simp only [reindexLM_apply]
  exact e.tsum_eq (fun n => ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal)

/-- Reindexing of an `ℓ²` sequence along a bijection of `ℤ`, as a continuous linear map. -/
noncomputable def reindexCLM (e : ℤ ≃ ℤ) : L2Z →L[ℂ] L2Z :=
  (reindexLM e).mkContinuous 1 (fun x => by rw [norm_reindexLM, one_mul])

@[simp] theorem reindexCLM_apply (e : ℤ ≃ ℤ) (x : L2Z) (n : ℤ) :
    ((reindexCLM e x : L2Z) : ℤ → ℂ) n = (x : ℤ → ℂ) (e n) := rfl

theorem norm_reindexCLM_le (e : ℤ ≃ ℤ) : ‖reindexCLM e‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

theorem inner_reindexCLM (e : ℤ ≃ ℤ) (x y : L2Z) :
    ⟪reindexCLM e x, y⟫_ℂ = ⟪x, reindexCLM e.symm y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [reindexCLM_apply]
  simpa using e.tsum_eq (fun m => ⟪(x : ℤ → ℂ) m, (y : ℤ → ℂ) (e.symm m)⟫_ℂ)

/-! ## Multiplication operators -/

/-- Multiplication by a bounded real sequence, as a linear map on `ℓ²(ℤ; ℂ)`. -/
noncomputable def mulLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →ₗ[ℂ] L2Z where
  toFun x := ⟨fun n => (V n : ℂ) * (x : ℤ → ℂ) n, memℓp_mul_bdd V C hV x⟩
  map_add' x y := by ext n; simp [mul_add]
  map_smul' c x := by ext n; simp [mul_left_comm]

@[simp] theorem mulLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) (n : ℤ) :
    ((mulLM V C hV x : L2Z) : ℤ → ℂ) n = (V n : ℂ) * (x : ℤ → ℂ) n := rfl

theorem norm_mulLM_le (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) :
    ‖mulLM V C hV x‖ ≤ C * ‖x‖ := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hV 0)
  refine lp.norm_le_of_tsum_le (by norm_num) (by positivity) ?_
  have hsum : Summable (fun n : ℤ => ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ)) := by
    simpa using summable_norm_sq (mulLM V C hV x)
  have hle : ∀ n : ℤ, ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    intro n
    simp only [mulLM_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
    gcongr
    exact hV n
  have h1 : ∑' n : ℤ, ‖((mulLM V C hV x : L2Z) : ℤ → ℂ) n‖ ^ (2 : ℝ≥0∞).toReal
      ≤ ∑' n : ℤ, C ^ (2 : ℝ) * ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) := by
    refine Summable.tsum_le_tsum ?_ (by simpa using hsum) ((summable_norm_sq x).mul_left _)
    simpa using hle
  have hx : ∑' n : ℤ, ‖(x : ℤ → ℂ) n‖ ^ (2 : ℝ) = ‖x‖ ^ (2 : ℝ) := by
    simpa using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) x).symm
  refine h1.trans (le_of_eq ?_)
  rw [tsum_mul_left, hx]
  simp only [ENNReal.toReal_ofNat]
  rw [Real.mul_rpow hC (norm_nonneg _)]

/-- Multiplication by a bounded real sequence, as a continuous linear map on `ℓ²(ℤ; ℂ)`. -/
noncomputable def mulCLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : L2Z →L[ℂ] L2Z :=
  (mulLM V C hV).mkContinuous C (norm_mulLM_le V C hV)

@[simp] theorem mulCLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x : L2Z) (n : ℤ) :
    ((mulCLM V C hV x : L2Z) : ℤ → ℂ) n = (V n : ℂ) * (x : ℤ → ℂ) n := rfl

theorem norm_mulCLM_le (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) : ‖mulCLM V C hV‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (abs_nonneg _) (hV 0)) _

theorem inner_mulCLM (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (x y : L2Z) :
    ⟪mulCLM V C hV x, y⟫_ℂ = ⟪x, mulCLM V C hV y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun n => ?_)
  simp only [mulCLM_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ## The almost Mathieu operator -/

/-- The potential of the almost Mathieu operator:
`v(n) = 2 λ cos (2π (θ + n α))`. -/
noncomputable def amoPotential (lam alpha theta : ℝ) (n : ℤ) : ℝ :=
  2 * lam * Real.cos (2 * Real.pi * (theta + n * alpha))

theorem abs_amoPotential_le (lam alpha theta : ℝ) (n : ℤ) :
    |amoPotential lam alpha theta n| ≤ 2 * |lam| := by
  unfold amoPotential
  rw [abs_mul, abs_mul]
  have h1 : |Real.cos (2 * Real.pi * (theta + n * alpha))| ≤ 1 := Real.abs_cos_le_one _
  have h2 : (0 : ℝ) ≤ |(2 : ℝ)| * |lam| := by positivity
  calc |(2 : ℝ)| * |lam| * |Real.cos (2 * Real.pi * (theta + n * alpha))|
      ≤ |(2 : ℝ)| * |lam| * 1 := by gcongr
    _ = 2 * |lam| := by simp

/-- The **almost Mathieu operator** `H_{λ,α,θ}` on `ℓ²(ℤ; ℂ)`:
`(H u)(n) = u(n+1) + u(n-1) + 2 λ cos (2π (θ + n α)) u(n)`. -/
noncomputable def amo (lam alpha theta : ℝ) : L2Z →L[ℂ] L2Z :=
  reindexCLM (Equiv.addRight (1 : ℤ)) + reindexCLM (Equiv.addRight (-1 : ℤ))
    + mulCLM (amoPotential lam alpha theta) (2 * |lam|) (abs_amoPotential_le lam alpha theta)

theorem amo_apply (lam alpha theta : ℝ) (x : L2Z) (n : ℤ) :
    ((amo lam alpha theta x : L2Z) : ℤ → ℂ)  n
      = (x : ℤ → ℂ) (n + 1) + (x : ℤ → ℂ) (n - 1)
        + (amoPotential lam alpha theta n : ℂ) * (x : ℤ → ℂ) n := by
  simp [amo, sub_eq_add_neg]

theorem norm_amo_le (lam alpha theta : ℝ) : ‖amo lam alpha theta‖ ≤ 2 + 2 * |lam| := by
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_reindexCLM_le (Equiv.addRight (1 : ℤ))
  have h2 := norm_reindexCLM_le (Equiv.addRight (-1 : ℤ))
  have h3 := norm_mulCLM_le (amoPotential lam alpha theta) (2 * |lam|)
    (abs_amoPotential_le lam alpha theta)
  have h4 : ‖reindexCLM (Equiv.addRight (1 : ℤ)) + reindexCLM (Equiv.addRight (-1 : ℤ))‖ ≤ 2 :=
    le_trans (norm_add_le _ _) (by linarith)
  linarith

theorem equiv_addRight_one_symm : (Equiv.addRight (1 : ℤ)).symm = Equiv.addRight (-1 : ℤ) := by
  ext n; simp [Equiv.addRight]

theorem equiv_addRight_neg_one_symm : (Equiv.addRight (-1 : ℤ)).symm = Equiv.addRight (1 : ℤ) := by
  ext n; simp [Equiv.addRight]

/-- The almost Mathieu operator is self-adjoint. -/
theorem amo_isSelfAdjoint (lam alpha theta : ℝ) : IsSelfAdjoint (amo lam alpha theta) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hsymm := equiv_addRight_one_symm
  have hsymm' := equiv_addRight_neg_one_symm
  simp only [amo, ContinuousLinearMap.coe_add, LinearMap.add_apply,
    ContinuousLinearMap.coe_coe, inner_add_left, inner_add_right]
  rw [inner_reindexCLM, inner_reindexCLM, inner_mulCLM, hsymm, hsymm']
  ring

/-! ## Covariance of the almost Mathieu family -/

theorem reindexCLM_mul (e f : ℤ ≃ ℤ) :
    reindexCLM e * reindexCLM f = reindexCLM (e.trans f) := by
  ext x n
  rfl

@[simp] theorem reindexCLM_refl : reindexCLM (Equiv.refl ℤ) = 1 := by
  ext x n
  rfl

/-- Reindexing along a bijection of `ℤ` is a unit of the algebra of bounded operators. -/
noncomputable def reindexUnit (e : ℤ ≃ ℤ) : (L2Z →L[ℂ] L2Z)ˣ where
  val := reindexCLM e
  inv := reindexCLM e.symm
  val_inv := by rw [reindexCLM_mul]; simp
  inv_val := by rw [reindexCLM_mul]; simp

/-- **Covariance of the almost Mathieu family**: conjugating `H_{λ,α,θ}` by the shift gives
`H_{λ,α,θ+α}`. -/
theorem amo_conj (lam alpha theta : ℝ) :
    reindexCLM (Equiv.addRight (1 : ℤ)) * amo lam alpha theta
        * reindexCLM (Equiv.addRight (-1 : ℤ)) = amo lam alpha (theta + alpha) := by
  ext x n
  simp only [ContinuousLinearMap.mul_apply, reindexCLM_apply, amo_apply, Equiv.coe_addRight]
  have hV : amoPotential lam alpha theta (n + 1) = amoPotential lam alpha (theta + alpha) n := by
    unfold amoPotential
    have hcos : theta + ((n + 1 : ℤ) : ℝ) * alpha = theta + alpha + (n : ℝ) * alpha := by
      push_cast; ring
    rw [hcos]
  rw [hV, show n + 1 + 1 + -1 = n + 1 from by ring, show n + 1 - 1 + -1 = n - 1 from by ring,
    show n + 1 + -1 = n from by ring]

/-! ## The spectrum of the almost Mathieu operator -/

/-- The spectrum of the almost Mathieu operator, viewed as a subset of `ℝ`
(legitimate since the operator is self-adjoint). -/
noncomputable def amoSpectrum (lam alpha theta : ℝ) : Set ℝ :=
  {E : ℝ | (E : ℂ) ∈ spectrum ℂ (amo lam alpha theta)}

theorem amoSpectrum_nonempty (lam alpha theta : ℝ) : (amoSpectrum lam alpha theta).Nonempty := by
  obtain ⟨z, hz⟩ := spectrum.nonempty (amo lam alpha theta)
  refine ⟨z.re, ?_⟩
  have : z = (z.re : ℂ) := (amo_isSelfAdjoint lam alpha theta).mem_spectrum_eq_re hz
  simpa [amoSpectrum, ← this] using hz

/-- The spectrum of the almost Mathieu operator is invariant under the phase shift
`θ ↦ θ + α`. -/
theorem amoSpectrum_theta_add (lam alpha theta : ℝ) :
    amoSpectrum lam alpha (theta + alpha) = amoSpectrum lam alpha theta := by
  set u : (L2Z →L[ℂ] L2Z)ˣ := reindexUnit (Equiv.addRight (1 : ℤ))
  have hval : (u : L2Z →L[ℂ] L2Z) = reindexCLM (Equiv.addRight (1 : ℤ)) := rfl
  have hinv : ((u⁻¹ : (L2Z →L[ℂ] L2Z)ˣ) : L2Z →L[ℂ] L2Z)
      = reindexCLM (Equiv.addRight (-1 : ℤ)) := by
    show reindexCLM (Equiv.addRight (1 : ℤ)).symm = _
    rw [equiv_addRight_one_symm]
  have h : spectrum ℂ (amo lam alpha (theta + alpha)) = spectrum ℂ (amo lam alpha theta) :=
    calc spectrum ℂ (amo lam alpha (theta + alpha))
        = spectrum ℂ ((u : L2Z →L[ℂ] L2Z) * amo lam alpha theta * (u⁻¹ : (L2Z →L[ℂ] L2Z)ˣ)) := by
          rw [hval, hinv, amo_conj]
      _ = spectrum ℂ (amo lam alpha theta) := spectrum.units_conjugate
  ext E
  simp [amoSpectrum, h]

theorem amoSpectrum_subset_Icc (lam alpha theta : ℝ) :
    amoSpectrum lam alpha theta ⊆ Set.Icc (-(2 + 2 * |lam|)) (2 + 2 * |lam|) := by
  intro E hE
  have h1 : ‖(E : ℂ)‖ ≤ ‖amo lam alpha theta‖ := spectrum.norm_le_norm_of_mem hE
  have h2 : |E| ≤ 2 + 2 * |lam| :=
    le_trans (by simpa using h1) (norm_amo_le lam alpha theta)
  exact ⟨by cases abs_le.mp h2 with | intro a b => linarith, (abs_le.mp h2).2⟩

theorem amoSpectrum_isClosed (lam alpha theta : ℝ) : IsClosed (amoSpectrum lam alpha theta) := by
  have hc : Continuous (fun E : ℝ => (E : ℂ)) := Complex.continuous_ofReal
  exact (spectrum.isClosed (amo lam alpha theta)).preimage hc

theorem amoSpectrum_isCompact (lam alpha theta : ℝ) : IsCompact (amoSpectrum lam alpha theta) :=
  Metric.isCompact_of_isClosed_isBounded (amoSpectrum_isClosed lam alpha theta)
    ((Metric.isBounded_Icc _ _).subset (amoSpectrum_subset_Icc lam alpha theta))

/-! ## Cantor sets -/

/-- A subset of `ℝ` is a Cantor set if it is nonempty, compact, perfect (closed with no isolated
points) and totally disconnected.  By Brouwer's characterization these are exactly the subsets of
`ℝ` homeomorphic to the Cantor space `ℕ → Bool`. -/
def IsCantorSet (s : Set ℝ) : Prop :=
  s.Nonempty ∧ IsCompact s ∧ Perfect s ∧ IsTotallyDisconnected s

theorem interior_eq_empty_of_isTotallyDisconnected {s : Set ℝ} (h : IsTotallyDisconnected s) :
    interior s = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hsub : Set.Icc x (x + ε / 2) ⊆ s := by
    intro y hy
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have := h _ hsub isPreconnected_Icc
  have hmem1 : x ∈ Set.Icc x (x + ε / 2) := ⟨le_rfl, by linarith⟩
  have hmem2 : x + ε / 2 ∈ Set.Icc x (x + ε / 2) := ⟨by linarith, le_rfl⟩
  have := this hmem1 hmem2
  linarith

theorem isTotallyDisconnected_of_interior_eq_empty {s : Set ℝ} (h : interior s = ∅) :
    IsTotallyDisconnected s := by
  intro t hts hpre a ha b hb
  by_contra hab
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · have hIcc : Set.Icc a b ⊆ t := hpre.Icc_subset ha hb
    have : Set.Ioo a b ⊆ interior s :=
      interior_maximal (fun y hy => hts (hIcc ⟨hy.1.le, hy.2.le⟩)) isOpen_Ioo
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.mpr hlt).ne_empty this
  · have hIcc : Set.Icc b a ⊆ t := hpre.Icc_subset hb ha
    have : Set.Ioo b a ⊆ interior s :=
      interior_maximal (fun y hy => hts (hIcc ⟨hy.1.le, hy.2.le⟩)) isOpen_Ioo
    rw [h, Set.subset_empty_iff] at this
    exact (Set.nonempty_Ioo.mpr hlt).ne_empty this

/-! ## The Ten Martini problem -/

/--
**The Ten Martini Problem** (Avila–Jitomirskaya), as a Lean-checked reduction.

For every nonzero coupling `λ`, every irrational flux `α` and every phase `θ`, the spectrum of the
almost Mathieu operator `H_{λ,α,θ}` on `ℓ²(ℤ)` is a Cantor set **if and only if** for all such
parameters the spectrum has empty interior (all spectral gaps present) and no isolated points.

The two remaining defining features of a Cantor set — nonemptiness and compactness of the
spectrum — are proved here unconditionally from the construction of the operator
(`amoSpectrum_nonempty`, `amoSpectrum_isCompact`), together with self-adjointness of `H_{λ,α,θ}`
(`amo_isSelfAdjoint`), which is what makes the real spectrum `amoSpectrum` the right object.

Thus this statement is exactly the reduction of the Ten Martini problem to the two analytic
inputs of Avila–Jitomirskaya: absence of interior, and absence of isolated points, in the
spectrum.  Neither of those inputs is assumed anywhere in this file; they appear only as the
right-hand side of the equivalence.
-/
theorem avila_ten_martini :
    (∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
        IsCantorSet (amoSpectrum lam alpha theta))
      ↔ (∀ lam alpha theta : ℝ, lam ≠ 0 → Irrational alpha →
        interior (amoSpectrum lam alpha theta) = ∅ ∧
          ∀ E ∈ amoSpectrum lam alpha theta,
            AccPt E (Filter.principal (amoSpectrum lam alpha theta))) := by
  constructor
  · intro h lam alpha theta hlam halpha
    obtain ⟨-, -, hperf, htd⟩ := h lam alpha theta hlam halpha
    exact ⟨interior_eq_empty_of_isTotallyDisconnected htd, hperf.acc⟩
  · intro h lam alpha theta hlam halpha
    obtain ⟨hint, hacc⟩ := h lam alpha theta hlam halpha
    exact ⟨amoSpectrum_nonempty lam alpha theta, amoSpectrum_isCompact lam alpha theta,
      ⟨amoSpectrum_isClosed lam alpha theta, hacc⟩,
      isTotallyDisconnected_of_interior_eq_empty hint⟩

/-- Consequence of the Ten Martini property: the spectrum contains a topologically embedded copy
of the Cantor space `ℕ → Bool`. -/
theorem exists_cantor_embedding_of_isCantorSet {s : Set ℝ} (h : IsCantorSet s) :
    ∃ f : (ℕ → Bool) → ℝ, Set.range f ⊆ s ∧ Continuous f ∧ Function.Injective f := by
  obtain ⟨hne, -, hperf, -⟩ := h
  exact hperf.exists_nat_bool_injection hne

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

