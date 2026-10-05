import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Phys

open Complex MeasureTheory intervalIntegral
open scoped InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## Phases -/

/-- The unimodular phase `u ↦ exp (i r u)`. -/
def cphase (r : ℝ) (s : ℝ) : ℂ := Complex.exp (((r * s : ℝ) : ℂ) * Complex.I)

theorem cphase_hasDerivAt (r s : ℝ) :
    HasDerivAt (cphase r) (cphase r s * ((r : ℂ) * Complex.I)) s := by
  have h0 : HasDerivAt (fun s : ℝ => r * s) r s := by simpa using (hasDerivAt_id s).const_mul r
  have h1 : HasDerivAt (fun s : ℝ => ((r * s : ℝ) : ℂ)) (r : ℂ) s := by
    have := (Complex.ofRealCLM.hasDerivAt (x := r * s)).scomp s h0
    simp only [Complex.ofRealCLM_apply, Function.comp_def] at this
    simpa using this
  exact (h1.mul_const Complex.I).cexp

theorem norm_cphase (r s : ℝ) : ‖cphase r s‖ = 1 := by
  simp [cphase, Complex.norm_exp]

theorem cphase_ne_zero (r s : ℝ) : cphase r s ≠ 0 := Complex.exp_ne_zero _

theorem cphase_add (a b s : ℝ) : cphase a s * cphase b s = cphase (a + b) s := by
  simp only [cphase, ← Complex.exp_add]
  push_cast
  ring_nf

theorem cphase_inv (a s : ℝ) : (cphase a s)⁻¹ = cphase (-a) s :=
  inv_eq_of_mul_eq_one_right (by rw [cphase_add]; simp [cphase])

theorem cphase_continuous (r : ℝ) : Continuous (cphase r) :=
  continuous_iff_continuousAt.mpr fun s => (cphase_hasDerivAt r s).continuousAt

/-! ## Differentiating the application of an operator-valued function -/

/-- Product rule for `t ↦ (A t) (v t)` where `A` is `ℂ`-linear but the parameter is real. -/
theorem hasDerivAt_clmApply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A DA : ℝ → E →L[ℂ] F) (v : ℝ → E) (v' : F) (dv : E) (s : ℝ)
    (hA : HasDerivAt A (DA s) s) (hv : HasDerivAt v dv s) (hv' : v' = DA s (v s) + A s dv) :
    HasDerivAt (fun t => A t (v t)) v' s := by
  subst hv'
  have hRS : HasDerivAt (fun t => (A t).restrictScalars ℝ) ((DA s).restrictScalars ℝ) s :=
    ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).hasFDerivAt).comp_hasDerivAt s hA
  exact hRS.clm_apply hv

/-! ## The instantaneous Hamiltonian -/

/-- The instantaneous Hamiltonian with (real) eigenvalue `e₁` on the range of the projection
`P s` and eigenvalue `e₂` on its kernel. -/
def ham (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ) : E →L[ℂ] E :=
  (e₁ : ℂ) • P s + (e₂ : ℂ) • (ContinuousLinearMap.id ℂ E - P s)

theorem ham_apply (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ) (v : E) :
    ham P e₁ e₂ s v = (e₁ : ℂ) • P s v + (e₂ : ℂ) • (v - P s v) := by
  simp [ham]

theorem proj_ham (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ)
    (hidem : (P s).comp (P s) = P s) (v : E) :
    P s (ham P e₁ e₂ s v) = (e₁ : ℂ) • P s v := by
  have h : P s (P s v) = P s v := by
    have := congrArg (fun T : E →L[ℂ] E => T v) hidem
    simpa using this
  simp [ham_apply, h]

theorem compl_ham (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ)
    (hidem : (P s).comp (P s) = P s) (v : E) :
    ham P e₁ e₂ s v - P s (ham P e₁ e₂ s v) = (e₂ : ℂ) • (v - P s v) := by
  rw [proj_ham P e₁ e₂ s hidem, ham_apply]
  abel

theorem ham_symm [CompleteSpace E] (P : ℝ → E →L[ℂ] E) (e₁ e₂ : ℝ) (s : ℝ)
    (hsa : IsSelfAdjoint (P s)) (v w : E) :
    ⟪ham P e₁ e₂ s v, w⟫_ℂ = ⟪v, ham P e₁ e₂ s w⟫_ℂ := by
  have key : ⟪(P s) v, w⟫_ℂ = ⟪v, (P s) w⟫_ℂ :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) v w
  simp only [ham, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, Complex.conj_ofReal, key]

/-- Conservation of the norm along the Schrödinger flow. -/
theorem norm_sol_eq [CompleteSpace E] (P : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ)
    (hsa : ∀ s, IsSelfAdjoint (P s)) (ψ : ℝ → E)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    ‖ψ s‖ = ‖ψ 0‖ := by
  set c : ℂ := -Complex.I / (ε : ℂ) with hc
  have hconj : (starRingEnd ℂ) c + c = 0 := by
    simp [hc, div_eq_mul_inv, map_mul, Complex.conj_I]
  have hd : ∀ t : ℝ, HasDerivAt (fun t => ⟪ψ t, ψ t⟫_ℂ) 0 t := by
    intro t
    have hi := (hψ t).inner ℂ (hψ t)
    have hz : ⟪ψ t, c • ham P e₁ e₂ t (ψ t)⟫_ℂ + ⟪c • ham P e₁ e₂ t (ψ t), ψ t⟫_ℂ = 0 := by
      rw [inner_smul_right, inner_smul_left]
      have h1 : ⟪ham P e₁ e₂ t (ψ t), ψ t⟫_ℂ = ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ :=
        ham_symm P e₁ e₂ t (hsa t) _ _
      have h2 : (starRingEnd ℂ) c * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ
            + c * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ
          = ((starRingEnd ℂ) c + c) * ⟪ψ t, ham P e₁ e₂ t (ψ t)⟫_ℂ := by ring
      rw [h1, add_comm, h2, hconj, zero_mul]
    rw [hz] at hi
    exact hi
  have hconstf : ∀ x y : ℝ, (fun t => ⟪ψ t, ψ t⟫_ℂ) x = (fun t => ⟪ψ t, ψ t⟫_ℂ) y :=
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
  have hxy := hconstf s 0
  simp only [] at hxy
  have h1 : (‖ψ s‖ : ℝ) ^ 2 = (‖ψ 0‖ : ℝ) ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ψ s), inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (ψ 0)] at hxy
    exact_mod_cast hxy
  nlinarith [norm_nonneg (ψ s), norm_nonneg (ψ 0)]

/-! ## The two phase-corrected components of the state -/

/-- Phase-corrected component of the state inside the instantaneous eigenspace. -/
def alph (P : ℝ → E →L[ℂ] E) (e₁ ε : ℝ) (ψ : ℝ → E) (s : ℝ) : E :=
  cphase (e₁ / ε) s • P s (ψ s)

/-- Phase-corrected component of the state transverse to the instantaneous eigenspace. -/
def chi (P : ℝ → E →L[ℂ] E) (e₂ ε : ℝ) (ψ : ℝ → E) (s : ℝ) : E :=
  cphase (e₂ / ε) s • (ψ s - P s (ψ s))

theorem norm_alph (P : ℝ → E →L[ℂ] E) (e₁ ε : ℝ) (ψ : ℝ → E) (s : ℝ) :
    ‖alph P e₁ ε ψ s‖ = ‖P s (ψ s)‖ := by
  simp [alph, norm_smul, norm_cphase]

theorem norm_chi (P : ℝ → E →L[ℂ] E) (e₂ ε : ℝ) (ψ : ℝ → E) (s : ℝ) :
    ‖chi P e₂ ε ψ s‖ = ‖ψ s - P s (ψ s)‖ := by
  simp [chi, norm_smul, norm_cphase]

theorem alph_hasDerivAt (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (alph P e₁ ε ψ) (cphase (e₁ / ε) s • DP s (ψ s)) s := by
  have hu : HasDerivAt (fun t => P t (ψ t))
      (DP s (ψ s) + ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ)) • P s (ψ s)) s := by
    refine hasDerivAt_clmApply P DP ψ _ _ s (hP s) (hψ s) ?_
    rw [ContinuousLinearMap.map_smul, proj_ham P e₁ e₂ s (hidem s), smul_smul]
  have h := (cphase_hasDerivAt (e₁ / ε) s).smul hu
  have heq : cphase (e₁ / ε) s • (DP s (ψ s) + ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ)) • P s (ψ s))
      + (cphase (e₁ / ε) s * (((e₁ / ε : ℝ) : ℂ) * Complex.I)) • P s (ψ s)
      = cphase (e₁ / ε) s • DP s (ψ s) := by
    rw [smul_add, smul_smul, add_assoc, ← add_smul]
    have hz : cphase (e₁ / ε) s * ((-Complex.I / (ε : ℂ)) * (e₁ : ℂ))
        + cphase (e₁ / ε) s * (((e₁ / ε : ℝ) : ℂ) * Complex.I) = 0 := by
      push_cast
      ring
    rw [hz, zero_smul, add_zero]
  exact h.congr_deriv heq

theorem chi_hasDerivAt (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (chi P e₂ ε ψ) (-(cphase (e₂ / ε) s • DP s (ψ s))) s := by
  set c : ℂ := -Complex.I / (ε : ℂ) with hc
  have hu : HasDerivAt (fun t => P t (ψ t)) (DP s (ψ s) + P s (c • ham P e₁ e₂ s (ψ s))) s :=
    hasDerivAt_clmApply P DP ψ _ _ s (hP s) (hψ s) rfl
  have hw : HasDerivAt (fun t => ψ t - P t (ψ t))
      ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s)) - DP s (ψ s)) s := by
    refine ((hψ s).sub hu).congr_deriv ?_
    have h1 : P s (c • ham P e₁ e₂ s (ψ s)) = c • P s (ham P e₁ e₂ s (ψ s)) :=
      ContinuousLinearMap.map_smul _ _ _
    rw [h1]
    have h2 : ham P e₁ e₂ s (ψ s) - P s (ham P e₁ e₂ s (ψ s)) = (e₂ : ℂ) • (ψ s - P s (ψ s)) :=
      compl_ham P e₁ e₂ s (hidem s) (ψ s)
    have h3 : c • ham P e₁ e₂ s (ψ s) - (DP s (ψ s) + c • P s (ham P e₁ e₂ s (ψ s)))
        = c • (ham P e₁ e₂ s (ψ s) - P s (ham P e₁ e₂ s (ψ s))) - DP s (ψ s) := by
      rw [smul_sub]; abel
    rw [h3, h2, smul_smul]
  have h := (cphase_hasDerivAt (e₂ / ε) s).smul hw
  have heq : cphase (e₂ / ε) s • ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s)) - DP s (ψ s))
      + (cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
      = -(cphase (e₂ / ε) s • DP s (ψ s)) := by
    rw [smul_sub, smul_smul]
    have hz : cphase (e₂ / ε) s * (c * (e₂ : ℂ))
        + cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I) = 0 := by
      rw [hc]; push_cast; ring
    have : cphase (e₂ / ε) s • ((c * (e₂ : ℂ)) • (ψ s - P s (ψ s))) - cphase (e₂ / ε) s • DP s (ψ s)
        + (cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
        = ((cphase (e₂ / ε) s * (c * (e₂ : ℂ)))
            + cphase (e₂ / ε) s * (((e₂ / ε : ℝ) : ℂ) * Complex.I)) • (ψ s - P s (ψ s))
          - cphase (e₂ / ε) s • DP s (ψ s) := by
      rw [add_smul, smul_smul]; abel
    rw [smul_smul] at this
    rw [this, hz, zero_smul, zero_sub]
  exact h.congr_deriv heq

/-- Splitting the derivative of the transverse component into an oscillatory source term and a
term proportional to the transverse component itself. -/
theorem chi_deriv_split (P DP : ℝ → E →L[ℂ] E) (e₁ e₂ ε : ℝ) (ψ : ℝ → E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hidem : ∀ s, (P s).comp (P s) = P s)
    (hψ : ∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) (s : ℝ) :
    HasDerivAt (chi P e₂ ε ψ)
      (-(cphase ((e₂ - e₁) / ε) s • DP s (alph P e₁ ε ψ s)) - DP s (chi P e₂ ε ψ s)) s := by
  refine (chi_hasDerivAt P DP e₁ e₂ ε ψ hP hidem hψ s).congr_deriv ?_
  have h1 : DP s (alph P e₁ ε ψ s) = cphase (e₁ / ε) s • DP s (P s (ψ s)) := by
    rw [alph, ContinuousLinearMap.map_smul]
  have h2 : DP s (chi P e₂ ε ψ s) = cphase (e₂ / ε) s • DP s (ψ s - P s (ψ s)) := by
    rw [chi, ContinuousLinearMap.map_smul]
  have h3 : (e₂ - e₁) / ε + e₁ / ε = e₂ / ε := by ring
  rw [h1, h2, smul_smul, cphase_add, h3, map_sub, smul_sub]
  abel

/-! ## Bound on an oscillatory integral -/

/-- Nonstationary phase: an oscillatory integral of a `C¹` function is `O(1/ω)`. -/
theorem osc_integral_bound [CompleteSpace E] (f Df : ℝ → E)
    (hf : ∀ u, HasDerivAt f (Df u) u) (hDf : Continuous Df) (ω A B : ℝ) (hω : ω ≠ 0)
    (hA : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖f u‖ ≤ A)
    (hB : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖Df u‖ ≤ B) (s : ℝ) (hs : s ∈ Set.Icc (0:ℝ) 1) :
    ‖∫ u in (0:ℝ)..s, cphase ω u • f u‖ ≤ (2 * A + B) / |ω| := by
  obtain ⟨hs0, hs1⟩ := hs
  have hf_cont : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  set k : ℂ := (ω : ℂ) * Complex.I with hk
  have hkne : k ≠ 0 := by
    simp only [hk, ne_eq, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero]
    exact hω
  have hknorm : ‖k‖ = |ω| := by simp [hk]
  set F : ℝ → E := fun u => (cphase ω u / k) • f u with hF
  have hFd : ∀ u, HasDerivAt F (cphase ω u • f u + (cphase ω u / k) • Df u) u := by
    intro u
    have h1 : HasDerivAt (fun t => cphase ω t / k) (cphase ω u * k / k) u :=
      (cphase_hasDerivAt ω u).div_const k
    refine (h1.smul (hf u)).congr_deriv ?_
    rw [mul_div_assoc, div_self hkne, mul_one]
    abel
  have hg1 : Continuous (fun u => cphase ω u • f u) := (cphase_continuous ω).smul hf_cont
  have hg2 : Continuous (fun u => (cphase ω u / k) • Df u) :=
    ((cphase_continuous ω).div_const k).smul hDf
  have hint : ∫ u in (0:ℝ)..s, (cphase ω u • f u + (cphase ω u / k) • Df u) = F s - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hFd x)
      ((hg1.add hg2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hg1.intervalIntegrable _ _)
    (hg2.intervalIntegrable _ _)] at hint
  have hsplit : ∫ u in (0:ℝ)..s, cphase ω u • f u
      = (F s - F 0) - ∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u := by
    rw [← hint]; abel
  have hsub : Set.uIoc (0:ℝ) s ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    rw [Set.uIoc_of_le hs0] at hx
    exact ⟨le_of_lt hx.1, hx.2.trans hs1⟩
  have hωpos : (0:ℝ) < |ω| := abs_pos.mpr hω
  have hFbound : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖F u‖ ≤ A / |ω| := by
    intro u hu
    rw [hF]
    simp only [norm_smul, norm_div, norm_cphase, hknorm]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hωpos]
    exact hA u hu
  have hDbound : ‖∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u‖ ≤ (B / |ω|) * |s - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const ?_
    intro x hx
    have hx' := hB x (hsub hx)
    simp only [norm_smul, norm_div, norm_cphase, hknorm]
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right hωpos]
    exact hx'
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_refl 0, zero_le_one⟩)
  have hs' : |s - 0| ≤ 1 := by rw [sub_zero, abs_of_nonneg hs0]; exact hs1
  have h1 := hFbound s ⟨hs0, hs1⟩
  have h2 := hFbound 0 ⟨le_refl 0, zero_le_one⟩
  have h3 : (B / |ω|) * |s - 0| ≤ B / |ω| := by
    nlinarith [div_nonneg hB0 (le_of_lt hωpos), abs_nonneg (s - 0)]
  calc ‖∫ u in (0:ℝ)..s, cphase ω u • f u‖
      ≤ ‖F s - F 0‖ + ‖∫ u in (0:ℝ)..s, (cphase ω u / k) • Df u‖ := by
        rw [hsplit]; exact norm_sub_le _ _
    _ ≤ (‖F s‖ + ‖F 0‖) + (B / |ω|) * |s - 0| := by
        gcongr
        exact norm_sub_le _ _
    _ ≤ (A / |ω| + A / |ω|) + B / |ω| := by gcongr
    _ = (2 * A + B) / |ω| := by ring

/-! ## The adiabatic theorem -/

/-- **Adiabatic theorem.**

Let `P s` be a smoothly varying orthogonal projection (`P s` idempotent and self-adjoint) onto a
nondegenerate instantaneous eigenspace, and let
`ham P e₁ e₂ s = e₁ • P s + e₂ • (1 - P s)` be the corresponding instantaneous Hamiltonian, whose
eigenvalue `e₁` on `range (P s)` is separated by the spectral gap `e₂ - e₁ ≠ 0` from the rest of
the spectrum.

If `ψ` solves the Schrödinger equation `ε • ψ' = -i • ham ψ` -- i.e. the Hamiltonian is traversed
over a physical time `1/ε`, so that it varies ever more slowly as `ε → 0` -- and if the initial
state lies in the initial eigenspace (`P 0 (ψ 0) = ψ 0`), then, throughout the whole evolution, the
state stays in the instantaneous eigenspace `range (P s)` up to an error `O(ε)`: the transverse
component `ψ s - P s (ψ s)` is bounded by `C * ε * ‖ψ 0‖` with a constant `C` depending only on
the Hamiltonian, not on `ε` or on the solution. -/
theorem adiabatic_theorem [CompleteSpace E] (P DP D2P : ℝ → E →L[ℂ] E)
    (hP : ∀ s, HasDerivAt P (DP s) s) (hDP : ∀ s, HasDerivAt DP (D2P s) s)
    (hD2P : Continuous D2P)
    (hidem : ∀ s, (P s).comp (P s) = P s) (hsa : ∀ s, IsSelfAdjoint (P s))
    (e₁ e₂ : ℝ) (hgap : e₁ ≠ e₂) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ ψ : ℝ → E,
      (∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) →
      P 0 (ψ 0) = ψ 0 →
      ∀ s ∈ Set.Icc (0:ℝ) 1, ‖ψ s - P s (ψ s)‖ ≤ C * ε * ‖ψ 0‖ := by
  have hPcont : Continuous P := continuous_iff_continuousAt.mpr fun s => (hP s).continuousAt
  have hDPcont : Continuous DP := continuous_iff_continuousAt.mpr fun s => (hDP s).continuousAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hPcont.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hDPcont.continuousOn
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hD2P.continuousOn
  have hzo : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have hM₀n : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ 0 hzo)
  have hM₁n : 0 ≤ M₁ := le_trans (norm_nonneg _) (hM₁ 0 hzo)
  have hM₂n : 0 ≤ M₂ := le_trans (norm_nonneg _) (hM₂ 0 hzo)
  have hgap' : |e₂ - e₁| > 0 := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hgap))
  refine ⟨(2 * (M₁ * M₀) + (M₂ * M₀ + M₁ * M₁)) / |e₂ - e₁| * Real.exp (M₁ + 1), ?_, ?_⟩
  · positivity
  intro ε hε ψ hψ hinit s hs
  -- notation
  have hψcont : Continuous ψ := continuous_iff_continuousAt.mpr fun t => (hψ t).continuousAt
  have hN : ∀ t, ‖ψ t‖ = ‖ψ 0‖ := norm_sol_eq P e₁ e₂ ε hsa ψ hψ
  have hNn : 0 ≤ ‖ψ 0‖ := norm_nonneg _
  set N := ‖ψ 0‖ with hNdef
  set α : ℝ → E := alph P e₁ ε ψ with hαdef
  set χ : ℝ → E := chi P e₂ ε ψ with hχdef
  set Dα : ℝ → E := fun u => cphase (e₁ / ε) u • DP u (ψ u) with hDαdef
  have hαd : ∀ u, HasDerivAt α (Dα u) u := alph_hasDerivAt P DP e₁ e₂ ε ψ hP hidem hψ
  have hαcont : Continuous α := continuous_iff_continuousAt.mpr fun u => (hαd u).continuousAt
  have hDαcont : Continuous Dα :=
    (cphase_continuous _).smul (hDPcont.clm_apply hψcont)
  set f : ℝ → E := fun u => DP u (α u) with hfdef
  set Df : ℝ → E := fun u => D2P u (α u) + DP u (Dα u) with hDfdef
  have hfd : ∀ u, HasDerivAt f (Df u) u := fun u =>
    hasDerivAt_clmApply DP D2P α _ _ u (hDP u) (hαd u) rfl
  have hDfcont : Continuous Df := (hD2P.clm_apply hαcont).add (hDPcont.clm_apply hDαcont)
  -- uniform bounds on the source term
  have hαbound : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖α u‖ ≤ M₀ * N := by
    intro u hu
    rw [hαdef, norm_alph]
    calc ‖P u (ψ u)‖ ≤ ‖P u‖ * ‖ψ u‖ := (P u).le_opNorm _
      _ ≤ M₀ * N := by rw [hN u]; exact mul_le_mul_of_nonneg_right (hM₀ u hu) hNn
  have hDαbound : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖Dα u‖ ≤ M₁ * N := by
    intro u hu
    rw [hDαdef]
    simp only [norm_smul, norm_cphase, one_mul]
    calc ‖DP u (ψ u)‖ ≤ ‖DP u‖ * ‖ψ u‖ := (DP u).le_opNorm _
      _ ≤ M₁ * N := by rw [hN u]; exact mul_le_mul_of_nonneg_right (hM₁ u hu) hNn
  have hA : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖f u‖ ≤ M₁ * (M₀ * N) := by
    intro u hu
    calc ‖f u‖ ≤ ‖DP u‖ * ‖α u‖ := (DP u).le_opNorm _
      _ ≤ M₁ * (M₀ * N) :=
        mul_le_mul (hM₁ u hu) (hαbound u hu) (norm_nonneg _) hM₁n
  have hB : ∀ u ∈ Set.Icc (0:ℝ) 1, ‖Df u‖ ≤ M₂ * (M₀ * N) + M₁ * (M₁ * N) := by
    intro u hu
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖D2P u (α u)‖ ≤ ‖D2P u‖ * ‖α u‖ := (D2P u).le_opNorm _
        _ ≤ M₂ * (M₀ * N) := mul_le_mul (hM₂ u hu) (hαbound u hu) (norm_nonneg _) hM₂n
    · calc ‖DP u (Dα u)‖ ≤ ‖DP u‖ * ‖Dα u‖ := (DP u).le_opNorm _
        _ ≤ M₁ * (M₁ * N) := mul_le_mul (hM₁ u hu) (hDαbound u hu) (norm_nonneg _) hM₁n
  -- the oscillatory integral
  set ω : ℝ := (e₂ - e₁) / ε with hωdef
  have hωne : ω ≠ 0 := div_ne_zero (sub_ne_zero.mpr (Ne.symm hgap)) (ne_of_gt hε)
  set Kⱼ : ℝ := (2 * (M₁ * (M₀ * N)) + (M₂ * (M₀ * N) + M₁ * (M₁ * N))) * ε / |e₂ - e₁| with hKⱼdef
  have hKⱼn : 0 ≤ Kⱼ := by
    rw [hKⱼdef]
    positivity
  set J : ℝ → E := fun t => ∫ u in (0:ℝ)..t, cphase ω u • f u with hJdef
  have hJbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖J t‖ ≤ Kⱼ := by
    intro t ht
    have := osc_integral_bound f Df hfd hDfcont ω (M₁ * (M₀ * N))
      (M₂ * (M₀ * N) + M₁ * (M₁ * N)) hωne hA hB t ht
    have habs : |ω| = |e₂ - e₁| / ε := by
      rw [hωdef, abs_div, abs_of_pos hε]
    rw [habs] at this
    calc ‖J t‖ ≤ (2 * (M₁ * (M₀ * N)) + (M₂ * (M₀ * N) + M₁ * (M₁ * N))) / (|e₂ - e₁| / ε) := this
      _ = Kⱼ := by rw [hKⱼdef]; field_simp
  have hJd : ∀ t, HasDerivAt J (cphase ω t • f t) t := by
    intro t
    have hgc : Continuous (fun u => cphase ω u • f u) :=
      (cphase_continuous ω).smul (continuous_iff_continuousAt.mpr fun u => (hfd u).continuousAt)
    exact intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      (hgc.stronglyMeasurableAtFilter _ _) hgc.continuousAt
  -- the Gronwall functional
  set ξ : ℝ → E := fun t => χ t + J t with hξdef
  have hξd : ∀ t, HasDerivAt ξ (-(DP t (χ t))) t := by
    intro t
    refine ((chi_deriv_split P DP e₁ e₂ ε ψ hP hidem hψ t).add (hJd t)).congr_deriv ?_
    abel
  have hξ0 : ξ 0 = 0 := by
    have h1 : χ 0 = 0 := by
      rw [hχdef, chi, hinit, sub_self, smul_zero]
    have h2 : J 0 = 0 := by rw [hJdef]; simp
    rw [hξdef]
    simp [h1, h2]
  have hχbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖χ t‖ ≤ ‖ξ t‖ + Kⱼ := by
    intro t ht
    have hct : χ t = ξ t - J t := by simp [hξdef]
    rw [hct]
    calc ‖ξ t - J t‖ ≤ ‖ξ t‖ + ‖J t‖ := norm_sub_le _ _
      _ ≤ ‖ξ t‖ + Kⱼ := by linarith [hJbound t ht]
  have hgron := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := ξ) (f' := fun t => -(DP t (χ t))) (δ := 0) (K := M₁ + 1) (ε := (M₁ + 1) * Kⱼ)
    (a := 0) (b := 1)
    (continuous_iff_continuousAt.mpr fun t => (hξd t).continuousAt).continuousOn
    (fun x _ => (hξd x).hasDerivWithinAt)
    (by rw [hξ0]; simp)
    (by
      intro x hx
      have hx' : x ∈ Set.Icc (0:ℝ) 1 := Set.mem_Icc_of_Ico hx
      calc ‖-(DP x (χ x))‖ = ‖DP x (χ x)‖ := by rw [norm_neg]
        _ ≤ ‖DP x‖ * ‖χ x‖ := (DP x).le_opNorm _
        _ ≤ M₁ * (‖ξ x‖ + Kⱼ) :=
          mul_le_mul (hM₁ x hx') (hχbound x hx') (norm_nonneg _) hM₁n
        _ ≤ (M₁ + 1) * ‖ξ x‖ + (M₁ + 1) * Kⱼ := by nlinarith [norm_nonneg (ξ x)])
  have hgs := hgron s hs
  have hKne : (M₁ + 1 : ℝ) ≠ 0 := by positivity
  have hform : gronwallBound 0 (M₁ + 1) ((M₁ + 1) * Kⱼ) (s - 0)
      = Kⱼ * (Real.exp ((M₁ + 1) * s) - 1) := by
    rw [sub_zero, gronwallBound_of_K_ne_0 hKne]
    field_simp
    ring
  rw [hform] at hgs
  have hfin : ‖ψ s - P s (ψ s)‖ ≤ Kⱼ * Real.exp (M₁ + 1) := by
    have h1 : ‖ψ s - P s (ψ s)‖ = ‖χ s‖ := by rw [hχdef, norm_chi]
    have h2 : ‖χ s‖ ≤ ‖ξ s‖ + Kⱼ := hχbound s hs
    have h3 : Real.exp ((M₁ + 1) * s) ≤ Real.exp (M₁ + 1) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hs.1, hs.2]
    rw [h1]
    nlinarith [hgs, h2, hKⱼn]
  refine le_trans hfin (le_of_eq ?_)
  rw [hKⱼdef]
  field_simp

/-- The hypotheses of `Phys.adiabatic_theorem` are consistent: they are satisfied by the
one-dimensional system with `P s = 1`, whose Schrödinger equation has the explicit solution
`ψ s = exp (-i e₁ s / ε)`, a state of norm one (in particular a nonzero state). -/
theorem adiabatic_hypotheses_satisfiable (e₁ e₂ ε : ℝ) :
    ∃ (P DP D2P : ℝ → ℂ →L[ℂ] ℂ) (ψ : ℝ → ℂ),
      (∀ s, HasDerivAt P (DP s) s) ∧ (∀ s, HasDerivAt DP (D2P s) s) ∧ Continuous D2P ∧
      (∀ s, (P s).comp (P s) = P s) ∧ (∀ s, IsSelfAdjoint (P s)) ∧
      (∀ s, HasDerivAt ψ ((-Complex.I / (ε : ℂ)) • (ham P e₁ e₂ s (ψ s))) s) ∧
      P 0 (ψ 0) = ψ 0 ∧ ψ 0 ≠ 0 := by
  refine ⟨fun _ => ContinuousLinearMap.id ℂ ℂ, fun _ => 0, fun _ => 0,
    cphase (-(e₁ / ε)), fun s => hasDerivAt_const s _, fun s => hasDerivAt_const s _,
    continuous_const, fun s => ContinuousLinearMap.id_comp _, fun s => ?_, fun s => ?_, rfl, ?_⟩
  · exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun v w => rfl
  · refine (cphase_hasDerivAt (-(e₁ / ε)) s).congr_deriv ?_
    simp only [ham, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, sub_self,
      smul_eq_mul, smul_zero, add_zero]
    push_cast
    ring
  · exact cphase_ne_zero _ 0

end

end Phys

