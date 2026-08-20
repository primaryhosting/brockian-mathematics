import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open MeasureTheory

namespace Frontier

/-!
## Overview

We formalize, and prove, the one–dimensional base case of the Lieb–Thirring family of
inequalities, in its variational (quadratic form) formulation, which is exactly the
statement of *stability* for a one–dimensional one–particle Schrödinger operator
`H = -d²/dx² + V`:

for every `C¹` test function `ψ` of compact support,
`⟪ψ, Hψ⟫ = ∫ |ψ'|² + ∫ V |ψ|² ≥ - (1/4) (∫ V₋)² ∫ |ψ|²`,

where `V₋ x = max (-V x) 0` is the negative part of the potential.  Equivalently, the
bottom of the spectrum obeys `E₀ ≥ -(1/4) (∫ V₋)²`, i.e. `|E₀|^{1/2} ≤ (1/2) ∫ V₋`,
which is the `γ = 1/2`, `d = 1` Lieb–Thirring bound restricted to a single bound state,
with the sharp constant `L_{1/2,1} = 1/2`.

The proof is the classical one:

* `Frontier.sq_le_integral_abs_mul_abs` : `|ψ(x)|² ≤ ∫ |ψ| |ψ'|`
  (fundamental theorem of calculus, applied to `ψ²` from both `-∞` and `+∞`);
* `Frontier.integral_abs_mul_abs_le_sqrt_mul_sqrt` : `∫ |ψ| |ψ'| ≤ ‖ψ‖₂ ‖ψ'‖₂`
  (Cauchy–Schwarz, i.e. Hölder with `p = q = 2`, via
  `MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`);
* hence `∫ V |ψ|² ≥ - ‖ψ‖_∞² ∫ V₋ ≥ - ‖ψ‖₂ ‖ψ'‖₂ ∫ V₋`, and the result follows from
  `(‖ψ'‖₂ - ‖ψ‖₂ (∫ V₋)/2)² ≥ 0`.

Mathlib does not contain the Lieb–Thirring inequality (nor Schrödinger operator spectral
theory), so no single existing lemma closes the goal; the Mathlib inputs used are cited
above and in the individual proofs.
-/

/-- **Cauchy–Schwarz** for two continuous, compactly supported functions on `ℝ`:
`∫ |f| |g| ≤ (∫ f²)^(1/2) (∫ g²)^(1/2)`.  This is Hölder's inequality with `p = q = 2`
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`). -/

theorem integral_abs_mul_abs_le_sqrt_mul_sqrt
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    ∫ x, |f x| * |g x| ≤ Real.sqrt (∫ x, f x ^ 2) * Real.sqrt (∫ x, g x ^ 2) := by
  have h2 : (2 : ℝ).HolderConjugate 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  have hmf : MemLp (fun x => |f x|) (ENNReal.ofReal 2) volume :=
    hf.abs.memLp_of_hasCompactSupport hfs.abs
  have hmg : MemLp (fun x => |g x|) (ENNReal.ofReal 2) volume :=
    hg.abs.memLp_of_hasCompactSupport hgs.abs
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) h2
    (f := fun x => |f x|) (g := fun x => |g x|)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)
    (Filter.Eventually.of_forall fun x => abs_nonneg _) hmf hmg
  simpa [Real.rpow_two, Real.sqrt_eq_rpow, sq_abs] using h

/-- If `ψ` is everywhere differentiable with derivative `dψ` and has compact support, then
`dψ` has compact support as well. -/

theorem hasCompactSupport_of_hasDerivAt
    (ψ dψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt ψ (dψ x) x) (hs : HasCompactSupport ψ) :
    HasCompactSupport dψ := by
  apply HasCompactSupport.intro hs.isCompact
  intro x hx
  have hopen : IsOpen (tsupport ψ)ᶜ := (isClosed_tsupport ψ).isOpen_compl
  have h0 : HasDerivAt ψ 0 x := by
    have hev : ψ =ᶠ[nhds x] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hev
  exact (hd x).unique h0

/-- **Pointwise sup bound.**  For a `C¹` function `ψ : ℝ → ℝ` of compact support with
derivative `dψ`, one has `ψ(x)² ≤ ∫ |ψ| |dψ|` for every `x`.

This is the one–dimensional Gagliardo–Nirenberg/Sobolev estimate `‖ψ‖_∞² ≤ ‖ψ‖₂ ‖ψ'‖₂`
before Cauchy–Schwarz is applied. -/

theorem sq_le_integral_abs_mul_abs
    (ψ dψ : ℝ → ℝ) (hd : ∀ x, HasDerivAt ψ (dψ x) x) (hc : Continuous dψ)
    (hs : HasCompactSupport ψ) (x : ℝ) :
    ψ x ^ 2 ≤ ∫ y, |ψ y| * |dψ y| := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  set g : ℝ → ℝ := fun y => 2 * ψ y * dψ y with hg
  have hgc : Continuous g := by fun_prop
  have hgs : HasCompactSupport g := HasCompactSupport.mul_right hs.mul_left
  have hgi : Integrable g volume := hgc.integrable_of_hasCompactSupport hgs
  have habs : Integrable (fun y => |g y|) volume := hgi.abs
  obtain ⟨R, hR0, hR⟩ := hs.exists_pos_le_norm
  have hψa : ψ (-R) = 0 := hR _ (by simp [abs_of_pos hR0])
  have hψb : ψ R = 0 := hR _ (by simp [abs_of_pos hR0])
  have hgtot : ∫ y, |g y| = 2 * ∫ y, |ψ y| * |dψ y| := by
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [hg, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    ring
  have hnn : 0 ≤ ∫ y, |ψ y| * |dψ y| := by
    apply integral_nonneg; intro y; positivity
  -- fundamental theorem of calculus for `ψ²`
  have hFTC : ∀ u v : ℝ, ∫ y in u..v, g y = ψ v ^ 2 - ψ u ^ 2 := by
    intro u v
    have h : ∀ y ∈ Set.uIcc u v, HasDerivAt (fun t => ψ t ^ 2) (g y) y := by
      intro y _
      simpa [hg] using ((hd y).pow 2).congr_deriv (by ring)
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h hgi.intervalIntegrable
  by_cases hx : -R ≤ x ∧ x ≤ R
  · obtain ⟨h1, h2⟩ := hx
    have e1 : ∫ y in (-R)..x, g y = ψ x ^ 2 := by rw [hFTC, hψa]; ring
    have e2 : ∫ y in x..R, g y = -(ψ x ^ 2) := by rw [hFTC, hψb]; ring
    have b1 : ψ x ^ 2 ≤ ∫ y in (-R)..x, |g y| := by
      rw [← e1]
      exact le_trans (le_abs_self _) (intervalIntegral.abs_integral_le_integral_abs h1)
    have b2 : ψ x ^ 2 ≤ ∫ y in x..R, |g y| := by
      have h : |∫ y in x..R, g y| ≤ ∫ y in x..R, |g y| :=
        intervalIntegral.abs_integral_le_integral_abs h2
      rw [e2] at h
      simpa using h
    have badd : (∫ y in (-R)..x, |g y|) + (∫ y in x..R, |g y|) = ∫ y in (-R)..R, |g y| :=
      intervalIntegral.integral_add_adjacent_intervals
        habs.intervalIntegrable habs.intervalIntegrable
    have key : ∫ y in (-R)..R, |g y| ≤ ∫ y, |g y| := by
      rw [intervalIntegral.integral_of_le (by linarith)]
      exact setIntegral_le_integral habs (Filter.Eventually.of_forall fun y => abs_nonneg _)
    linarith [hgtot ▸ key]
  · have hzero : ψ x = 0 := by
      apply hR
      rw [Real.norm_eq_abs]
      rcases not_and_or.1 hx with h | h <;> cases abs_cases x <;> linarith
    simp [hzero, hnn]

/-- **Lieb–Thirring stability bound (one dimension, one particle, sharp constant).**

Let `V : ℝ → ℝ` be a potential whose negative part `V₋ x = max (-V x) 0` is integrable,
and let `ψ : ℝ → ℝ` be a `C¹` function with compact support (a form-core element of the
Schrödinger operator `H = -d²/dx² + V`).  Then the energy quadratic form of `H` is bounded
below:

`∫ |ψ'|² + ∫ V |ψ|² ≥ - (1/4) (∫ V₋)² ∫ |ψ|²`.

For normalized `ψ` this says that the ground state energy satisfies
`E₀ ≥ -(1/4) (∫ V₋)²`, i.e. `|E₀|^{1/2} ≤ (1/2) ∫ V₋`, which is the Lieb–Thirring
inequality for `γ = 1/2` in dimension `1` restricted to a single bound state, with the
sharp constant `L_{1/2,1} = 1/2`.  In particular the one–body Hamiltonian is stable:
its energy is bounded below by a constant depending only on the potential. -/

theorem lieb_thirring_stability
    (ψ dψ V : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt ψ (dψ x) x)
    (hc : Continuous dψ)
    (hs : HasCompactSupport ψ)
    (hV : Integrable (fun x => max (-V x) 0) volume)
    (hVψ : Integrable (fun x => V x * ψ x ^ 2) volume) :
    -(1 / 4) * (∫ x, max (-V x) 0) ^ 2 * (∫ x, ψ x ^ 2)
      ≤ (∫ x, dψ x ^ 2) + ∫ x, V x * ψ x ^ 2 := by
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  set M : ℝ := ∫ y, |ψ y| * |dψ y| with hM
  have hsup : ∀ x, ψ x ^ 2 ≤ M := sq_le_integral_abs_mul_abs ψ dψ hd hc hs
  have hMnn : 0 ≤ M := le_trans (sq_nonneg (ψ 0)) (hsup 0)
  -- the negative part of `V`, and its integral
  set B : ℝ := ∫ x, max (-V x) 0 with hB
  have hBnn : 0 ≤ B := integral_nonneg fun x => le_max_right _ _
  -- integrability of `V₋ · ψ²`
  have hint : Integrable (fun x => max (-V x) 0 * ψ x ^ 2) volume := by
    have hb : Integrable (fun x => ψ x ^ 2 * max (-V x) 0) volume :=
      hV.bdd_mul (by fun_prop)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hsup x)
    simpa [mul_comm] using hb
  -- Step 1 : `∫ V ψ² ≥ - ∫ V₋ ψ²`
  have step1 : -(∫ x, max (-V x) 0 * ψ x ^ 2) ≤ ∫ x, V x * ψ x ^ 2 := by
    rw [← integral_neg]
    refine integral_mono hint.neg hVψ fun x => ?_
    have h : -max (-V x) 0 ≤ V x := by
      rcases max_cases (-V x) (0:ℝ) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
    simpa using mul_le_mul_of_nonneg_right h (sq_nonneg (ψ x))
  -- Step 2 : `∫ V₋ ψ² ≤ M * B`
  have step2 : (∫ x, max (-V x) 0 * ψ x ^ 2) ≤ M * B := by
    have h : (∫ x, max (-V x) 0 * ψ x ^ 2) ≤ ∫ x, max (-V x) 0 * M := by
      refine integral_mono hint (hV.mul_const M) fun x => ?_
      exact mul_le_mul_of_nonneg_left (hsup x) (le_max_right _ _)
    rw [integral_mul_const, ← hB] at h
    linarith
  -- Step 3 : Cauchy–Schwarz, `M ≤ ‖ψ‖₂ ‖ψ'‖₂`
  have step3 : M ≤ Real.sqrt (∫ x, ψ x ^ 2) * Real.sqrt (∫ x, dψ x ^ 2) :=
    integral_abs_mul_abs_le_sqrt_mul_sqrt ψ dψ hψc hc hs
      (hasCompactSupport_of_hasDerivAt ψ dψ hd hs)
  -- Step 4 : optimize
  set N : ℝ := ∫ x, ψ x ^ 2 with hN
  set A : ℝ := ∫ x, dψ x ^ 2 with hA
  have hNnn : 0 ≤ N := integral_nonneg fun x => sq_nonneg _
  have hAnn : 0 ≤ A := integral_nonneg fun x => sq_nonneg _
  have hsN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNnn
  have hsA : Real.sqrt A ^ 2 = A := Real.sq_sqrt hAnn
  have hkey : -(1 / 4) * B ^ 2 * N ≤ A - M * B := by
    have hMB : M * B ≤ Real.sqrt N * Real.sqrt A * B :=
      mul_le_mul_of_nonneg_right step3 hBnn
    nlinarith [sq_nonneg (Real.sqrt A - Real.sqrt N * B / 2), Real.sqrt_nonneg N,
      Real.sqrt_nonneg A]
  linarith [step1, step2]

/-- **Ground state energy bound.**  For a normalized `C¹` test function of compact support,
the energy of the one–dimensional Schrödinger operator `-d²/dx² + V` is at least
`-(1/4) (∫ V₋)²`; equivalently `|E|^{1/2} ≤ (1/2) ∫ V₋`. -/
