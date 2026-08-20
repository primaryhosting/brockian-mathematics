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

/-
Essential self-adjointness via the basic criterion on deficiency subspaces.

This file develops, for an unbounded (partially defined) operator on a complex Hilbert
space, the classical criterion of von Neumann/Weyl:

  a densely defined symmetric operator `T` is essentially self-adjoint as soon as the two
  deficiency subspaces `ker (T† - i)` and `ker (T† + i)` are trivial.

Along the way we show that under this hypothesis the closure of `T` coincides with the
adjoint `T†`.
-/
import Mathlib

namespace Brockian.Weyl

open LinearPMap Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator on a Hilbert space is *essentially self-adjoint* if its closure is
self-adjoint. -/

theorem inner_isReal_of_weak_second_derivative (u w : L2R)
    (h : ∀ f : 𝓢(ℝ, ℂ), ⟪w, toL2 f⟫ = ⟪u, toL2 (-(D2 f))⟫) :
    conj ⟪u, w⟫ = ⟪u, w⟫ := by
  set a : ℝ → ℂ := ((𝓕 u : L2R) : ℝ → ℂ) with ha
  set b : ℝ → ℂ := ((𝓕 w : L2R) : ℝ → ℂ) with hb
  -- Step 1: on the Fourier side, `ŵ = (2πξ)² û` in the weak sense
  have key : ∀ ψ : 𝓢(ℝ, ℂ),
      ∫ x, conj (b x) * ψ x = ∫ x, conj (a x) * ((symb x : ℂ) * ψ x) := by
    intro ψ
    have hFψ : (𝓕 (𝓕⁻ ψ) : 𝓢(ℝ, ℂ)) = ψ := FourierTransform.fourier_fourierInv_eq ψ
    have hL : ⟪w, toL2 (𝓕⁻ ψ)⟫ = ∫ x, conj (b x) * ψ x := by
      rw [← Lp.inner_fourier_eq w (toL2 (𝓕⁻ ψ)), fourier_toL2, hFψ, inner_L2_toL2]
    have hR : ⟪u, toL2 (-(D2 (𝓕⁻ ψ)))⟫ = ∫ x, conj (a x) * ((symb x : ℂ) * ψ x) := by
      rw [← Lp.inner_fourier_eq u (toL2 (-(D2 (𝓕⁻ ψ)))), fourier_toL2, inner_L2_toL2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [fourier_neg_D2, hFψ]
    rw [← hL, ← hR, h]
  -- Step 2: local integrability of the relevant functions
  have hloc_a : LocallyIntegrable a volume := (Lp.memLp (𝓕 u)).locallyIntegrable (by norm_num)
  have hloc_b : LocallyIntegrable b volume := (Lp.memLp (𝓕 w)).locallyIntegrable (by norm_num)
  have hloc_sa : LocallyIntegrable (fun x => (symb x : ℂ) * a x) volume := by
    rw [← locallyIntegrableOn_univ] at hloc_a ⊢
    refine hloc_a.continuousOn_mul ?_ (IsClosed.isLocallyClosed isClosed_univ)
    exact (Complex.continuous_ofReal.comp continuous_symb).continuousOn
  have hF : LocallyIntegrable (fun x => b x - (symb x : ℂ) * a x) volume := hloc_b.sub hloc_sa
  -- Step 3: test against real-valued test functions
  have hzero : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • (b x - (symb x : ℂ) * a x) = 0 := by
    intro g hgs hgc
    have h1 : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hgs
    set ψ : 𝓢(ℝ, ℂ) := h1.toSchwartzMap (by exact_mod_cast h2) with hψdef
    have hψ : ⇑ψ = fun x => (g x : ℂ) := rfl
    have hk := key ψ
    rw [hψ] at hk
    have hk2 : ∫ x, b x * (g x : ℂ) = ∫ x, a x * ((symb x : ℂ) * (g x : ℂ)) := by
      have hc := congrArg conj hk
      rw [← integral_conj, ← integral_conj] at hc
      simpa [map_mul, Complex.conj_ofReal] using hc
    have hint1 : Integrable (fun x => g x • b x) volume :=
      hloc_b.integrable_smul_left_of_hasCompactSupport hgs.continuous hgc
    have hint2 : Integrable (fun x => g x • ((symb x : ℂ) * a x)) volume :=
      hloc_sa.integrable_smul_left_of_hasCompactSupport hgs.continuous hgc
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, sub_eq_zero]
    simp only [Complex.real_smul]
    rw [show (∫ (x : ℝ), (g x : ℂ) * b x) = ∫ (x : ℝ), b x * (g x : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), hk2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hF hzero
  have hbe : ∀ᵐ x : ℝ, b x = (symb x : ℂ) * a x := by
    filter_upwards [hae] with x hx
    exact sub_eq_zero.1 hx
  -- Step 4: conclude
  have hinner : ⟪u, w⟫ = ∫ x, conj (a x) * b x := by
    rw [← Lp.inner_fourier_eq u w, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [RCLike.inner_apply]
    ring
  rw [hinner, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hbe] with x hx
  rw [hx]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-! ### The main theorem -/

section Main

variable {V : ℝ → ℝ} {C : ℝ}

/-- Elements of the deficiency space of the minimal Schrödinger operator are weak solutions of
the deficiency ODE `-u'' + V u = z u`. -/
