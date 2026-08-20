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

import Mathlib
/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Real FourierTransform ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-! ### An abstract criterion for essential self-adjointness

We use the classical *basic criterion* (von Neumann's deficiency criterion): a densely defined
symmetric operator `T` on a Hilbert space is essentially self-adjoint if and only if the ranges of
`T + i` and `T - i` are dense.  Here the operator is given on a core `D` (an abstract vector space,
mapped into the Hilbert space by `ι`, e.g. the Schwartz space sitting inside `L²`). -/

/-- `IsEssentiallySelfAdjointCore ι T` states that the operator `T`, acting on the core `D` which is
embedded into the Hilbert space `H` via `ι`, is a densely defined symmetric operator whose
deficiency spaces are trivial, i.e. the ranges of `T ± i` are dense.  By von Neumann's basic
criterion this is exactly essential self-adjointness of `T` on the core `ι '' D`. -/
structure IsEssentiallySelfAdjointCore {D H : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : D →ₗ[ℂ] H) (T : D →ₗ[ℂ] D) : Prop where
  /-- the core is dense in the Hilbert space -/
  dense_domain : Dense (Set.range ι)
  /-- the operator is symmetric on the core -/
  symmetric : ∀ f g : D, inner ℂ (ι (T f)) (ι g) = inner ℂ (ι f) (ι (T g))
  /-- the range of `T + i` is dense -/
  dense_range_add_I : Dense (Set.range fun f : D => ι (T f) + Complex.I • ι f)
  /-- the range of `T - i` is dense -/
  dense_range_sub_I : Dense (Set.range fun f : D => ι (T f) - Complex.I • ι f)

/-! ### The free Laplacian on the Schwartz space -/

/-- The free Laplacian `-d²/dx²` acting on the Schwartz space `𝓢(ℝ, ℂ)`. -/

theorem dense_range_freeLaplacian_add_const {c : ℂ} (hc : c.im ≠ 0) :
    Dense (Set.range fun f : 𝓢(ℝ, ℂ) =>
      schwartzToL2 (freeLaplacian f) + c • schwartzToL2 f) := by
  set L : 𝓢(ℝ, ℂ) →ₗ[ℂ] Lp (α := ℝ) ℂ 2 :=
    (schwartzToL2.comp freeLaplacian + c • schwartzToL2).toLinearMap
  have hLapp : ∀ f, L f = schwartzToL2 (freeLaplacian f) + c • schwartzToL2 f := fun f => rfl
  have : (Set.range fun f : 𝓢(ℝ, ℂ) => schwartzToL2 (freeLaplacian f) + c • schwartzToL2 f)
      = Set.range L := by
    ext y; constructor <;> rintro ⟨f, rfl⟩ <;> exact ⟨f, by rw [hLapp]⟩
  rw [this]
  refine dense_range_of_inner_eq_zero L fun u hu => ?_
  set v : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 u with hv
  -- On the Fourier side, testing against `u` becomes testing against `(4π²ξ² + conj c) v`.
  set G : ℝ → ℂ := fun ξ => ((lapMultiplier ξ : ℂ) + (starRingEnd ℂ) c) * v ξ with hG
  have key : ∀ h : 𝓢(ℝ, ℂ), ∫ ξ, (starRingEnd ℂ) (h ξ) * G ξ = 0 := by
    intro h
    have h0 := hu (𝓕⁻ h)
    -- transport to the Fourier side using Plancherel
    have e1 : 𝓕 (L (𝓕⁻ h))
        = (𝓕 (freeLaplacian (𝓕⁻ h)) + c • h : 𝓢(ℝ, ℂ)).toLp 2 volume := by
      have hsum : ((𝓕 (freeLaplacian (𝓕⁻ h)) + c • h : 𝓢(ℝ, ℂ))).toLp 2 volume
          = (𝓕 (freeLaplacian (𝓕⁻ h)) : 𝓢(ℝ, ℂ)).toLp 2 volume + c • h.toLp 2 volume := by
        have ha := (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_add
          (𝓕 (freeLaplacian (𝓕⁻ h)) : 𝓢(ℝ, ℂ)) (c • h)
        have hs := (toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_smul c h
        simp only [toLpCLM_apply] at ha hs
        rw [ha, hs]
      rw [hLapp, hsum, schwartzToL2_apply, schwartzToL2_apply, FourierAdd.fourier_add, fourier_smul,
        SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, fourier_fourierInv_eq]
    have e2 : inner ℂ (𝓕 (L (𝓕⁻ h))) v = 0 := by
      rw [hv, Lp.inner_fourier_eq]
      exact h0
    rw [e1, inner_toLp_eq_integral] at e2
    rw [← e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hw : (𝓕 (freeLaplacian (𝓕⁻ h)) + c • h : 𝓢(ℝ, ℂ)) ξ
        = (lapMultiplier ξ : ℂ) * h ξ + c * h ξ := by
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, fourier_freeLaplacian_apply,
        fourier_fourierInv_eq]
      simp [smul_eq_mul]
    simp only [hw, hG, map_add, map_mul, Complex.conj_ofReal]
    ring
  -- Hence `(4π²ξ² + conj c) v = 0` a.e.
  have hGloc : LocallyIntegrable G volume := by
    refine locallyIntegrable_mul_Lp v ?_
    have : Continuous fun ξ : ℝ => (lapMultiplier ξ : ℂ) := by
      simp only [lapMultiplier]
      fun_prop
    exact this.add continuous_const
  have hGzero : ∀ᵐ ξ, G ξ = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hGloc fun g hg1 hg2 => ?_
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hg2.comp_left rfl
    have hg₂ : ContDiff ℝ (⊤ : ℕ∞) (Complex.ofRealCLM ∘ g) := by fun_prop
    have hk := key (hg₁.toSchwartzMap hg₂)
    rw [← hk]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have : (hg₁.toSchwartzMap hg₂ : 𝓢(ℝ, ℂ)) ξ = (g ξ : ℂ) := rfl
    simp only [this, Complex.conj_ofReal, Complex.real_smul]
  -- Since `4π²ξ² + conj c ≠ 0`, we get `v = 0`, hence `u = 0`.
  have hvzero : v = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [hGzero] with ξ hξ
    have hne : ((lapMultiplier ξ : ℂ) + (starRingEnd ℂ) c) ≠ 0 := by
      intro hzero
      apply hc
      have := congrArg Complex.im hzero
      simp [Complex.add_im, Complex.conj_im] at this
      exact this
    have := mul_eq_zero.1 hξ
    rcases this with h1 | h2
    · exact absurd h1 hne
    · simpa using h2
  have : u = 𝓕⁻ v := by rw [hv, fourierInv_fourier_eq]
  rw [this, hvzero]
  simp

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space.**

The operator `-d²/dx²`, defined on the Schwartz space `𝓢(ℝ, ℂ)` viewed as a dense subspace of
`L²(ℝ)`, is a densely defined symmetric operator both of whose deficiency spaces are trivial; by
von Neumann's basic criterion it is therefore essentially self-adjoint.  All three ingredients are
obtained from Plancherel's theorem, which conjugates the free Laplacian into multiplication by the
real function `ξ ↦ 4π²ξ²`. -/
