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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is a plain block comment because Lean requires `import` to precede any
-- module docstring; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv FourierTransform Real LinearPMap
open scoped ComplexConjugate

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`, the configuration space of the free particle. -/
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
noncomputable abbrev Hs (d : ℕ) := Lp ℂ 2 (volume : Measure (Space d))

variable {d : ℕ}

/-- The symbol (Fourier multiplier) of `-Δ`, namely `4π²‖ξ‖²`. -/

lemma fourier_of_formal (u w : Hs d)
    (h : ∀ f : 𝓢(Space d, ℂ), inner ℂ w (f.toLp 2 (volume : Measure (Space d)))
      = inner ℂ u ((-Δ f).toLp 2 (volume : Measure (Space d)))) :
    (fun ξ => (𝓕 w) ξ) =ᵐ[(volume : Measure (Space d))] fun ξ => (symbol ξ : ℂ) * (𝓕 u) ξ := by
  -- On the Fourier side, testing against `g` amounts to testing against `symbol * g`.
  have key : ∀ g : 𝓢(Space d, ℂ), ∫ ξ, conj ((𝓕 w) ξ) * g ξ
      = ∫ ξ, conj ((𝓕 u) ξ) * ((symbol ξ : ℂ) * g ξ) := by
    intro g
    set f : 𝓢(Space d, ℂ) := 𝓕⁻ g with hf
    have hfg : 𝓕 f = g := by rw [hf]; exact FourierTransform.fourier_fourierInv_eq g
    have e1 : inner ℂ (𝓕 w) (g.toLp 2 (volume : Measure (Space d)))
        = inner ℂ w (f.toLp 2 (volume : Measure (Space d))) := by
      rw [← hfg, ← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
    have e2 : inner ℂ u ((-Δ f).toLp 2 (volume : Measure (Space d)))
        = inner ℂ (𝓕 u) ((𝓕 (-Δ f)).toLp 2 (volume : Measure (Space d))) := by
      rw [← SchwartzMap.toLp_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
    have e3 := e1.trans ((h f).trans e2)
    rw [inner_toLp, inner_toLp] at e3
    rw [e3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    dsimp only
    rw [fourier_freeLaplacian_apply, hfg]
  -- Now use that a locally integrable function is determined by its action on test functions.
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 w)).locallyIntegrable one_le_two) (locallyIntegrable_symbol_mul (𝓕 u)) ?_
  intro φ hφ hφc
  have hcd := Complex.ofRealCLM.contDiff.comp hφ
  have hcs : HasCompactSupport (fun x : Space d => (φ x : ℂ)) :=
    hφc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  set g : 𝓢(Space d, ℂ) := hcs.toSchwartzMap hcd with hg
  have hgval : ∀ x, g x = (φ x : ℂ) := fun _ => rfl
  have h1 := key g
  simp only [hgval] at h1
  have hconj := congrArg (starRingEnd ℂ) h1
  rw [← integral_conj, ← integral_conj] at hconj
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at hconj
  refine (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)).trans
    (hconj.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)))
  · simp only [Complex.real_smul]; ring
  · simp only [Complex.real_smul]; ring

/-- Every element of the domain of the adjoint is described on the Fourier side by multiplication
with the symbol. -/
