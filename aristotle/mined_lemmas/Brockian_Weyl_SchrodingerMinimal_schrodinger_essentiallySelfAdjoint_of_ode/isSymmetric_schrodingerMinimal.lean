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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/

theorem isSymmetric_schrodingerMinimal (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) :
    Brockian.Weyl.IsSymmetricPMap (schrodingerMinimal V hV) := by
  intro a b
  obtain ⟨f, hf⟩ := a.2
  obtain ⟨g, hg⟩ := b.2
  have hfT := isTestFn_of_mem f.2
  have hgT := isTestFn_of_mem g.2
  rw [schrodingerMinimal_apply hV f a hf.symm, schrodingerMinimal_apply hV g b hg.symm, ← hf, ← hg,
    inner_testToL2, inner_testToL2]
  have hFT : IsTestFn (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y)) := hfT.conj
  have hA : Integrable (fun x => (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x)
      (volume : Measure ℝ) :=
    integrable_mul_of_isTestFn ((isTestFn_schExpr hV hfT).conj) hgT
  have hB : Integrable (fun x => (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x)
      (volume : Measure ℝ) :=
    integrable_mul_of_isTestFn hFT (isTestFn_schExpr hV hgT)
  have hpoint : ∀ x : ℝ, (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x
      - (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x
      = -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x)
        + (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x := by
    intro x
    show (starRingEnd ℂ) (schExpr V (f : ℝ → ℂ) x) * (g : ℝ → ℂ) x
      - (starRingEnd ℂ) ((f : ℝ → ℂ) x) * schExpr V (g : ℝ → ℂ) x = _
    rw [conj_schExpr V hfT x]
    simp only [schExpr]
    ring
  have hsplit : (∫ x, (-(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x
        * (g : ℝ → ℂ) x) + (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x))
      = (∫ x, -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x))
        + ∫ x, (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x :=
    integral_add ((integrable_mul_of_isTestFn hFT.deriv.deriv hgT).neg)
      (integrable_mul_of_isTestFn hFT hgT.deriv.deriv)
  have hneg : (∫ x, -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x))
      = -∫ x, deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x :=
    integral_neg _
  have hzero : (∫ x, (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x)
      - ∫ x, (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x = 0 := by
    rw [← integral_sub hA hB,
      integral_congr_ae (Filter.Eventually.of_forall hpoint), hsplit, hneg,
      integral_deriv_deriv_mul hFT hgT]
    ring
  linear_combination hzero

/-- An eigenvector of the adjoint of the minimal operator is a distributional solution of the
Schrödinger equation. -/
