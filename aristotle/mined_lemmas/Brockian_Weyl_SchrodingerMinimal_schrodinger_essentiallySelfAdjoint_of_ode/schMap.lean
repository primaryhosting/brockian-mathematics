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

noncomputable def schMap (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) : testFunctions →ₗ[ℂ] testFunctions where
  toFun g := ⟨schExpr V (g : ℝ → ℂ), isTestFn_schExpr hV (isTestFn_of_mem g.2)⟩
  map_add' f g := by
    have hf := isTestFn_of_mem f.2
    have hg := isTestFn_of_mem g.2
    apply Subtype.ext
    have hd2 : deriv (deriv ((f : ℝ → ℂ) + (g : ℝ → ℂ)))
        = deriv (deriv (f : ℝ → ℂ)) + deriv (deriv (g : ℝ → ℂ)) := by
      rw [deriv_add_contDiff hf.1 hg.1,
        deriv_add_contDiff (contDiff_deriv hf.1) (contDiff_deriv hg.1)]
    show schExpr V ((f : ℝ → ℂ) + (g : ℝ → ℂ)) = schExpr V (f : ℝ → ℂ) + schExpr V (g : ℝ → ℂ)
    funext x
    simp only [schExpr, hd2, Pi.add_apply]
    ring
  map_smul' c f := by
    have hf := isTestFn_of_mem f.2
    apply Subtype.ext
    have hd2 : deriv (deriv (c • (f : ℝ → ℂ))) = c • deriv (deriv (f : ℝ → ℂ)) := by
      rw [deriv_smul_contDiff c hf.1, deriv_smul_contDiff c (contDiff_deriv hf.1)]
    show schExpr V (c • (f : ℝ → ℂ)) = c • schExpr V (f : ℝ → ℂ)
    funext x
    simp only [schExpr, hd2, Pi.smul_apply, smul_eq_mul]
    ring

/-- The minimal Schrödinger operator: `-d²/dx² + V` with domain the smooth compactly supported
functions inside `L²(ℝ)`. -/
