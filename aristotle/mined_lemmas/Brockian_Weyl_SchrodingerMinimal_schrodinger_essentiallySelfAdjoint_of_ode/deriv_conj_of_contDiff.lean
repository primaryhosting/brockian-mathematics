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

theorem deriv_conj_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    deriv (fun x => (starRingEnd ℂ) (f x)) = fun x => (starRingEnd ℂ) (deriv f x) := by
  funext x
  have h1 : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
  exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x h1).deriv

/-- Integration by parts, twice, for test functions. -/
