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

theorem conjL2_eq_zero_iff (u : L2) : conjL2 u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : (fun x => (starRingEnd ℂ) ((u : ℝ → ℂ) x)) =ᵐ[volume] (0 : ℝ → ℂ) := by
      refine (conjL2_coeFn u).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero ℂ 2 volume
    refine Lp.ext_iff.mpr ?_
    filter_upwards [h0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0
    have : (starRingEnd ℂ) ((u : ℝ → ℂ) x) = 0 := hx
    rw [hx0]
    simpa using congrArg (starRingEnd ℂ) this
  · intro h
    refine Lp.ext_iff.mpr ?_
    filter_upwards [conjL2_coeFn u, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0
    rw [hx, hx0, h]
    simp

/-- **Essential self-adjointness of the minimal Schrödinger operator.**

If the differential equation `-u'' + V u = z u` (understood in the distributional sense) has no
nonzero solution `u ∈ L²(ℝ)` for `z = i` and for `z = -i`, then the minimal Schrödinger operator
`-d²/dx² + V`, defined on the smooth compactly supported functions, is essentially self-adjoint:
its closure is a self-adjoint operator. -/
