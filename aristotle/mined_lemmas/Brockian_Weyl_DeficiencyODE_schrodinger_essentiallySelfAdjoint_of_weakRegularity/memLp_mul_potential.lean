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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with unbounded operators on a complex inner product space `H`, presented as linear maps
`T : D →ₗ[ℂ] H` out of a submodule `D` (the operator domain).

For a densely defined symmetric operator `T`, essential self-adjointness is equivalent to the
symmetry of the adjoint `T†` (equivalently: `T† = T††`, i.e. the closure `T̄ = T††` is
self-adjoint).  Since the adjoint of an unbounded operator is only defined on the set of vectors
`y` for which a representing vector `z` exists, we encode `z = T† y` through the relation
`IsAdjointPair T y z`, and encode symmetry of `T†` as `AdjointIsSymmetric T`.  This avoids any
use of choice and is exactly the classical criterion.

The main result is the (bounded) Kato–Rellich theorem in the concrete Schrödinger setting: on
`L²(ℝ)`, if the kinetic part `T` (e.g. `-d²/dx²` on a core such as `Cc^∞` or the Schwartz space)
is essentially self-adjoint, then adding a potential `V` of *weak regularity* — merely a.e. measurable
and essentially bounded, with no continuity or differentiability assumed — preserves essential
self-adjointness. In particular the deficiency spaces of the Schrödinger operator `-Δ + V` are
trivial, i.e. its deficiency indices vanish (Weyl's deficiency-index criterion).
-/

open MeasureTheory

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `IsAdjointPair T y z` says that `z` represents the adjoint `T† y`, i.e.
`⟪T x, y⟫ = ⟪x, z⟫` for all `x` in the domain of `T`. -/

theorem memLp_mul_potential (f : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (fun x => (V x : ℂ) * (f : ℝ → ℂ) x) 2 volume := by
  refine MemLp.of_le ((Lp.memLp f).const_mul (C : ℂ)) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hV).mul
      (Lp.aestronglyMeasurable f)
  · filter_upwards [hVb] with x hx
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (norm_nonneg _)

/-- The potential term of a Schrödinger operator: multiplication by a bounded measurable
real-valued function `V`, as an everywhere-defined operator on `L²(ℝ)`. -/
