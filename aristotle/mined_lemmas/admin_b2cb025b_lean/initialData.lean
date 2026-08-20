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
# Weyl theory: the deficiency space of a Schrödinger operator is represented by ODE solutions

For a real (or complex) potential `q : ℝ → ℂ` the formal differential expression
`τ u = -u'' + q u` gives rise to a maximal operator on `L²(ℝ)`.  For `z : ℂ` the
*deficiency space* at `z` is the kernel of `τ - z` inside the maximal domain.

This file proves the two basic facts of Weyl's theory in this setting:

* the deficiency space is exactly the set of square integrable solutions of the
  ordinary differential equation `u'' = (q - z) u`;
* the space of *all* solutions of that ODE has dimension at most `2`, hence the
  deficiency index of the operator is at most `2`.

The second statement requires a regularity assumption on `q`; the (weak) form used here is
that `q` is bounded on every compact interval (`WeakRegularity`).  Continuous potentials
satisfy it (`WeakRegularity.of_continuous`).
-/

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory Set

/-- **Weak regularity** of a potential: `q` is bounded on each compact interval.
This is weaker than continuity, and it is all that the uniqueness theory for the
associated ODE requires. -/

noncomputable def initialData (q : ℝ → ℂ) (z : ℂ) : solutionSubmodule q z →ₗ[ℂ] ℂ × ℂ where
  toFun u := ((u : ℝ → ℂ) 0, deriv (u : ℝ → ℂ) 0)
  map_add' := by
    rintro ⟨u₁, h₁⟩ ⟨u₂, h₂⟩
    have hd₁ : Differentiable ℝ u₁ := IsODESolution.differentiable h₁
    have hd₂ : Differentiable ℝ u₂ := IsODESolution.differentiable h₂
    have : deriv (u₁ + u₂) 0 = deriv u₁ 0 + deriv u₂ 0 := deriv_add (hd₁ 0) (hd₂ 0)
    simp [this]
  map_smul' := by
    rintro c ⟨u, hu⟩
    have hd : Differentiable ℝ u := IsODESolution.differentiable hu
    have : deriv (c • u) 0 = c • deriv u 0 := deriv_const_smul c (hd 0)
    simp [this]

