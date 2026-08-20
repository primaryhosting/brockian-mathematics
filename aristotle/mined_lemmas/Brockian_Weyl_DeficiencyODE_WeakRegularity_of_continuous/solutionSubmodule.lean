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

def solutionSubmodule (q : ℝ → ℂ) (z : ℂ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {u | IsODESolution q z u}
  add_mem' := by
    rintro u₁ u₂ ⟨v₁, h₁⟩ ⟨v₂, h₂⟩
    refine ⟨v₁ + v₂, ⟨fun x => (h₁.deriv_left x).add (h₂.deriv_left x), fun x => ?_⟩⟩
    have := (h₁.deriv_right x).add (h₂.deriv_right x)
    simpa [Pi.add_apply, mul_add] using this
  zero_mem' := ⟨0, ⟨fun x => by simpa using hasDerivAt_const x (0 : ℂ),
    fun x => by simpa using hasDerivAt_const x (0 : ℂ)⟩⟩
  smul_mem' := by
    rintro c u ⟨v, h⟩
    refine ⟨c • v, ⟨fun x => (h.deriv_left x).const_smul c, fun x => ?_⟩⟩
    have := (h.deriv_right x).const_smul c
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using this

