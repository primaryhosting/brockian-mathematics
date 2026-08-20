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

theorem deficiencySpace_eq (q : ℝ → ℂ) (z : ℂ) :
    deficiencySpace q z = {u | MemLp u 2 volume ∧ IsODESolution q z u} := by
  ext u
  simp only [deficiencySpace, maximalDomain, mem_setOf_eq]
  constructor
  · rintro ⟨⟨hL2, hd1, hd2, -⟩, heq⟩
    refine ⟨hL2, deriv u, ⟨fun x => (hd1 x).hasDerivAt, fun x => ?_⟩⟩
    have h1 : -deriv (deriv u) x + q x * u x = z * u x := congrFun heq x
    have h2 : deriv (deriv u) x = (q x - z) * u x := by linear_combination -h1
    exact h2 ▸ (hd2 x).hasDerivAt
  · rintro ⟨hL2, hsol⟩
    obtain ⟨v, h⟩ := hsol
    have hdu : deriv u = v := h.deriv_eq
    have hd1 : Differentiable ℝ u := fun x => (h.deriv_left x).differentiableAt
    have hd2 : Differentiable ℝ (deriv u) := by
      rw [hdu]; exact fun x => (h.deriv_right x).differentiableAt
    have htau : tau q u = fun x => z * u x := by
      funext x
      have := IsODESolution.deriv_deriv ⟨v, h⟩ x
      simp only [tau, this]
      ring
    exact ⟨⟨hL2, hd1, hd2, htau ▸ hL2.const_mul z⟩, htau⟩

/-- Uniqueness for the initial value problem: a solution vanishing to first order at a point
vanishes identically.  This is where weak regularity of the potential is used. -/
