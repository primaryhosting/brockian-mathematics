import Mathlib

/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## Setting

We formalize the one-dimensional base case of the Ma–Trudinger–Wang / Figalli regularity
theory for optimal transport.

The transport cost is the quadratic cost `c x y = (x - y)^2 / 2`.  For this cost Brenier's

theorem quadraticCost_mixed_deriv (x y : ℝ) :
    deriv (fun x' : ℝ => deriv (fun y' : ℝ => quadraticCost x' y') y) x = -1 := by
  have h : ∀ x' : ℝ, deriv (fun y' : ℝ => quadraticCost x' y') y = -(x' - y) := by
    intro x'
    have : deriv (fun y' : ℝ => (x' - y') ^ 2 / 2) y = -(x' - y) := by
      have hd : HasDerivAt (fun y' : ℝ => (x' - y') ^ 2 / 2) (-(x' - y)) y := by
        have h1 : HasDerivAt (fun y' : ℝ => x' - y') (-1 : ℝ) y := by
          simpa using (hasDerivAt_id y).const_sub x'
        have h2 := (h1.pow 2).div_const 2
        convert h2 using 1
        ring
      exact hd.deriv
    simpa [quadraticCost] using this
  simp only [h]
  have hd : HasDerivAt (fun x' : ℝ => -(x' - y)) (-1 : ℝ) x :=
    ((hasDerivAt_id x).sub_const y).neg
  exact hd.deriv

/-!
## A monotone function with the intermediate value property is continuous
-/

/-- One-sided (right) estimate: a monotone function whose image on a closed interval around `a`
is order-connected can be squeezed just above `T a` immediately to the right of `a`. -/
