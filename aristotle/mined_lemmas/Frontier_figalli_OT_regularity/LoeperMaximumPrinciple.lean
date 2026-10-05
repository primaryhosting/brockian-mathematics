/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-! ## The cost function and the Ma–Trudinger–Wang condition -/

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖² / 2` on a real inner product
space. -/

def LoeperMaximumPrinciple {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : E → E → ℝ) : Prop :=
  ∀ (x z y₀ y₁ : E), ∀ t ∈ Set.Icc (0 : ℝ) 1,
    c x ((1 - t) • y₀ + t • y₁) - c z ((1 - t) • y₀ + t • y₁) ≤
      max (c x y₀ - c z y₀) (c x y₁ - c z y₁)

/-- Base case of the MTW theory: the quadratic cost satisfies the (degenerate) MTW
condition (A3w), in Loeper's form.  Indeed `c x y - c z y` is an affine function of `y`. -/
