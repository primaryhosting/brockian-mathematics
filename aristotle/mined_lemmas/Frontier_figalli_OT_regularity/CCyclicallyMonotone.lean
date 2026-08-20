/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic (Brenier) transport cost `c(x,y) = ‖x - y‖²/2`. -/

def CCyclicallyMonotone (c : E → E → ℝ) (S : Set (E × E)) : Prop :=
  ∀ (n : ℕ) (p : Fin (n + 1) → E × E), (∀ i, p i ∈ S) →
    ∑ i, c (p i).1 (p i).2 ≤ ∑ i, c (p i).1 (p (i + 1)).2

/-- Flatness of the quadratic cost (the Ma–Trudinger–Wang tensor of `‖x-y‖²/2` vanishes
identically).  We record the elementary manifestation of this degeneracy which drives the
whole theory: for the quadratic cost, differences `x ↦ c(x,y) - c(x,y')` are affine
functions of `x`, so that `c`-convex functions are exactly convex functions. -/
omit [CompleteSpace E] in
