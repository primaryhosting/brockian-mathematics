import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
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

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem coord1_convex {S : Set (Fin 1 → ℝ)} (hS : SymmetricConvex S) : Convex ℝ (coord1 S) := by
  intro x hx y hy a b ha hb hab
  have hxS : (fun _ : Fin 1 => x) ∈ S := hx
  have hyS : (fun _ : Fin 1 => y) ∈ S := hy
  have := hS.1 hxS hyS ha hb hab
  have heq : a • (fun _ : Fin 1 => x) + b • (fun _ : Fin 1 => y) = (fun _ : Fin 1 => a • x + b • y) := by
    funext i
    simp
  rwa [heq] at this

