import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
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

namespace Math2

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

/-- The Dedekind zeta function of a number field `K`, written explicitly as the `L`-series
whose `n`-th coefficient is the number of integral ideals of `𝓞 K` of absolute norm `n`. -/

noncomputable def zeta (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  LSeries (fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) s

