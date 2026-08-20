/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

open Filter Topology

/-! ## The Sato–Tate measure -/

/-- The density of the Sato–Tate measure `(2/π) sin²θ dθ` on `[0, π]`. -/

def SatoTateEquidistributed (theta : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, Continuous f →
    Tendsto (fun N : ℕ => (∑ p ∈ primesBelow N, f (theta p)) / ((primesBelow N).card : ℝ))
      atTop (𝓝 (∫ x in (0:ℝ)..Real.pi, f x * satoTateDensity x))

/-- The Sato–Tate conjecture (a theorem of Clozel–Harris–Shepherd-Barron–Taylor for
non-CM elliptic curves over `ℚ`): the Frobenius angles of `W` are Sato–Tate
equidistributed. -/
