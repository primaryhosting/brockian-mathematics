import Mathlib

/-!
# Hales Jewett
Category: Frontier Math
Target: Math2.hales_jewett
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

set_option grind.warning false

namespace Math2

/-- The point of the combinatorial line described by the template `τ : Fin N → Option (Fin k)`
at the parameter value `a : Fin k`.  A coordinate `i` with `τ i = none` is a *moving* coordinate
(its value is `a`), while a coordinate with `τ i = some b` is *frozen* at the value `b`. -/

def linePoint {N k : ℕ} (τ : Fin N → Option (Fin k)) (a : Fin k) : Fin N → Fin k :=
  fun i => (τ i).getD a

/-- **The Hales–Jewett theorem.**  For every alphabet size `k` and every number of colours `r`
there is a dimension `N` such that every `r`-colouring of the combinatorial cube
`Fin N → Fin k` admits a monochromatic combinatorial line: a template
`τ : Fin N → Option (Fin k)` with at least one moving coordinate, all of whose `k` points
receive the same colour. -/
