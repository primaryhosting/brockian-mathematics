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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- `IsCombLine N k L` says that `L : Fin k → (Fin N → Fin k)` is a *combinatorial line* in the
hypercube `Fin N → Fin k`: there is a word `f : Fin N → Option (Fin k)` such that in coordinate
`i` the point `L x` is the constant `a` when `f i = some a`, and is the "moving" letter `x` when
`f i = none`, and at least one coordinate is moving. -/

def IsCombLine (N k : ℕ) (L : Fin k → Fin N → Fin k) : Prop :=
  ∃ f : Fin N → Option (Fin k), (∃ i : Fin N, f i = none) ∧ ∀ (x : Fin k) (i : Fin N),
    L x i = (f i).getD x

/-- **The Hales–Jewett theorem.** For any number of colours `r` and any alphabet size `k` there is
a dimension `N` such that every `r`-colouring of the hypercube `Fin N → Fin k` admits a
monochromatic combinatorial line.

The proof is by transport from Mathlib's `Combinatorics.Line.exists_mono_in_high_dimension`. -/
