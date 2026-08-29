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


def LegendreConjecture : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < (n + 1) * (n + 1)

/-- A square-root prime-gap hypothesis: for `m ≥ 1000`, every interval `(m, m + k)` with
`k² ≤ m` (i.e. of length at least `√m`) contains a prime.  This is a standard, still open,
conjectural strengthening of known prime-gap bounds; the threshold `1000` excludes the small
counterexamples (such as `m = 24`, where the interval `(24, 28)` contains no prime). -/
