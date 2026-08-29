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


theorem small : (List.range 101).all
    (fun n => decide (n < 2) || (hasPrimeIn (n*(n-1)) (n*n) && hasPrimeIn (n*n) (n*(n+1)))) = true := by
  decide

/-!
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.OppermannConjecture

/-! ## Primality

This file is deliberately import-free: the required header comment must be the very first
thing in the file, and Lean only accepts `import` lines before any other command.  We
therefore set up from scratch the small amount of primality theory that is needed.  The
companion file `Brockian/OppermannConjectureMathlib.lean` imports Mathlib and proves that
`IsPrimeNat` below agrees with `Nat.Prime`, and hence that `OppermannConjecture` is
equivalent to the statement of Oppermann's conjecture phrased with `Nat.Prime`. -/

/-- `p` is prime: `p ≥ 2` and its only divisors are `1` and `p`. -/
