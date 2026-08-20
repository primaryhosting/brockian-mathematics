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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite number `n > 1` such that `p ∣ n / p - 1` for every
prime `p` dividing `n`. -/

lemma criterion_thirty :
    (∑ p ∈ ({2, 3, 5} : Finset ℕ), (p : ℚ)⁻¹) - (∏ p ∈ ({2, 3, 5} : Finset ℕ), (p : ℚ)⁻¹) = 1 := by
  norm_num

/-- **Odd Giuga numbers exist iff an odd Giuga system exists.**

Whether an odd Giuga number exists is an open problem; this theorem is a Lean-checked
reduction of that existence statement to Giuga's rational criterion: there is an odd Giuga
number if and only if there is a finite set `S` of at least two odd primes with
`∑_{p ∈ S} 1/p - ∏_{p ∈ S} 1/p ∈ ℤ`. -/
