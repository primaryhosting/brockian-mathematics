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

def IsOddGiugaSystem (S : Finset ℕ) : Prop :=
  (∀ p ∈ S, p.Prime ∧ Odd p) ∧ 2 ≤ S.card ∧
    ∃ k : ℤ, (∑ p ∈ S, (p : ℚ)⁻¹) - (∏ p ∈ S, (p : ℚ)⁻¹) = (k : ℚ)

section Helpers

variable {S : Finset ℕ}

/-- In a product of nonzero naturals, dividing by one factor leaves the product of the others. -/
