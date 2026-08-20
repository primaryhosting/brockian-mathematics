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

/-- A *Giuga number* is a composite natural number `n > 1` such that
`p ∣ n / p - 1` for every prime `p` dividing `n`. -/

theorem oddGiugaExists_iff :
    (∃ n : ℕ, Odd n ∧ IsGiuga n) ↔
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ (∀ p ∈ S, p ≠ 2) ∧ 2 ≤ S.card ∧
        ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1 := by
  constructor
  · rintro ⟨n, hodd, h⟩
    refine ⟨n.primeFactors, fun p hpm => Nat.prime_of_mem_primeFactors hpm, ?_,
      h.two_le_card, h.dvd_prod_erase⟩
    intro p hpm hp2
    subst hp2
    have hd : (2 : ℕ) ∣ n := Nat.dvd_of_mem_primeFactors hpm
    rw [Nat.odd_iff] at hodd
    omega
  · rintro ⟨S, hp, h2, hcard, hdvd⟩
    exact OddGiugaExists hp h2 hcard hdvd

end Brockian.GiugaNumbers

