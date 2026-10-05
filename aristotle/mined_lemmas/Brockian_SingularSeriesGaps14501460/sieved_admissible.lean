/-
# Singular Series Gaps 14501460
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps14501460
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian

/-- A finite set of nonnegative integers is *admissible* (in the Hardy–Littlewood /
Hensley–Richards sense) if for every prime `p` it fails to cover all residue classes
modulo `p`.  Equivalently, the singular series attached to the tuple is nonzero. -/

theorem sieved_admissible (q0 d : ℕ) (hc : (sieved q0 d).card ≤ 140) :
    Admissible (sieved q0 d) := by
  intro p hp
  by_cases hple : p ≤ 140
  · have hppos : 0 < p := hp.pos
    refine ⟨(p - q0 % p) % p, Nat.mod_lt _ hppos, ?_⟩
    intro h hh hcon
    have hmem : p ∈ smallPrimes := mem_smallPrimes hp hple
    have hne : (q0 + h) % p ≠ 0 := (Finset.mem_filter.mp hh).2 p hmem
    apply hne
    have ha : q0 % p < p := Nat.mod_lt _ hppos
    rcases Nat.eq_zero_or_pos (q0 % p) with h0 | h0
    · have hz : (p - q0 % p) % p = 0 := by rw [h0, Nat.sub_zero, Nat.mod_self]
      rw [Nat.add_mod, h0, hcon, hz]
      simp
    · have hlt : p - q0 % p < p := by omega
      have hz : (p - q0 % p) % p = p - q0 % p := Nat.mod_eq_of_lt hlt
      rw [Nat.add_mod, hcon, hz]
      have hsum : q0 % p + (p - q0 % p) = p := by omega
      rw [hsum, Nat.mod_self]
  · exact exists_uncovered_residue _ _ (by omega)

/-- Packaging: from a computation of the cardinality of a sieved window and the fact
that both endpoints survive the sieve, we get an admissible tuple of diameter exactly
`d` and size at least `100`. -/
