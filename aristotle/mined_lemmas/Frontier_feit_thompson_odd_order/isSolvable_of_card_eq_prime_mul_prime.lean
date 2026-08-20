/-
# Feit Thompson Odd Order
Category: Frontier Abel
Target: Frontier.feit_thompson_odd_order
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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

universe u

/-- The full Feit–Thompson theorem, as a proposition about a universe of types:
every finite group of odd order is solvable. -/

theorem isSolvable_of_card_eq_prime_mul_prime {G : Type u} [Group G] [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hcard : Nat.card G = p * q) : IsSolvable G := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain Q : Sylow q G := default
  have hne : p ≠ q := hpq.ne
  have hQcard : Nat.card (Q : Subgroup G) = q := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_mul hp.ne_zero hq.ne_zero]
    simp [hp.factorization, hq.factorization, hne]
  have hindex : (Q : Subgroup G).index = p := by
    have hmul := Subgroup.card_mul_index (Q : Subgroup G)
    rw [hQcard, hcard] at hmul
    have hq0 : 0 < q := hq.pos
    nlinarith [hmul]
  have hn : Nat.card (Sylow q G) = 1 := by
    have hdvd : Nat.card (Sylow q G) ∣ p := hindex ▸ Sylow.card_dvd_index Q
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h1 | h1
    · exact h1
    · exfalso
      have hmod := card_sylow_modEq_one q G
      rw [h1] at hmod
      have h2 : p % q = p := Nat.mod_eq_of_lt hpq
      have h3 : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
      have h4 : p % q = 1 % q := hmod
      have h5 := hp.one_lt
      omega
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hn).1
  haveI : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  haveI : IsCyclic (Q : Subgroup G) := isCyclic_of_prime_card hQcard
  haveI : IsSolvable (Q : Subgroup G) := isSolvable_of_isCyclic
  haveI : IsCyclic (G ⧸ (Q : Subgroup G)) := isCyclic_of_prime_card (p := p) hindex
  haveI : IsSolvable (G ⧸ (Q : Subgroup G)) := isSolvable_of_isCyclic
  exact solvable_of_ker_le_range (Q : Subgroup G).subtype (QuotientGroup.mk' (Q : Subgroup G))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

/-- Every odd number below `45` is either a prime power or a product of two distinct primes. -/
