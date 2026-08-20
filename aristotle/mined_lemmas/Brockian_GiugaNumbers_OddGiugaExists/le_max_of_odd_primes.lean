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

/-
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GiugaNumbers

open Finset

/-- A *Giuga number* is a composite natural number `n > 1` such that every prime `p`
dividing `n` satisfies `p ∣ n / p - 1`. -/

theorem le_max_of_odd_primes :
    ∀ (k : ℕ), k ≤ 7 → ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime ∧ p ≠ 2) → S.card = k + 1 →
      ∃ hS : S.Nonempty, q k ≤ S.max' hS := by
  intro k
  induction k with
  | zero =>
    intro _ S hS hc
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨hne, ?_⟩
    obtain ⟨hp, hp2⟩ := hS _ (S.max'_mem hne)
    have h3 := three_le_of_prime_ne_two hp hp2
    simpa [q] using h3
  | succ k ih =>
    intro hk S hS hc
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    refine ⟨hne, ?_⟩
    have hmS : S.max' hne ∈ S := S.max'_mem hne
    have hcard' : (S.erase (S.max' hne)).card = k + 1 := by
      rw [Finset.card_erase_of_mem hmS, hc]
      omega
    obtain ⟨hne', hle⟩ :=
      ih (by omega) (S.erase (S.max' hne)) (fun p hp => hS p (Finset.mem_of_mem_erase hp)) hcard'
    have hmem := Finset.max'_mem _ hne'
    have hlt : (S.erase (S.max' hne)).max' hne' < S.max' hne :=
      lt_of_le_of_ne (Finset.le_max' S _ (Finset.mem_of_mem_erase hmem))
        (Finset.ne_of_mem_erase hmem)
    exact q_step (by omega) (hS _ hmS).1 (lt_of_le_of_lt hle hlt)

