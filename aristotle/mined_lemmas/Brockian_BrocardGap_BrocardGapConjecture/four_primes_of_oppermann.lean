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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

/-- The number of primes strictly between `a` and `b`. -/

theorem four_primes_of_oppermann (hO : Oppermann) (P q : ℕ) (hP : 3 ≤ P) (hq : P + 2 ≤ q) :
    4 ≤ primeCountIn (P ^ 2) (q ^ 2) := by
  obtain ⟨-, a, ha, ha1, ha2⟩ := hO P (by omega)
  obtain ⟨⟨b, hb, hb1, hb2⟩, c, hc, hc1, hc2⟩ := hO (P + 1) (by omega)
  obtain ⟨⟨d, hd, hd1, hd2⟩, -⟩ := hO (P + 2) (by omega)
  have e1 : (P + 1) * (P + 1) = P * P + 2 * P + 1 := by ring
  have e2 : (P + 2) * (P + 2) = P * P + 4 * P + 4 := by ring
  rw [e1] at hb1 hb2 hc1 hc2
  rw [e2] at hd1 hd2
  have hqq : P * P + 4 * P + 4 ≤ q * q := by
    rw [← e2]; exact Nat.mul_le_mul hq hq
  have hp2 : P ^ 2 = P * P := sq P
  have hq2 : q ^ 2 = q * q := sq q
  set S := P * P with hS
  set T := q * q with hT
  clear_value S T
  have hsub : ({a, b, c, d} : Finset ℕ) ⊆ (Finset.Ioo (P ^ 2) (q ^ 2)).filter Nat.Prime := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_Ioo]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨⟨by omega, by omega⟩, ha⟩
    · exact ⟨⟨by omega, by omega⟩, hb⟩
    · exact ⟨⟨by omega, by omega⟩, hc⟩
    · exact ⟨⟨by omega, by omega⟩, hd⟩
  have hcard : ({a, b, c, d} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega),
      Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  calc (4 : ℕ) = ({a, b, c, d} : Finset ℕ).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- The second prime is `3`. -/
