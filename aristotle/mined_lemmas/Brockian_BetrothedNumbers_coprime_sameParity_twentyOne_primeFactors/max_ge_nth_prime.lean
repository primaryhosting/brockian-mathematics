import Mathlib
/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.BetrothedNumbers

open ArithmeticFunction

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose
divisor sums equals the sum of the pair plus one. -/

lemma max_ge_nth_prime {S : Finset ℕ} (hp : ∀ p ∈ S, p.Prime) (h3 : ∀ p ∈ S, 3 ≤ p)
    {m : ℕ} (hm : ∀ p ∈ S, p ≤ m) (hne : S.Nonempty) : Nat.nth Nat.Prime S.card ≤ m := by
  obtain ⟨x, hx⟩ := hne
  have hm2 : 2 ≤ m := le_trans (h3 x hx) (hm x hx) |>.trans' (by omega)
  by_contra hcon
  push_neg at hcon
  have h2S : (2:ℕ) ∉ S := fun h => by have := h3 2 h; omega
  have hsub : insert 2 S ⊆ (Finset.range (m + 1)).filter Nat.Prime := by
    intro y hy
    simp only [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by have := hm y hy; omega, hp y hy⟩
  have hcard : S.card + 1 ≤ Nat.count Nat.Prime (m + 1) := by
    rw [Nat.count_eq_card_filter_range]
    have := Finset.card_le_card hsub
    rwa [Finset.card_insert_of_notMem h2S] at this
  have hmono : Nat.count Nat.Prime (m + 1) ≤ Nat.count Nat.Prime (Nat.nth Nat.Prime S.card) :=
    Nat.count_monotone _ (by omega)
  rw [Nat.count_nth_of_infinite Nat.infinite_setOf_prime] at hmono
  omega

