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

lemma prod_abFactor_le_bound : ∀ (n : ℕ) (S : Finset ℕ), S.card = n → (∀ p ∈ S, p.Prime) →
    (∀ p ∈ S, 3 ≤ p) → ∏ p ∈ S, abFactor p ≤ oddPrimeBound n := by
  intro n
  induction n with
  | zero =>
      intro S hS _ _
      rw [Finset.card_eq_zero] at hS
      subst hS
      simp [oddPrimeBound]
  | succ n ih =>
      intro S hS hp h3
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set m := S.max' hne with hmdef
      have hmS : m ∈ S := S.max'_mem hne
      have hle : ∀ p ∈ S, p ≤ m := fun p hp' => S.le_max' p hp'
      have hnth : Nat.nth Nat.Prime (n + 1) ≤ m := by
        have := max_ge_nth_prime hp h3 hle hne
        rwa [hS] at this
      have hprod : ∏ p ∈ S, abFactor p = abFactor m * ∏ p ∈ S.erase m, abFactor p :=
        (Finset.mul_prod_erase _ _ hmS).symm
      have hcarderase : (S.erase m).card = n := by
        rw [Finset.card_erase_of_mem hmS, hS]
        omega
      have hih := ih (S.erase m) hcarderase (fun p hp' => hp p (Finset.mem_of_mem_erase hp'))
        (fun p hp' => h3 p (Finset.mem_of_mem_erase hp'))
      have h1 : abFactor m ≤ abFactor (Nat.nth Nat.Prime (n + 1)) :=
        abFactor_antitone (Nat.prime_nth_prime _).two_le hnth
      have h2 : (0:ℚ) ≤ abFactor m := abFactor_nonneg (by have := h3 m hmS; omega)
      have h4 : (0:ℚ) ≤ ∏ p ∈ S.erase m, abFactor p :=
        Finset.prod_nonneg (fun p hp' =>
          abFactor_nonneg (by have := h3 p (Finset.mem_of_mem_erase hp'); omega))
      rw [hprod, oddPrimeBound_succ]
      calc abFactor m * ∏ p ∈ S.erase m, abFactor p
          ≤ abFactor (Nat.nth Nat.Prime (n + 1)) * oddPrimeBound n :=
            mul_le_mul h1 hih h4 (le_trans h2 h1)
        _ = oddPrimeBound n * abFactor (Nat.nth Nat.Prime (n + 1)) := mul_comm _ _

