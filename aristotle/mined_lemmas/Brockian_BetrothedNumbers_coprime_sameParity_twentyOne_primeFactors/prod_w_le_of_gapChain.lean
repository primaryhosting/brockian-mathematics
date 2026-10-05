/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
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

namespace Brockian
namespace BetrothedNumbers

open Finset

/-! ## Basic definitions -/

/-- `sigmaOne n` is the sum-of-divisors function `σ₁(n) = ∑_{d ∣ n} d`. -/

lemma prod_w_le_of_gapChain :
    ∀ (L : List ℕ) (S : Finset ℕ),
      (∀ b ∈ L, 2 ≤ b) →
      L.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) →
      (∀ p ∈ S, p.Prime) →
      (∀ b ∈ L.head?, ∀ p ∈ S, b ≤ p) →
      S.card ≤ L.length →
      ∏ p ∈ S, w p ≤ (L.map w).prod := by
  intro L
  induction L with
  | nil =>
      intro S _ _ _ _ hcard
      simp only [List.length_nil, Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard]
  | cons b T ih =>
      intro S hb2 hchain hprime hhead hcard
      rcases Finset.eq_empty_or_nonempty S with rfl | hS
      · simpa using one_le_prod_map_w (b :: T) hb2
      · set m := S.min' hS with hm
        have hmS : m ∈ S := S.min'_mem hS
        have hbm : b ≤ m := hhead b (by simp) m hmS
        have hb2' : 2 ≤ b := hb2 b (by simp)
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchainT⟩ := hchain
        have hsplit : ∏ p ∈ S, w p = w m * ∏ p ∈ S.erase m, w p :=
          (Finset.mul_prod_erase S w hmS).symm
        have hIH : ∏ p ∈ S.erase m, w p ≤ (T.map w).prod := by
          refine ih (S.erase m) (fun x hx => hb2 x (by simp [hx])) hchainT
            (fun p hp => hprime p (Finset.mem_of_mem_erase hp)) ?_ ?_
          · intro b' hb' p hp
            have hpS : p ∈ S := Finset.mem_of_mem_erase hp
            have hne : p ≠ m := Finset.ne_of_mem_erase hp
            have hmp : m ≤ p := S.min'_le p hpS
            exact hrel b' hb' p (hprime p hpS) (by omega)
          · have hce := Finset.card_erase_of_mem hmS
            simp only [List.length_cons] at hcard
            omega
        have hwm : w m ≤ w b := w_anti hb2' hbm
        have hnn : 0 ≤ ∏ p ∈ S.erase m, w p :=
          Finset.prod_nonneg fun p hp =>
            w_nonneg (hprime p (Finset.mem_of_mem_erase hp)).two_le
        simp only [List.map_cons, List.prod_cons]
        rw [hsplit]
        exact mul_le_mul hwm hIH hnn (w_nonneg hb2')

