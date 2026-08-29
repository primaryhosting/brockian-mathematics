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

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: two positive integers, each of whose sum of
divisors equals their sum plus one. -/

lemma prod_ratio_le_list :
    ∀ (L : List ℕ), List.IsChain (fun a b => ∀ p : ℕ, p.Prime → a < p → b ≤ p) L →
      (∀ a ∈ L, 2 ≤ a) →
      ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
        (∀ a, L.head? = some a → ∀ p ∈ S, a ≤ p) → S.card ≤ L.length →
        ∏ p ∈ S, (p : ℚ) / (p - 1) ≤ (L.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
  intro L
  induction L with
  | nil =>
    intro _ _ S _ _ hcard
    simp only [List.length_nil, Nat.le_zero, Finset.card_eq_zero] at hcard
    simp [hcard]
  | cons a T ih =>
    intro hchain hge2 S hSp hSge hcard
    have ha2 : 2 ≤ a := hge2 a (by simp)
    have ha2' : (2 : ℚ) ≤ (a : ℚ) := by exact_mod_cast ha2
    have hTnonneg : (0 : ℚ) ≤ (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
      refine List.prod_nonneg ?_
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hge2 q (by simp [hq])
      exact le_of_lt (div_pos (by linarith) (by linarith))
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · simp only [Finset.prod_empty]
      refine List.one_le_prod ?_
      intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨q, hq, rfl⟩ := hb
      have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hge2 q hq
      rw [le_div_iff₀ (by linarith)]
      linarith
    · set m := S.min' hne with hm
      have hmS : m ∈ S := S.min'_mem hne
      have ham : a ≤ m := hSge a (by simp) m hmS
      have hm2 : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast le_trans ha2 ham
      have hprod : ∏ p ∈ S, (p : ℚ) / (p - 1)
          = ((m : ℚ) / (m - 1)) * ∏ p ∈ S.erase m, (p : ℚ) / (p - 1) :=
        (Finset.mul_prod_erase S _ hmS).symm
      have hIH : ∏ p ∈ S.erase m, (p : ℚ) / (p - 1)
          ≤ (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod := by
        refine ih (List.IsChain.tail hchain) (fun x hx => hge2 x (by simp [hx])) _
          (fun p hp => hSp p (Finset.mem_of_mem_erase hp)) ?_ ?_
        · intro b hb p hp
          have hpS : p ∈ S := Finset.mem_of_mem_erase hp
          have hpm : m < p :=
            lt_of_le_of_ne (S.min'_le p hpS) (Ne.symm (Finset.ne_of_mem_erase hp))
          exact (List.isChain_cons.mp hchain).1 b hb p (hSp p hpS) (lt_of_le_of_lt ham hpm)
        · have hcard' := Finset.card_erase_of_mem hmS
          have hc : S.card ≤ T.length + 1 := by simpa using hcard
          omega
      have hmono : (m : ℚ) / (m - 1) ≤ (a : ℚ) / (a - 1) := ratio_antitone ha2 ham
      have hmpos : (0 : ℚ) ≤ (m : ℚ) / (m - 1) := le_of_lt (div_pos (by linarith) (by linarith))
      simp only [List.map_cons, List.prod_cons]
      rw [hprod]
      calc ((m : ℚ) / (m - 1)) * ∏ p ∈ S.erase m, (p : ℚ) / (p - 1)
          ≤ ((m : ℚ) / (m - 1)) * (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod :=
            mul_le_mul_of_nonneg_left hIH hmpos
        _ ≤ ((a : ℚ) / (a - 1)) * (T.map (fun p : ℕ => (p : ℚ) / (p - 1))).prod :=
            mul_le_mul_of_nonneg_right hmono hTnonneg

/-- The first twenty odd primes. -/
