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

import RequestProject.AKS.Algorithm

/-!
# Correctness of the AKS primality test

The main result of this file is `AKS.aksTest_iff_prime`:
the decision procedure `AKS.aksTest` returns `true` exactly on the primes.
-/

namespace AKS

open Polynomial Finset


theorem nat_pow_mul_pow_injective {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (hnk : ∀ k, n ≠ p ^ k) {i₁ j₁ i₂ j₂ : ℕ} (h : n ^ i₁ * p ^ j₁ = n ^ i₂ * p ^ j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hp2 : 2 ≤ p := hp.two_le
  have hn0 : 0 < n := by omega
  have hp0 : 0 < p := by omega
  have key : ∀ a b c e : ℕ, a < b → n ^ a * p ^ c = n ^ b * p ^ e → False := by
    intro a b c e hab heq
    have hdvd : n ∣ p ^ c := by
      have h1 : n ^ a * p ^ c = n ^ a * (n ^ (b - a) * p ^ e) := by
        rw [heq, ← mul_assoc, ← pow_add]
        congr 2
        omega
      have h2 : p ^ c = n ^ (b - a) * p ^ e := by
        exact Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hn0) h1
      refine ⟨n ^ (b - a - 1) * p ^ e, ?_⟩
      rw [h2, ← mul_assoc, ← pow_succ']
      congr 2
      omega
    obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    exact hnk k hk
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exact absurd h (fun hh => key i₁ i₂ j₁ j₂ hlt hh)
  · subst heq
    refine ⟨rfl, ?_⟩
    have := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hn0 (n := i₁)) h
    exact Nat.pow_right_injective hp2 this
  · exact absurd h.symm (fun hh => key i₂ i₁ j₂ j₁ hgt hh)

/-! ## Introspection at a root of unity -/

