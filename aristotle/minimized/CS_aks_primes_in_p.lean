/-
# Aks Primes In P
Category: Frontier Cs
Target: CS.aks_primes_in_p
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

open Polynomial

/-- If `p` is a prime dividing `n`, then `p` does not divide `(n-1).choose (p-1)`.
Indeed, by Lucas' theorem this binomial coefficient is `≡ 1 [MOD p]`. -/

theorem not_dvd_choose_pred (p n : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 1 ≤ n) :
    ¬ p ∣ (n - 1).choose (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 2 ≤ p := hp.two_le
  have hmod : (n - 1) % p = p - 1 := by
    obtain ⟨t, rfl⟩ := hpn
    have ht : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · simp [h] at hn
      · exact h
    obtain ⟨s, rfl⟩ : ∃ s : ℕ, t = s + 1 := ⟨t - 1, by omega⟩
    have hexp : p * (s + 1) = p * s + p := by ring
    have hrw : p * (s + 1) - 1 = p * s + (p - 1) := by omega
    rw [hrw, Nat.mul_add_mod, Nat.mod_eq_of_lt (show p - 1 < p by omega)]
  have key := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n - 1) (k := p - 1) (p := p)
  rw [hmod, Nat.mod_eq_of_lt (show p - 1 < p by omega),
    Nat.div_eq_of_lt (show p - 1 < p by omega), Nat.choose_self, Nat.choose_zero_right,
    Nat.mul_one] at key
  intro hdvd
  have hkey : (n - 1).choose (p - 1) % p = 1 % p := key
  rw [Nat.dvd_iff_mod_eq_zero.mp hdvd, Nat.mod_eq_of_lt hp.one_lt] at hkey
  exact absurd hkey (by omega)

/-- If `p` is a prime dividing `n` and `2 ≤ n`, then `n` does not divide `n.choose p`. -/
