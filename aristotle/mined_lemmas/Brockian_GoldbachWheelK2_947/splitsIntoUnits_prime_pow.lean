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

/-- The `K2` Goldbach wheel property at modulus `m`:

every residue class `r` modulo `m` is represented as `p + q` with `p`, `q` prime, where moreover
the two primes may be taken arbitrarily large (larger than any prescribed bound `N`).

This is the "wheel" (residue-class) shadow of the binary Goldbach problem: it says that, modulo
`m`, no congruence obstruction can rule out a representation as a sum of two primes, uniformly in
the size of the primes used. -/

theorem splitsIntoUnits_prime_pow {p n : ℕ} (hp : Nat.Prime p) (hodd : Odd p) (hn : 0 < n) :
    SplitsIntoUnits (p ^ n) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro r
  have hp2 : p ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hodd
  have h2 : (2 : ZMod p) ≠ 0 := by
    have hnd : ¬ (p ∣ 2) := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hnd
    simpa using h
  have hne : (1 : ZMod p) ≠ 2 := by
    intro h
    apply h2
    have hs : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h.symm
    have h1 : (1 : ZMod p) = 0 := by linear_combination hs
    linear_combination (2 : ZMod p) * h1
  have hu2 : IsUnit (2 : ZMod (p ^ n)) := by
    rw [isUnit_zmod_prime_pow_iff hp hn, map_ofNat]
    exact h2
  by_cases hc : (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) (r - 1) = 0
  · refine ⟨2, r - 2, hu2, ?_, by ring⟩
    rw [isUnit_zmod_prime_pow_iff hp hn]
    intro h0
    apply hne
    rw [map_sub, map_one, sub_eq_zero] at hc
    rw [map_sub, map_ofNat, sub_eq_zero] at h0
    rw [← hc, h0]
  · exact ⟨1, r - 1, isUnit_one, by rw [isUnit_zmod_prime_pow_iff hp hn]; exact hc, by ring⟩

/-- The wheel splitting property is multiplicative along coprime factorisations, by the Chinese
remainder theorem. -/
