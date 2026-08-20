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

theorem not_dvd_choose (p n : ℕ) (hp : p.Prime) (hpn : p ∣ n) (hn : 2 ≤ n) :
    ¬ n ∣ n.choose p := by
  intro ⟨m, hm⟩
  have hkey : n * ((n - 1).choose (p - 1)) = n.choose p * p := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (p - 1)
    have h1 : n - 1 + 1 = n := by omega
    have h2 : p - 1 + 1 = p := by omega
    rw [h1, h2] at h
    exact h
  rw [hm] at hkey
  have hn0 : 0 < n := by omega
  have : (n - 1).choose (p - 1) = m * p := by
    have : n * ((n - 1).choose (p - 1)) = n * (m * p) := by rw [hkey]; ring
    exact Nat.eq_of_mul_eq_mul_left hn0 this
  exact not_dvd_choose_pred p n hp hpn (by omega) ⟨m, by rw [this]; ring⟩

/--
**AKS criterion (Agrawal–Kayal–Saxena, Lemma 2.1)**, the number-theoretic heart of the
"PRIMES is in P" theorem.

For `n ≥ 2` and `a` coprime to `n`, the number `n` is prime if and only if the polynomial
identity `(X + a) ^ n = X ^ n + a` holds in `(ZMod n)[X]`.
-/
