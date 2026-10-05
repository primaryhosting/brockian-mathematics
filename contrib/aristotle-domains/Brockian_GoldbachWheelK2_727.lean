/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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

namespace Brockian

/-- The two-prime ("K2") Goldbach wheel condition at modulus `m`.

Thinking of the residues mod `m` as a wheel, this says that the wheel is *fully covered*
by sums of two prime spokes: every residue class `n` mod `m` can be hit by a sum `p + q`
of two primes, both coprime to `m` (i.e. both lying on the wheel), and with the two primes
taken arbitrarily large.  This is the exact local-at-`m` statement underlying a Goldbach-type
two-prime representation: no residue class mod `m` is obstructed. -/
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ n N : ℕ, ∃ p q : ℕ, N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧
    Nat.Coprime p m ∧ Nat.Coprime q m ∧ (p + q) ≡ n [MOD m]

/-- On a wheel of prime modulus `P ≥ 3`, every residue class is the sum of two nonzero
residue classes.  This is the combinatorial heart of the wheel condition. -/
theorem exists_add_mod_eq_of_three_le {P : ℕ} (hP : 3 ≤ P) (n : ℕ) :
    ∃ a b : ℕ, 0 < a ∧ a < P ∧ 0 < b ∧ b < P ∧ (a + b) % P = n % P := by
  have hPpos : 0 < P := by omega
  have hr : n % P < P := Nat.mod_lt _ hPpos
  rcases eq_or_ne (n % P) 0 with h0 | h0
  · refine ⟨1, P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h1 : 1 + (P - 1) = P := by omega
    rw [h1, Nat.mod_self, h0]
  rcases eq_or_ne (n % P) 1 with h1 | h1
  · refine ⟨2, P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h2 : 2 + (P - 1) = P + 1 := by omega
    rw [h2, h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  · refine ⟨1, n % P - 1, by omega, by omega, by omega, by omega, ?_⟩
    have h3 : 1 + (n % P - 1) = n % P := by omega
    rw [h3]
    exact Nat.mod_eq_of_lt hr

/-- A residue strictly between `0` and a prime `P` is coprime to `P`. -/
theorem coprime_of_pos_lt_prime {P a : ℕ} (hP : Nat.Prime P) (h0 : 0 < a) (h : a < P) :
    Nat.Coprime a P := by
  rw [Nat.coprime_comm]
  rw [Nat.Prime.coprime_iff_not_dvd hP]
  intro hdvd
  have := Nat.le_of_dvd h0 hdvd
  omega

/-- **The Goldbach wheel is fully covered at every odd prime modulus.**
For a prime `P > 2`, every residue class mod `P` is the sum of two arbitrarily large primes,
both coprime to `P`. -/
theorem goldbachWheelK2_of_prime_of_two_lt {P : ℕ} (hP : Nat.Prime P) (hP2 : 2 < P) :
    GoldbachWheelK2 P := by
  intro n N
  obtain ⟨a, b, ha0, haP, hb0, hbP, hab⟩ :=
    exists_add_mod_eq_of_three_le (P := P) (by omega) n
  have hPne : P ≠ 0 := hP.ne_zero
  have hca : Nat.Coprime a P := coprime_of_pos_lt_prime hP ha0 haP
  have hcb : Nat.Coprime b P := coprime_of_pos_lt_prime hP hb0 hbP
  obtain ⟨p, hpgt, hpp, hpa⟩ := Nat.forall_exists_prime_gt_and_modEq (max N P) hPne hca
  obtain ⟨q, hqgt, hqp, hqb⟩ := Nat.forall_exists_prime_gt_and_modEq (max N P) hPne hcb
  have hpN : N < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hqN : N < q := lt_of_le_of_lt (le_max_left _ _) hqgt
  have hpP : P < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  have hqP : P < q := lt_of_le_of_lt (le_max_right _ _) hqgt
  refine ⟨p, q, hpN, hqN, hpp, hqp, ?_, ?_, ?_⟩
  · exact (Nat.coprime_primes hpp hP).2 (by omega)
  · exact (Nat.coprime_primes hqp hP).2 (by omega)
  · calc p + q ≡ a + b [MOD P] := Nat.ModEq.add hpa hqb
      _ ≡ n [MOD P] := hab

/-- **New wheel modulus 727.**  The two-prime Goldbach wheel condition holds at `m = 727`:
every residue class mod `727` is a sum `p + q` of two arbitrarily large primes, each coprime
to `727`. -/
theorem GoldbachWheelK2_727 : GoldbachWheelK2 727 :=
  goldbachWheelK2_of_prime_of_two_lt (by norm_num) (by norm_num)

end Brockian

