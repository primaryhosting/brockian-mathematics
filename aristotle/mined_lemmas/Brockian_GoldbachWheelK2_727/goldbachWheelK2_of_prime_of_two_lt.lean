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
