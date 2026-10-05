/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
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

set_option grind.warning false

namespace Brockian

/-- The `K2` Goldbach wheel property at modulus `m`:

every residue class `r` modulo `m` is represented as `p + q` with `p`, `q` prime, where moreover
the two primes may be taken arbitrarily large (larger than any prescribed bound `N`).

This is the "wheel" (residue-class) shadow of the binary Goldbach problem: it says that, modulo
`m`, no congruence obstruction can rule out a representation as a sum of two primes, uniformly in
the size of the primes used. -/
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ (N : ℕ) (r : ZMod m), ∃ p q : ℕ,
    N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod m) + (q : ZMod m) = r

/-- Auxiliary "wheel splitting" property: every residue modulo `m` is a sum of two units of
`ZMod m`.  Units are precisely the residues that can contain large primes, so this is the exact
residue-theoretic content of `GoldbachWheelK2`. -/
def SplitsIntoUnits (m : ℕ) : Prop :=
  ∀ r : ZMod m, ∃ c d : ZMod m, IsUnit c ∧ IsUnit d ∧ c + d = r

theorem splitsIntoUnits_one : SplitsIntoUnits 1 := fun _ =>
  ⟨0, 0, isUnit_of_subsingleton _, isUnit_of_subsingleton _, Subsingleton.elim _ _⟩

/-- In `ZMod (p ^ n)` for a prime `p`, being a unit is detected by the reduction map to
`ZMod p`. -/
theorem isUnit_zmod_prime_pow_iff {p n : ℕ} (hp : Nat.Prime p) (hn : 0 < n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ (ZMod.castHom (dvd_pow_self p hn.ne') (ZMod p)) x ≠ 0 := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.pos.ne'⟩
  have hx : ((x.val : ℕ) : ZMod (p ^ n)) = x := ZMod.natCast_rightInverse x
  rw [← hx, ZMod.isUnit_iff_coprime, map_natCast, Ne, ZMod.natCast_eq_zero_iff,
    Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.coprime_iff_not_dvd]

/-- Odd prime power moduli split every residue into a sum of two units: one of `1 + (r - 1)` and
`2 + (r - 2)` works, since `1` and `2` are distinct nonzero residues modulo an odd prime. -/
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
theorem splitsIntoUnits_mul {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : SplitsIntoUnits a) (hb : SplitsIntoUnits b) : SplitsIntoUnits (a * b) := by
  intro r
  set e := ZMod.chineseRemainder hab with he
  obtain ⟨c1, d1, hc1, hd1, h1⟩ := ha (e r).1
  obtain ⟨c2, d2, hc2, hd2, h2⟩ := hb (e r).2
  refine ⟨e.symm (c1, c2), e.symm (d1, d2), (Prod.isUnit_iff.mpr ⟨hc1, hc2⟩).map e.symm,
    (Prod.isUnit_iff.mpr ⟨hd1, hd2⟩).map e.symm, ?_⟩
  rw [← map_add]
  have hsum : ((c1, c2) + (d1, d2) : ZMod a × ZMod b) = e r := by
    rw [Prod.mk_add_mk, h1, h2]
  rw [hsum, e.symm_apply_apply]

/-- Every odd modulus splits every residue class into a sum of two units. -/
theorem splitsIntoUnits_of_odd : ∀ {m : ℕ}, Odd m → SplitsIntoUnits m := by
  suffices h : ∀ m : ℕ, Odd m → SplitsIntoUnits m from fun {m} => h m
  intro m
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
      intro hodd
      exact splitsIntoUnits_prime_pow hp ((Nat.odd_pow_iff hn.ne').mp hodd) hn
  | zero => intro h; simp [Nat.odd_iff] at h
  | one => intro _; exact splitsIntoUnits_one
  | coprime a b _ _ hab iha ihb =>
      intro hodd
      exact splitsIntoUnits_mul hab (iha (Nat.odd_mul.mp hodd).1) (ihb (Nat.odd_mul.mp hodd).2)

/-- Every odd modulus is a `K2` Goldbach wheel modulus.  The proof combines the wheel splitting
lemma with Dirichlet's theorem on primes in arithmetic progressions. -/
theorem goldbachWheelK2_of_odd {m : ℕ} (hm : Odd m) : GoldbachWheelK2 m := by
  haveI : NeZero m := ⟨by rintro rfl; simp [Nat.odd_iff] at hm⟩
  intro N r
  obtain ⟨c, d, hc, hd, hcd⟩ := splitsIntoUnits_of_odd hm r
  obtain ⟨p, hpN, hp, hpc⟩ := Nat.forall_exists_prime_gt_and_eq_mod hc N
  obtain ⟨q, hqN, hq, hqd⟩ := Nat.forall_exists_prime_gt_and_eq_mod hd N
  exact ⟨p, q, hpN, hqN, hp, hq, by rw [hpc, hqd, hcd]⟩

/-- An even modulus is never a `K2` Goldbach wheel modulus: modulo `2` a sum of two primes bigger
than `2` is always even, so the odd residue classes are missed. -/
theorem not_goldbachWheelK2_of_two_dvd {m : ℕ} (hm : 2 ∣ m) : ¬ GoldbachWheelK2 m := by
  intro h
  obtain ⟨p, q, hpN, hqN, hp, hq, hsum⟩ := h 2 1
  have hcast := congrArg (ZMod.castHom hm (ZMod 2)) hsum
  rw [map_add, map_one, map_natCast, map_natCast] at hcast
  have hp1 : ((p : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))]; norm_num
  have hq1 : ((q : ℕ) : ZMod 2) = 1 := by
    rw [← ZMod.natCast_mod, Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))]; norm_num
  rw [hp1, hq1] at hcast
  exact absurd hcast (by decide)

/-- Characterisation of the `K2` Goldbach wheel moduli: they are exactly the odd numbers. -/
theorem goldbachWheelK2_iff_odd (m : ℕ) : GoldbachWheelK2 m ↔ Odd m := by
  refine ⟨fun h => ?_, goldbachWheelK2_of_odd⟩
  by_contra hodd
  exact not_goldbachWheelK2_of_two_dvd (Nat.not_odd_iff_even.mp hodd).two_dvd h

/-- **Target.** `947` is a `K2` Goldbach wheel modulus. -/
theorem GoldbachWheelK2_947 : GoldbachWheelK2 947 :=
  goldbachWheelK2_of_odd (by decide)

/-- A new composite wheel modulus: `3 * 5 * 7 * 11 = 1155`. -/
theorem GoldbachWheelK2_1155 : GoldbachWheelK2 1155 :=
  goldbachWheelK2_of_odd (by decide)

/-- A new odd prime-power wheel modulus: `3 ^ 5 = 243`. -/
theorem GoldbachWheelK2_243 : GoldbachWheelK2 243 :=
  goldbachWheelK2_of_odd (by decide)

/-- The classical even wheel moduli (such as `2`, `6`, `30`, `210`, `2310`) are *not* `K2`
Goldbach wheel moduli in this sense. -/
theorem not_GoldbachWheelK2_2310 : ¬ GoldbachWheelK2 2310 :=
  not_goldbachWheelK2_of_two_dvd (by norm_num)

end Brockian

#print axioms Brockian.GoldbachWheelK2_947
#print axioms Brockian.goldbachWheelK2_iff_odd
#print axioms Brockian.GoldbachWheelK2_1155
#print axioms Brockian.GoldbachWheelK2_243
#print axioms Brockian.not_GoldbachWheelK2_2310

