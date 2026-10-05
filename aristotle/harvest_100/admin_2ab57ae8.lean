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

/-
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Repunit Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.RepunitPrimes.RepunitPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace RepunitPrimes

open Finset

/-- The `n`-th repunit: the number written with `n` copies of the digit `1` in base ten,
i.e. `repunit n = (10 ^ n - 1) / 9 = ∑_{i < n} 10 ^ i`. -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

@[simp] lemma repunit_zero : repunit 0 = 0 := rfl

@[simp] lemma repunit_one : repunit 1 = 1 := rfl

lemma repunit_two : repunit 2 = 11 := rfl

lemma repunit_succ (n : ℕ) : repunit (n + 1) = repunit n + 10 ^ n :=
  Finset.sum_range_succ _ _

/-- The repunits are strictly increasing. -/
lemma repunit_strictMono : StrictMono repunit := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [repunit_succ]
  exact Nat.lt_add_of_pos_right (pow_pos (by norm_num) n)

lemma repunit_injective : Function.Injective repunit :=
  repunit_strictMono.injective

/-- The closed form `9 * repunit n + 1 = 10 ^ n`. -/
lemma nine_mul_repunit (n : ℕ) : 9 * repunit n + 1 = 10 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repunit_succ]; ring_nf; ring_nf at ih; omega

/-- Splitting a repunit index as a sum. -/
lemma repunit_add (m k : ℕ) : repunit (m + k) = repunit m + 10 ^ m * repunit k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← Nat.add_assoc, repunit_succ, repunit_succ, ih, pow_add]
      ring

/-- If `m ∣ n` then `repunit m ∣ repunit n`. -/
lemma repunit_dvd_repunit_of_dvd {m n : ℕ} (h : m ∣ n) : repunit m ∣ repunit n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.mul_succ, repunit_add]
      exact Nat.dvd_add ih (Dvd.dvd.mul_left dvd_rfl _)

/-- A repunit can only be prime if its index is prime. -/
theorem prime_index_of_repunit_prime {n : ℕ} (h : Nat.Prime (repunit n)) : Nat.Prime n := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at h; exact Nat.not_prime_zero h
  have hn1 : n ≠ 1 := by rintro rfl; simp at h; exact Nat.not_prime_one h
  have hn2 : 2 ≤ n := by omega
  refine Nat.prime_def.mpr ⟨hn2, ?_⟩
  intro m hm
  have hdvd : repunit m ∣ repunit n := repunit_dvd_repunit_of_dvd hm
  rcases (Nat.Prime.eq_one_or_self_of_dvd h _ hdvd) with h1 | h2
  · left
    have : repunit m = repunit 1 := by simpa using h1
    exact repunit_injective this
  · right
    exact repunit_injective h2

/-- `11 = repunit 2` is a repunit prime, so the sets below are nonempty. -/
lemma repunit_two_prime : Nat.Prime (repunit 2) := by
  rw [repunit_two]; norm_num

/-- The set of indices `n` for which `repunit n` is prime. -/
def RepunitPrimeIndices : Set ℕ := {n | Nat.Prime (repunit n)}

/-- The set of repunit primes. -/
def RepunitPrimeSet : Set ℕ := {p | Nat.Prime p ∧ ∃ n, p = repunit n}

/-- The indices of repunit primes are themselves prime. -/
theorem repunitPrimeIndices_eq :
    RepunitPrimeIndices = {n | Nat.Prime n ∧ Nat.Prime (repunit n)} := by
  ext n
  exact ⟨fun h => ⟨prime_index_of_repunit_prime h, h⟩, fun h => h.2⟩

/--
**Repunit prime infinitude, reduced to prime indices.**

Whether there are infinitely many repunit primes is an open problem; this theorem is a
Lean-checked *reduction* of that question.  It states that the set of repunit primes is
infinite if and only if there are infinitely many *prime* exponents `p` for which the
repunit `repunit p = (10 ^ p - 1) / 9` is prime.  In particular one never has to look at
composite exponents: the two formulations of the conjecture are equivalent.
-/
theorem RepunitPrimeInfinitude :
    RepunitPrimeSet.Infinite ↔ {p : ℕ | Nat.Prime p ∧ Nat.Prime (repunit p)}.Infinite := by
  constructor
  · intro h
    have hsub : RepunitPrimeSet ⊆ repunit '' {p : ℕ | Nat.Prime p ∧ Nat.Prime (repunit p)} := by
      rintro p ⟨hp, n, rfl⟩
      exact ⟨n, ⟨prime_index_of_repunit_prime hp, hp⟩, rfl⟩
    exact Set.Infinite.of_image repunit (h.mono hsub)
  · intro h
    have himg : (repunit '' {p : ℕ | Nat.Prime p ∧ Nat.Prime (repunit p)}).Infinite :=
      h.image (Set.injOn_of_injective repunit_injective)
    refine himg.mono ?_
    rintro q ⟨n, ⟨-, hn⟩, rfl⟩
    exact ⟨hn, n, rfl⟩

/-! ## An unconditional partial result

While the infinitude of repunit *primes* is open, one can prove unconditionally that
infinitely many primes occur as *divisors* of repunits: every prime other than `2` and `5`
divides some repunit. -/

/-- Every prime `p ∉ {2, 5}` divides some repunit. -/
theorem exists_repunit_dvd_of_prime {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h5 : p ≠ 5) :
    ∃ n, 0 < n ∧ p ∣ repunit n := by
  by_cases h3 : p = 3
  · exact ⟨3, by norm_num, by subst h3; decide⟩
  · have hnd : ¬ p ∣ 10 := by
      intro hdvd
      have hdvd' : p ∣ 2 * 5 := by norm_num; exact hdvd
      rcases (Nat.Prime.dvd_mul hp).mp hdvd' with h | h
      · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
      · exact h5 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)
    have hcop : Nat.Coprime 10 p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd)
    have hferm : 10 ^ (p - 1) ≡ 1 [MOD p] := by
      have := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at this
    have hdvd : p ∣ 9 * repunit (p - 1) := by
      have h10 : 9 * repunit (p - 1) + 1 = 10 ^ (p - 1) := nine_mul_repunit _
      have hmod : (9 * repunit (p - 1) + 1) ≡ 1 [MOD p] := by rw [h10]; exact hferm
      have := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
      simpa using this
    have hp9 : ¬ p ∣ 9 := by
      intro hd
      have hd' : p ∣ 3 ^ 2 := by norm_num; exact hd
      exact h3 ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow hd'))
    refine ⟨p - 1, ?_, ?_⟩
    · have := hp.two_le; omega
    · exact Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd hp).mpr hp9) hdvd

/-- Infinitely many primes divide some repunit. -/
theorem infinite_primes_dvd_repunit :
    {p : ℕ | Nat.Prime p ∧ ∃ n, 0 < n ∧ p ∣ repunit n}.Infinite := by
  have hinf : ({p : ℕ | Nat.Prime p} \ {2, 5}).Infinite :=
    Nat.infinite_setOf_prime.diff (Set.toFinite _)
  refine hinf.mono ?_
  rintro p ⟨hp, hne⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  exact ⟨hp, exists_repunit_dvd_of_prime hp hne.1 hne.2⟩

end RepunitPrimes
end Brockian

