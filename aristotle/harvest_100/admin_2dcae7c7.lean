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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`
-- because Lean 4 requires `import` commands to precede every other command, including
-- module docstrings.)

import Mathlib

/-!
# Polignac Conjecture

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is an open problem (the case
`n = 2` is the twin prime conjecture), so what is proved here is a *conditional reduction*:
Polignac's conjecture is derived from Dickson's conjecture on simultaneous primality of
linear forms.

The derivation is the classical one.  Given an even `n ≥ 2`, one chooses for each `j` with
`0 < j < n` a distinct prime `q j > n`, sets `Q = ∏ q j` and uses the Chinese Remainder Theorem
to find `a` with `q j ∣ a + j` for all such `j`.  The pair of linear forms `a + Q x`,
`(a + n) + Q x` is then admissible, so Dickson's conjecture produces arbitrarily large `x`
making both forms prime; and every intermediate value `a + Q x + j` (`0 < j < n`) is divisible
by the prime `q j`, which is smaller than it, hence composite.  So the two primes are
consecutive with difference exactly `n`.
-/

namespace Brockian
namespace PolignacPrimes

open Finset
open scoped Function

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies strictly
between them. -/
def IsConsecutivePrimePair (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ Nat.Prime r

/-- **Dickson's conjecture**: a finite family of linear forms `a i + b i * x` with positive
leading coefficients which is *admissible* (for every prime `r` there is an `x` making none of
the values divisible by `r`) takes simultaneously prime values for arbitrarily large `x`. -/
def DicksonConjecture : Prop :=
  ∀ (k : ℕ) (a b : Fin k → ℕ), (∀ i, 0 < b i) →
    (∀ r : ℕ, r.Prime → ∃ x : ℕ, ∀ i, ¬ (r ∣ a i + b i * x)) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ ∀ i, Nat.Prime (a i + b i * x)

/-! ### Choice of a residue class -/

/-- In `ZMod r` (`r` prime, `n` even) there is a value `v` with `v ≠ 0` and `v + n ≠ 0`. -/
theorem exists_nonzero_shift_nonzero {r n : ℕ} (hr : r.Prime) (hn : Even n) :
    ∃ v : ZMod r, v ≠ 0 ∧ v + (n : ZMod r) ≠ 0 := by
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases h0 : (n : ZMod r) = 0
  · exact ⟨1, one_ne_zero, by simp [h0]⟩
  · have hr2 : r ≠ 2 := by
      rintro rfl
      exact h0 (ZMod.natCast_eq_zero_iff_even.mpr hn)
    by_cases h1 : (1 : ZMod r) + (n : ZMod r) = 0
    · refine ⟨2, ?_, ?_⟩
      · intro h
        have h2 : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
        exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
          ((ZMod.natCast_eq_zero_iff _ _).mp h2))
      · have h3 : (2 : ZMod r) + (n : ZMod r) = ((1 : ZMod r) + n) + 1 := by ring
        rw [h3, h1, zero_add]
        exact one_ne_zero
    · exact ⟨1, one_ne_zero, h1⟩

/-- Admissibility at primes `r` not dividing the common difference `Q`. -/
theorem exists_not_dvd_of_not_dvd {r Q a n : ℕ} (hr : r.Prime) (hQ : ¬ r ∣ Q) (hn : Even n) :
    ∃ x : ℕ, ¬ (r ∣ a + Q * x) ∧ ¬ (r ∣ (a + n) + Q * x) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨v, hv0, hvn⟩ := exists_nonzero_shift_nonzero hr hn
  have hQ0 : (Q : ZMod r) ≠ 0 := fun h => hQ ((ZMod.natCast_eq_zero_iff _ _).mp h)
  set y : ZMod r := (v - (a : ZMod r)) * (Q : ZMod r)⁻¹ with hy
  have key : (a : ZMod r) + (Q : ZMod r) * y = v := by
    rw [hy]; field_simp; ring
  refine ⟨y.val, ?_, ?_⟩
  · intro h
    have h2 : ((a + Q * y.val : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at h2
    rw [ZMod.natCast_val, ZMod.cast_id, key] at h2
    exact hv0 h2
  · intro h
    have h2 : ((a + n + Q * y.val : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    push_cast at h2
    rw [ZMod.natCast_val, ZMod.cast_id] at h2
    apply hvn
    rw [← key]
    linear_combination h2

/-- The Chinese-Remainder step: for every `n` there are `a` and `Q > 0` such that every
intermediate value `a + j` (`0 < j < n`) is divisible by some prime divisor of `Q`, while no
prime divisor of `Q` divides `a` or `a + n`.  (The primes used are the `n`-th, `(n+1)`-st, …
primes, all of which exceed `n`.) -/
theorem exists_residue_class (n : ℕ) :
    ∃ a Q : ℕ, 0 < Q ∧
      (∀ j, 0 < j → j < n → ∃ r, r.Prime ∧ r ∣ Q ∧ r ∣ a + j) ∧
      (∀ r : ℕ, r.Prime → r ∣ Q → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) := by
  classical
  set q : ℕ → ℕ := fun j => Nat.nth Nat.Prime (n + j) with hq
  have hqp : ∀ j, (q j).Prime := fun j => Nat.prime_nth_prime (n + j)
  have hqgt : ∀ j, n < q j := by
    intro j
    have := Nat.add_two_le_nth_prime (n + j)
    simp only [hq]
    omega
  have hqinj : Function.Injective q := by
    intro i j hij
    have := (Nat.nth_injective Nat.infinite_setOf_prime) hij
    omega
  have hs : ∀ i ∈ Finset.Ico 1 n, q i ≠ 0 := fun i _ => (hqp i).pos.ne'
  have pp : Set.Pairwise ((Finset.Ico 1 n : Finset ℕ) : Set ℕ) (Nat.Coprime on q) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hqp i) (hqp j)).mpr (fun h => hij (hqinj h))
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun j => q j - j) q (Finset.Ico 1 n) hs pp
  have hdvd : ∀ j ∈ Finset.Ico 1 n, q j ∣ a + j := by
    intro j hjt
    have hjn : j < n := (Finset.mem_Ico.mp hjt).2
    have h := (ha j hjt).add_right j
    rw [Nat.sub_add_cancel (le_of_lt (lt_trans hjn (hqgt j)))] at h
    exact (Nat.modEq_zero_iff_dvd).mp (h.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  refine ⟨a, ∏ j ∈ Finset.Ico 1 n, q j, Finset.prod_pos (fun i _ => (hqp i).pos), ?_, ?_⟩
  · intro j hj0 hjn
    have hjt : j ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨hj0, hjn⟩
    exact ⟨q j, hqp j, Finset.dvd_prod_of_mem q hjt, hdvd j hjt⟩
  · intro r hr hrQ
    obtain ⟨j, hjt, hrj⟩ := (Nat.Prime.prime hr).exists_mem_finset_dvd hrQ
    have hrq : r = q j := (Nat.prime_dvd_prime_iff_eq hr (hqp j)).mp hrj
    have hj0 := Finset.mem_Ico.mp hjt
    have hd := hdvd j hjt
    subst hrq
    have hgt := hqgt j
    refine ⟨?_, ?_⟩
    · intro hcon
      have h1 : q j ∣ j := by simpa using Nat.dvd_sub hd hcon
      have := Nat.le_of_dvd (by omega) h1
      omega
    · intro hcon
      have h1 : q j ∣ n - j := by simpa [Nat.add_sub_add_left] using Nat.dvd_sub hcon hd
      have := Nat.le_of_dvd (by omega) h1
      omega

/-- **Polignac's conjecture**, conditional on Dickson's conjecture: for every positive even `n`
there are arbitrarily large primes `p` such that `p` and `p + n` are consecutive primes. -/
theorem PolignacConjecture (H : DicksonConjecture) (n : ℕ) (hn : Even n) (hn0 : 0 < n) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ IsConsecutivePrimePair p (p + n) := by
  have hn2 : 2 ≤ n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  obtain ⟨a, Q, hQ0, hint, hdvd⟩ := exists_residue_class n
  set A : Fin 2 → ℕ := ![a, a + n] with hA
  set B : Fin 2 → ℕ := ![Q, Q] with hB
  have hBpos : ∀ i, 0 < B i := by
    intro i
    fin_cases i <;> simpa [hB] using hQ0
  have hadm : ∀ r : ℕ, r.Prime → ∃ x : ℕ, ∀ i, ¬ (r ∣ A i + B i * x) := by
    intro r hr
    by_cases hrQ : r ∣ Q
    · refine ⟨0, ?_⟩
      intro i
      obtain ⟨h1, h2⟩ := hdvd r hr hrQ
      fin_cases i <;> simpa [hA, hB] using ‹_›
    · obtain ⟨x, hx1, hx2⟩ := exists_not_dvd_of_not_dvd (a := a) hr hrQ hn
      refine ⟨x, ?_⟩
      intro i
      fin_cases i
      · simpa [hA, hB] using hx1
      · simpa [hA, hB] using hx2
  obtain ⟨x, hxbig, hprime⟩ := H 2 A B hBpos hadm (N + Q + 1)
  refine ⟨a + Q * x, ?_, ?_⟩
  · have : x ≤ Q * x := Nat.le_mul_of_pos_left x hQ0
    omega
  · have hQx : Q < Q * x := by
      calc Q < x := by omega
        _ ≤ Q * x := Nat.le_mul_of_pos_left x hQ0
    have hp0 : Nat.Prime (a + Q * x) := by simpa [hA, hB] using hprime 0
    have hp1 : Nat.Prime (a + Q * x + n) := by
      have h1 := hprime 1
      simp only [hA, hB, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      have he : a + n + Q * x = a + Q * x + n := by ring
      rwa [he] at h1
    refine ⟨hp0, hp1, by omega, ?_⟩
    intro r hr1 hr2 hrp
    obtain ⟨s, hs, hsQ, hsdvd⟩ := hint (r - (a + Q * x)) (by omega) (by omega)
    have hsr : s ∣ r := by
      have hre : r = a + (r - (a + Q * x)) + Q * x := by omega
      rw [hre]
      exact hsdvd.add (hsQ.mul_right x)
    have hsle : s ≤ Q := Nat.le_of_dvd hQ0 hsQ
    have := (Nat.Prime.eq_one_or_self_of_dvd hrp s hsr).resolve_left hs.one_lt.ne'
    omega

/-- Restatement of the conditional Polignac conjecture as an infinitude statement: conditional
on Dickson's conjecture, for every positive even `n` infinitely many primes `p` are such that
`p` and `p + n` are consecutive primes. -/
theorem infinite_consecutive_prime_pairs_of_dickson (H : DicksonConjecture) (n : ℕ)
    (hn : Even n) (hn0 : 0 < n) :
    {p : ℕ | IsConsecutivePrimePair p (p + n)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun N => ?_)
  obtain ⟨p, hp, hcons⟩ := PolignacConjecture H n hn hn0 N
  exact ⟨p, hcons, hp⟩

/-- The twin prime conjecture is the case `n = 2`. -/
theorem twin_primes_of_dickson (H : DicksonConjecture) :
    {p : ℕ | IsConsecutivePrimePair p (p + 2)}.Infinite :=
  infinite_consecutive_prime_pairs_of_dickson H 2 (by decide) (by norm_num)

/-- A sanity check that `IsConsecutivePrimePair` is satisfiable: `3` and `5` are consecutive
primes. -/
theorem isConsecutivePrimePair_three_five : IsConsecutivePrimePair 3 5 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro r h1 h2
  interval_cases r
  norm_num

end PolignacPrimes
end Brockian

