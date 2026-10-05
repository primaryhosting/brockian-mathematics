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

import Mathlib

/-!
# Landau Fourth Conjecture
Category: Brockian Conjecture
Target: Brockian.LandauNSquaredPlusOne.LandauFourthConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian
namespace LandauNSquaredPlusOne

open Set

/-- The set of natural numbers `n` for which `n ^ 2 + 1` is prime. -/
def LandauSet : Set ℕ := {n : ℕ | Nat.Prime (n ^ 2 + 1)}

/-- Landau's fourth problem: there are infinitely many primes of the form `n ^ 2 + 1`. -/
def LandauFourthStatement : Prop := LandauSet.Infinite

/-- Sieve-theoretic hypothesis: infinitely often the number `n ^ 2 + 1` has no prime
factor `≤ n`. -/
def NoSmallPrimeFactorInfinitelyOften : Prop :=
  ∀ N : ℕ, ∃ n > N, ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p

/-! ### Elementary facts about `n ^ 2 + 1` -/

/-- If every prime factor of `n ^ 2 + 1` exceeds `n` (and `n ≥ 1`), then `n ^ 2 + 1` is prime. -/
theorem prime_of_no_small_prime_factor {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p) : Nat.Prime (n ^ 2 + 1) := by
  by_contra hnp
  have h2 : 2 ≤ n ^ 2 + 1 := by nlinarith
  have hmf : (n ^ 2 + 1).minFac ^ 2 ≤ n ^ 2 + 1 :=
    Nat.minFac_sq_le_self (by omega) hnp
  have hp : ((n ^ 2 + 1).minFac).Prime := Nat.minFac_prime (by omega)
  have hdvd : (n ^ 2 + 1).minFac ∣ n ^ 2 + 1 := Nat.minFac_dvd _
  have := h _ hp hdvd
  nlinarith

/-- Conversely, if `n ^ 2 + 1` is prime and `n ≥ 1`, then all of its prime factors exceed `n`. -/
theorem no_small_prime_factor_of_prime {n : ℕ} (hn : 1 ≤ n) (hp : Nat.Prime (n ^ 2 + 1)) :
    ∀ p : ℕ, p.Prime → p ∣ n ^ 2 + 1 → n < p := by
  intro p hpp hdvd
  have : p = n ^ 2 + 1 := ((Nat.prime_dvd_prime_iff_eq hpp hp).1 hdvd)
  subst this
  nlinarith

/-- Any odd prime dividing a number of the form `n ^ 2 + 1` is congruent to `1` modulo `4`. -/
theorem prime_factor_mod_four {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ n ^ 2 + 1) :
    p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq : ((n : ZMod p)) ^ 2 = -1 := by
    have : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).2 hdvd
    push_cast at this
    linear_combination this
  have h3 : p % 4 ≠ 3 := ZMod.mod_four_ne_three_of_sq_eq_neg_one hsq
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  omega

/-! ### An unconditional partial result -/

/-- Unconditionally, infinitely many primes divide some number of the form `n ^ 2 + 1`.
(Equivalently, infinitely many primes `p` have `-1` as a quadratic residue.) -/
theorem infinite_primes_dividing_sq_add_one :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p ∣ n ^ 2 + 1}.Infinite := by
  have hinf : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 4]}.Infinite :=
    Nat.infinite_setOf_prime_modEq_one (k := 4) (by norm_num)
  refine hinf.mono ?_
  rintro p ⟨hp, hmod⟩
  refine ⟨hp, ?_⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 = 1 := by
    have h' := hmod
    unfold Nat.ModEq at h'
    omega
  have : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  obtain ⟨y, hy⟩ := this
  refine ⟨y.val, ?_⟩
  have : ((y.val ^ 2 + 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [sq, ← hy]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 this

/-! ### The conditional reduction -/

/-- **Landau's fourth problem, conditionally.**

Landau's fourth conjecture asserts that there are infinitely many primes of the form
`n ^ 2 + 1`; it is an open problem.  Here we give a Lean-checked reduction: assuming the
sieve-theoretic hypothesis `NoSmallPrimeFactorInfinitelyOften` — that infinitely often
`n ^ 2 + 1` has no prime factor `≤ n` — the set of `n` with `n ^ 2 + 1` prime is infinite. -/
theorem LandauFourthConjecture (h : NoSmallPrimeFactorInfinitelyOften) :
    LandauFourthStatement := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  obtain ⟨n, hnN, hn⟩ := h (max N 1)
  have h1 : 1 ≤ n := le_trans (le_max_right N 1) hnN.le
  have hmem : n ∈ LandauSet := prime_of_no_small_prime_factor h1 hn
  have := hN hmem
  have : N < n := lt_of_le_of_lt (le_max_left N 1) hnN
  omega

/-! ### A second reduction: from Bunyakovsky's conjecture -/

open Polynomial in
/-- **Bunyakovsky's conjecture**: an irreducible integer polynomial of positive degree with no
fixed prime divisor takes infinitely many prime values. -/
def BunyakovskyConjecture : Prop :=
  ∀ f : Polynomial ℤ, 1 ≤ f.natDegree → Irreducible f →
    (∀ p : ℕ, p.Prime → ∃ m : ℤ, ¬ ((p : ℤ) ∣ f.eval m)) →
    ∀ N : ℤ, ∃ m : ℤ, N < m ∧ Prime (f.eval m)

open Polynomial in
/-- The polynomial `X ^ 2 + 1` is irreducible over `ℤ` (it stays irreducible mod `3`). -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  have hm : (X ^ 2 + 1 : ℤ[X]).Monic := by monicity!
  refine hm.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3)) _ ?_
  have hmap : ((X ^ 2 + 1 : ℤ[X]).map (Int.castRingHom (ZMod 3))) = X ^ 2 + 1 := by simp
  rw [hmap]
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have h2 : (X ^ 2 + 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    simp [h2]
  · intro x hx
    have hx2 : x ^ 2 + 1 = 0 := by simpa [Polynomial.IsRoot] using hx
    clear hx
    revert hx2
    revert x
    decide

open Polynomial in
/-- Bunyakovsky's conjecture implies Landau's fourth conjecture, applied to `X ^ 2 + 1`. -/
theorem landauFourth_of_bunyakovsky (hB : BunyakovskyConjecture) : LandauFourthStatement := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨N, hN⟩
  have hdeg : 1 ≤ (X ^ 2 + 1 : ℤ[X]).natDegree := by
    have : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by compute_degree!
    omega
  have hfix : ∀ p : ℕ, p.Prime → ∃ m : ℤ, ¬ ((p : ℤ) ∣ (X ^ 2 + 1 : ℤ[X]).eval m) := by
    intro p hp
    refine ⟨0, ?_⟩
    simp only [eval_add, eval_pow, eval_X, eval_one]
    norm_num
    intro h
    have : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h
    exact hp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨m, hm, hprime⟩ := hB (X ^ 2 + 1) hdeg irreducible_X_sq_add_one hfix (N : ℤ)
  have heval : (X ^ 2 + 1 : ℤ[X]).eval m = m ^ 2 + 1 := by simp
  rw [heval] at hprime
  have hm0 : 0 ≤ m := le_trans (Int.natCast_nonneg N) hm.le
  set n : ℕ := m.natAbs
  have hnm : (n : ℤ) = m := Int.natAbs_of_nonneg hm0
  have hmem : n ∈ LandauSet := by
    have : Prime ((n ^ 2 + 1 : ℕ) : ℤ) := by push_cast [hnm]; exact hprime
    exact Nat.prime_iff_prime_int.2 this
  have hle := hN hmem
  have : (N : ℤ) < (n : ℤ) := by rw [hnm]; exact hm
  exact absurd hle (by exact_mod_cast not_le.2 (by exact_mod_cast this))

/-- The hypothesis used above is in fact *equivalent* to Landau's fourth conjecture, so the
reduction above loses nothing. -/
theorem landauFourth_iff_noSmallPrimeFactor :
    LandauFourthStatement ↔ NoSmallPrimeFactorInfinitelyOften := by
  constructor
  · intro h N
    obtain ⟨n, hn, hnN⟩ := h.exists_gt (max N 1)
    have h1 : 1 ≤ n := le_trans (le_max_right N 1) hnN.le
    exact ⟨n, lt_of_le_of_lt (le_max_left N 1) hnN,
      no_small_prime_factor_of_prime h1 hn⟩
  · exact LandauFourthConjecture

end LandauNSquaredPlusOne
end Brockian

