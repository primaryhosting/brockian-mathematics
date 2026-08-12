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

/-! ## A kernel-friendly primality test

Mathlib's `Decidable` instance for `Nat.Prime` performs a linear scan, which makes
`by decide` unusable for numbers of the size we need.  We therefore set up a trial
division test by divisors `≤ 63`, which is sound for all `n < 64 ^ 2 = 4096`.
-/

/-- `noSmallDiv n k = true` asserts that no `d` with `2 ≤ d ≤ k` and `d ≠ n` divides `n`. -/
def noSmallDiv (n : ℕ) : ℕ → Bool
  | 0 => true
  | (k + 1) =>
      ((decide (k + 1 < 2)) || (decide (k + 1 = n)) || (decide (n % (k + 1) ≠ 0)))
        && noSmallDiv n k

lemma noSmallDiv_spec : ∀ {n k : ℕ}, noSmallDiv n k = true →
    ∀ {d : ℕ}, 2 ≤ d → d ≤ k → d ≠ n → ¬ (d ∣ n) := by
  intro n k
  induction k with
  | zero => intro _ d hd2 hdk; omega
  | succ k ih =>
      intro h d hd2 hdk hdn
      rw [noSmallDiv, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      rcases Nat.lt_or_ge d (k + 1) with hlt | hge
      · exact ih h2 hd2 (by omega) hdn
      · have hde : d = k + 1 := by omega
        subst hde
        simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
        rcases h1 with (h1 | h1) | h1
        · omega
        · omega
        · exact fun hdvd => h1 (Nat.dvd_iff_mod_eq_zero.mp hdvd)

lemma prime_of_noSmallDiv {n k : ℕ} (h2 : 2 ≤ n) (hk : n < (k + 1) * (k + 1))
    (h : noSmallDiv n k = true) : Nat.Prime n := by
  by_contra hp
  have hpos : 0 < n := by omega
  have hsq : n.minFac * n.minFac ≤ n := by
    have := Nat.minFac_sq_le_self hpos hp
    nlinarith [this]
  have hmf2 : 2 ≤ n.minFac := (Nat.minFac_prime (by omega)).two_le
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ k := by nlinarith
  have hne : n.minFac ≠ n := by nlinarith
  exact noSmallDiv_spec h hmf2 hle hne hdvd

/-- Boolean primality test; it is sound (`prime_of_isPrimeB`) for all `n < 4096`. -/
def isPrimeB (n : ℕ) : Bool := decide (2 ≤ n) && noSmallDiv n 63

lemma prime_of_isPrimeB {n : ℕ} (hn : n < 4096) (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact prime_of_noSmallDiv h.1 (by omega) h.2

/-! ## Searching for a Goldbach representation -/

/-- `gbFrom n p f` searches, among the `f` candidates `p, p+1, …, p+f-1`, for a prime `a ≤ n`
such that `n - a` is also prime. -/
def gbFrom (n : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | p, (f + 1) => (decide (p ≤ n) && isPrimeB p && isPrimeB (n - p)) || gbFrom n (p + 1) f

lemma gbFrom_spec {n : ℕ} (hn : n < 4096) : ∀ {f p : ℕ}, gbFrom n p f = true →
    ∃ a b : ℕ, Nat.Prime a ∧ Nat.Prime b ∧ a + b = n := by
  intro f
  induction f with
  | zero => intro p h; simp [gbFrom] at h
  | succ f ih =>
      intro p h
      rw [gbFrom, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨hle, hp⟩, hq⟩ := h
        refine ⟨p, n - p, prime_of_isPrimeB (by omega) hp,
          prime_of_isPrimeB (by omega) hq, by omega⟩
      · exact ih h

/-- `allGB K = true` checks the Goldbach property for all even numbers `4, 6, …, 2K + 2`. -/
def allGB : ℕ → Bool
  | 0 => true
  | (k + 1) => gbFrom (2 * k + 4) 2 128 && allGB k

lemma allGB_spec : ∀ {K : ℕ}, allGB K = true → ∀ {k : ℕ}, k < K →
    gbFrom (2 * k + 4) 2 128 = true := by
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
      intro h k hk
      rw [allGB, Bool.and_eq_true] at h
      rcases Nat.lt_or_ge k K with hlt | hge
      · exact ih h.2 hlt
      · have : k = K := by omega
        subst this
        exact h.1

/-! ## The wheel statement -/

/-- `m` is a **Goldbach K2 wheel modulus** when `m` is prime and the whole wheel window
`[4, 2 * m]` is covered by the binary (`K2`) Goldbach property: every even `n` in that
window is a sum of two primes. -/
def IsGoldbachWheelK2 (m : ℕ) : Prop :=
  Nat.Prime m ∧
    ∀ n : ℕ, 4 ≤ n → n ≤ 2 * m → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

private lemma allGB_1326 : allGB 1326 = true := by decide +kernel

/-- **New wheel modulus.** `1327` is a Goldbach K2 wheel modulus: it is prime, and every
even number `n` with `4 ≤ n ≤ 2654` is the sum of two primes. -/
theorem GoldbachWheelK2_1327 : IsGoldbachWheelK2 1327 := by
  refine ⟨by norm_num, ?_⟩
  intro n h4 hle hev
  obtain ⟨m, hm⟩ := hev
  have hk : 2 * ((n - 4) / 2) + 4 = n := by omega
  have hlt : (n - 4) / 2 < 1326 := by omega
  have := gbFrom_spec (n := 2 * ((n - 4) / 2) + 4) (by omega) (allGB_spec allGB_1326 hlt)
  rw [hk] at this
  exact this

end Brockian

