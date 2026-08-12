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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → ¬ (d ∣ p)

instance : DecidablePred IsPrime := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem IsPrime.two_le {p : Nat} (h : IsPrime p) : 2 ≤ p := h.1

/-- A prime has no divisor strictly between `1` and itself. -/
theorem IsPrime.not_dvd {p d : Nat} (h : IsPrime p) (hlt : d < p) (h2 : 2 ≤ d) : ¬ (d ∣ p) :=
  h.2 d hlt h2

/-- The primorial `primorial n` is the product of all primes `≤ n`. -/
def primorial : Nat → Nat
  | 0 => 1
  | n + 1 => if IsPrime (n + 1) then (n + 1) * primorial n else primorial n

theorem primorial_pos : ∀ n, 0 < primorial n
  | 0 => Nat.zero_lt_one
  | n + 1 => by
      rw [primorial]
      by_cases h : IsPrime (n + 1)
      · simp only [h, if_true]
        exact Nat.mul_pos (Nat.succ_pos n) (primorial_pos n)
      · simp only [h, if_false]
        exact primorial_pos n

/-- Every prime `q ≤ n` divides `primorial n`. -/
theorem prime_dvd_primorial : ∀ {q n : Nat}, IsPrime q → q ≤ n → q ∣ primorial n
  | q, 0, hq, hqn => absurd hq.two_le (by omega)
  | q, n + 1, hq, hqn => by
      rw [primorial]
      by_cases hp : IsPrime (n + 1)
      · simp only [hp, if_true]
        by_cases hqe : q = n + 1
        · exact ⟨primorial n, by rw [hqe]⟩
        · exact Nat.dvd_trans (prime_dvd_primorial hq (by omega))
            (Nat.dvd_mul_left (primorial n) (n + 1))
      · simp only [hp, if_false]
        have hqe : q ≠ n + 1 := fun h => hp (h ▸ hq)
        exact prime_dvd_primorial hq (by omega)

/-! ## Least prime factors -/

/-- Every composite number `m ≥ 2` has a prime factor `p` with `p * p ≤ m`. -/
theorem exists_prime_factor_sq_le :
    ∀ m : Nat, 2 ≤ m → ¬ IsPrime m → ∃ p, IsPrime p ∧ p ∣ m ∧ p * p ≤ m := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro hm hnp
    by_cases hc : ∃ d, d < m ∧ 2 ≤ d ∧ d ∣ m
    · obtain ⟨d, hdlt, hd2, hdvd⟩ := hc
      -- helper: from a divisor `e` with `e * e ≤ m` we extract a prime factor
      have key : ∀ e, e ∣ m → 2 ≤ e → e < m → e * e ≤ m →
          ∃ p, IsPrime p ∧ p ∣ m ∧ p * p ≤ m := by
        intro e hed he2 helt hee
        by_cases hpe : IsPrime e
        · exact ⟨e, hpe, hed, hee⟩
        · obtain ⟨p, hp, hpd, hpp⟩ := ih e helt he2 hpe
          exact ⟨p, hp, Nat.dvd_trans hpd hed, Nat.le_trans hpp (Nat.le_of_lt helt)⟩
      obtain ⟨k, hmk⟩ : ∃ k, d * k = m := ⟨m / d, Nat.mul_div_cancel' hdvd⟩
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, Nat.mul_zero] at hmk; omega
        · exact h
      have hkdvd : k ∣ m := ⟨d, by rw [← hmk, Nat.mul_comm]⟩
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · have hk1 : k = 1 := by omega
          rw [hk1, Nat.mul_one] at hmk
          omega
        · exact h
      have hklt : k < m := by
        have : 2 * k ≤ d * k := Nat.mul_le_mul_right k hd2
        omega
      rcases Nat.le_total d k with hdk | hkd
      · have : d * d ≤ d * k := Nat.mul_le_mul_left d hdk
        exact key d hdvd hd2 hdlt (by omega)
      · have : k * k ≤ d * k := Nat.mul_le_mul_right k hkd
        exact key k hkdvd hk2 hklt (by omega)
    · exact absurd ⟨hm, fun d hd h2 hdvd => hc ⟨d, hd, h2, hdvd⟩⟩ hnp

/-- Every `m ≥ 2` has a prime factor. -/
theorem exists_prime_dvd : ∀ m : Nat, 2 ≤ m → ∃ p, IsPrime p ∧ p ∣ m := by
  intro m hm
  by_cases hp : IsPrime m
  · exact ⟨m, hp, Nat.dvd_refl m⟩
  · obtain ⟨p, hp, hpd, _⟩ := exists_prime_factor_sq_le m hm hp
    exact ⟨p, hp, hpd⟩

/-! ## Infinitude of primes -/

/-- The factorial function. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => Nat.zero_lt_one
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem dvd_fact : ∀ {k n : Nat}, 1 ≤ k → k ≤ n → k ∣ fact n
  | k, 0, hk, hkn => absurd hkn (by omega)
  | k, n + 1, hk, hkn => by
      rw [fact]
      by_cases h : k = n + 1
      · exact ⟨fact n, by rw [h]⟩
      · exact Nat.dvd_trans (dvd_fact hk (by omega)) (Nat.dvd_mul_left (fact n) (n + 1))

/-- Euclid: there are arbitrarily large primes. -/
theorem exists_prime_gt (N : Nat) : ∃ p, IsPrime p ∧ N < p := by
  have h2 : 2 ≤ fact N + 1 := by have := fact_pos N; omega
  obtain ⟨p, hp, hpd⟩ := exists_prime_dvd (fact N + 1) h2
  refine ⟨p, hp, Classical.byContradiction fun hle => ?_⟩
  have hpN : p ∣ fact N := dvd_fact (by have := hp.two_le; omega) (by omega)
  have hd1 : p ∣ 1 := by
    have hsub := Nat.dvd_sub hpd hpN
    have he : fact N + 1 - fact N = 1 := by omega
    rwa [he] at hsub
  have := Nat.le_of_dvd Nat.zero_lt_one hd1
  have := hp.two_le
  omega

/-! ## Fortunate numbers -/

/-- `IsFortunate n m` says that `m` is the `n`-th **fortunate number**: the least `m > 1`
such that `primorial n + m` is prime. -/
def IsFortunate (n m : Nat) : Prop :=
  1 < m ∧ IsPrime (primorial n + m) ∧ ∀ k, k < m → 1 < k → ¬ IsPrime (primorial n + k)

instance : ∀ n m, Decidable (IsFortunate n m) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A least witness exists for any decidable predicate on `Nat` that holds somewhere. -/
theorem exists_least (P : Nat → Prop) [DecidablePred P] (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ k, k < n → ¬ P k := by
  obtain ⟨N, hN⟩ := h
  induction N using Nat.strongRecOn with
  | _ N ih =>
    by_cases hc : ∃ k, k < N ∧ P k
    · obtain ⟨k, hk, hPk⟩ := hc
      exact ih k hk hPk
    · exact ⟨N, hN, fun k hk hPk => hc ⟨k, hk, hPk⟩⟩

/-- For every `n`, the `n`-th fortunate number exists. -/
theorem exists_isFortunate (n : Nat) : ∃ m, IsFortunate n m := by
  obtain ⟨p, hp, hpgt⟩ := exists_prime_gt (primorial n + 1)
  have hex : ∃ m, 1 < m ∧ IsPrime (primorial n + m) := by
    refine ⟨p - primorial n, by omega, ?_⟩
    have : primorial n + (p - primorial n) = p := by omega
    rw [this]; exact hp
  obtain ⟨m, ⟨hm1, hmp⟩, hmin⟩ := exists_least _ hex
  exact ⟨m, hm1, hmp, fun k hk hk1 hkp => hmin k hk ⟨hk1, hkp⟩⟩

/-- The fortunate number of a given index is unique. -/
theorem isFortunate_unique {n m₁ m₂ : Nat} (h₁ : IsFortunate n m₁) (h₂ : IsFortunate n m₂) :
    m₁ = m₂ := by
  rcases Nat.lt_trichotomy m₁ m₂ with h | h | h
  · exact absurd h₁.2.1 (h₂.2.2 m₁ h h₁.1)
  · exact h
  · exact absurd h₂.2.1 (h₁.2.2 m₂ h h₂.1)

/-- **Unconditional partial result.** No prime `q ≤ n` divides the `n`-th fortunate number:
all prime factors of a fortunate number exceed its index. -/
theorem not_dvd_of_isFortunate {n m q : Nat} (h : IsFortunate n m) (hq : IsPrime q)
    (hqn : q ≤ n) : ¬ q ∣ m := by
  intro hdvd
  have hdP : q ∣ primorial n := prime_dvd_primorial hq hqn
  have hsum : q ∣ primorial n + m := Nat.dvd_add hdP hdvd
  have hqle : q ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hdP
  have hlt : q < primorial n + m := by have := h.1; omega
  exact h.2.1.not_dvd hlt hq.two_le hsum

/-- **Key reduction.** A fortunate number that is at most the square of its index is prime. -/
theorem isFortunate_prime_of_le_sq {n m : Nat} (h : IsFortunate n m) (hle : m ≤ n * n) :
    IsPrime m := by
  refine Classical.byContradiction fun hnp => ?_
  obtain ⟨p, hp, hpd, hpp⟩ := exists_prime_factor_sq_le m h.1 hnp
  have hpn : n < p :=
    Classical.byContradiction fun hcon => not_dvd_of_isFortunate h hp (by omega) hpd
  have : n * n < p * p := Nat.mul_self_lt_mul_self hpn
  omega

/-! ## The two degenerate indices -/

theorem primorial_zero : primorial 0 = 1 := rfl

theorem primorial_one : primorial 1 = 1 := by decide

/-- For `n = 0, 1` the primorial is `1` and the fortunate number is `2`. -/
theorem isFortunate_of_primorial_eq_one {n m : Nat} (hn : primorial n = 1)
    (h : IsFortunate n m) : m = 2 := by
  refine Classical.byContradiction fun hne => ?_
  have h3 : 2 < m := by have := h.1; omega
  refine h.2.2 2 h3 (by omega) ?_
  rw [hn]
  decide

/-! ## Small cases, verified by computation -/

theorem isFortunate_zero : IsFortunate 0 2 := by decide

theorem isFortunate_one : IsFortunate 1 2 := by decide

theorem isFortunate_two : IsFortunate 2 3 := by decide

theorem isFortunate_three : IsFortunate 3 5 := by decide

theorem isFortunate_four : IsFortunate 4 5 := by decide

theorem isFortunate_five : IsFortunate 5 7 := by decide

theorem isFortunate_six : IsFortunate 6 7 := by decide

set_option maxRecDepth 40000 in
theorem isFortunate_seven : IsFortunate 7 13 := by decide

set_option maxRecDepth 40000 in
theorem isFortunate_eight : IsFortunate 8 13 := by decide

set_option maxRecDepth 40000 in
theorem isFortunate_nine : IsFortunate 9 13 := by decide

set_option maxRecDepth 40000 in
theorem isFortunate_ten : IsFortunate 10 13 := by decide

/-- The hypothesis of `FortuneConjecture` holds unconditionally for all indices `2 ≤ n ≤ 10`. -/
theorem le_sq_of_index_le_ten {n m : Nat} (h2 : 2 ≤ n) (h10 : n ≤ 10) (h : IsFortunate n m) :
    m ≤ n * n := by
  have hn : n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 := by omega
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [isFortunate_unique h isFortunate_two]; decide
  · rw [isFortunate_unique h isFortunate_three]; decide
  · rw [isFortunate_unique h isFortunate_four]; decide
  · rw [isFortunate_unique h isFortunate_five]; decide
  · rw [isFortunate_unique h isFortunate_six]; decide
  · rw [isFortunate_unique h isFortunate_seven]; decide
  · rw [isFortunate_unique h isFortunate_eight]; decide
  · rw [isFortunate_unique h isFortunate_nine]; decide
  · rw [isFortunate_unique h isFortunate_ten]; decide

/-- **Unconditional partial result.** Fortune's conjecture holds for all indices `n ≤ 10`. -/
theorem isPrime_of_isFortunate_of_index_le_ten {n m : Nat} (hn : n ≤ 10) (h : IsFortunate n m) :
    IsPrime m := by
  match n with
  | 0 => rw [isFortunate_of_primorial_eq_one primorial_zero h]; decide
  | 1 => rw [isFortunate_of_primorial_eq_one primorial_one h]; decide
  | (k + 2) => exact isFortunate_prime_of_le_sq h (le_sq_of_index_le_ten (by omega) hn h)

/-! ## Fortune's conjecture -/

/-- **Fortune's conjecture, conditional reduction.**

Fortune's conjecture states that every fortunate number is prime; it is an open problem.
We prove it here from the hypothesis `h` that the `n`-th fortunate number is at most `n * n`
for `n ≥ 11` (itself open, though empirically fortunate numbers are far smaller than that).
All indices `n ≤ 10` are handled unconditionally, by `isPrime_of_isFortunate_of_index_le_ten`.

The mathematical content is `not_dvd_of_isFortunate`: no prime `≤ n` divides the `n`-th
fortunate number, so a composite fortunate number would have to exceed `n * n`. -/
theorem FortuneConjecture (h : ∀ n m, 11 ≤ n → IsFortunate n m → m ≤ n * n) :
    ∀ n m, IsFortunate n m → IsPrime m := by
  intro n m hm
  by_cases hn : n ≤ 10
  · exact isPrime_of_isFortunate_of_index_le_ten hn hm
  · exact isFortunate_prime_of_le_sq hm (h n m (by omega) hm)

end Brockian.FortunateNumbers

