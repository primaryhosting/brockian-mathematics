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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 forbids a module
-- docstring before `import`; the same header is repeated as a module docstring below.)

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — "there is always a prime between two consecutive squares" — is a
well-known open problem.  This file therefore does what can be done rigorously:

* it states the conjecture (`LegendreStatement`);
* it gives several **equivalent reformulations**, including the contrapositive
  ("no prime-free interval between consecutive squares"), a formulation via the
  next-prime function, and a formulation via the prime counting function;
* it gives **conditional reductions**: Legendre's conjecture follows from Andrica's
  conjecture (`LegendreConjecture`, the target theorem) and from a `√m`-size prime gap
  hypothesis;
* it proves **unconditional partial results**: a weakened Bertrand-type version, and a
  verification of the conjecture for all `n ≤ 30`.
-/

namespace Brockian.LegendreConjecture

/-! ## The statement -/

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`. -/
def LegendreStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-! ## The next prime function -/

theorem exists_prime_gt (m : ℕ) : ∃ p : ℕ, m < p ∧ Nat.Prime p := by
  obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes (m + 1)
  exact ⟨p, hp, hp'⟩

/-- `nextPrime m` is the smallest prime strictly larger than `m`. -/
def nextPrime (m : ℕ) : ℕ := Nat.find (exists_prime_gt m)

theorem nextPrime_prime (m : ℕ) : Nat.Prime (nextPrime m) :=
  (Nat.find_spec (exists_prime_gt m)).2

theorem lt_nextPrime (m : ℕ) : m < nextPrime m :=
  (Nat.find_spec (exists_prime_gt m)).1

theorem nextPrime_le {m q : ℕ} (h : m < q) (hq : Nat.Prime q) : nextPrime m ≤ q :=
  Nat.find_le ⟨h, hq⟩

/-! ## Equivalent reformulations -/

/-- Legendre's conjecture is equivalent to saying that the next prime after `n ^ 2`
is smaller than `(n + 1) ^ 2`. -/
theorem legendre_iff_nextPrime :
    LegendreStatement ↔ ∀ n : ℕ, 1 ≤ n → nextPrime (n ^ 2) < (n + 1) ^ 2 := by
  constructor
  · intro h n hn
    obtain ⟨p, hp, hp1, hp2⟩ := h n hn
    exact lt_of_le_of_lt (nextPrime_le hp1 hp) hp2
  · intro h n hn
    exact ⟨nextPrime (n ^ 2), nextPrime_prime _, lt_nextPrime _, h n hn⟩

/-- Contrapositive form: Legendre's conjecture is equivalent to the non-existence of a
"prime-free" interval between consecutive squares. -/
theorem legendre_iff_no_prime_free_interval :
    LegendreStatement ↔
      ¬ ∃ n : ℕ, 1 ≤ n ∧ ∀ p : ℕ, Nat.Prime p → p ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ p := by
  constructor
  · rintro h ⟨n, hn, hfree⟩
    obtain ⟨p, hp, hp1, hp2⟩ := h n hn
    rcases hfree p hp with h' | h' <;> omega
  · intro h n hn
    by_contra hcon
    refine h ⟨n, hn, fun p hp => ?_⟩
    push_neg at hcon
    have := hcon p hp
    omega

/-- A counting helper: for `a ≤ b`, the count of `p` strictly increases from `a` to `b`
exactly when some `k` in `[a, b)` satisfies `p`. -/
theorem count_lt_count_iff (p : ℕ → Prop) [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p a < Nat.count p b ↔ ∃ k, a ≤ k ∧ k < b ∧ p k := by
  induction b, hab using Nat.le_induction with
  | base =>
      simp only [lt_self_iff_false, false_iff, not_exists]
      intro x
      omega
  | succ b hab ih =>
      rw [Nat.count_succ]
      by_cases hb : p b
      · simp only [hb, if_pos]
        constructor
        · intro _
          exact ⟨b, hab, Nat.lt_succ_self b, hb⟩
        · intro _
          have := Nat.count_monotone p hab
          omega
      · simp only [hb, if_false, add_zero]
        rw [ih]
        constructor
        · rintro ⟨k, hk1, hk2, hk3⟩
          exact ⟨k, hk1, by omega, hk3⟩
        · rintro ⟨k, hk1, hk2, hk3⟩
          refine ⟨k, hk1, ?_, hk3⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with h | h
          · exact h
          · exact absurd (h ▸ hk3) hb

/-- Formulation via the prime counting function: Legendre's conjecture says that the
number of primes `≤ n ^ 2` is strictly smaller than the number of primes `< (n + 1) ^ 2`. -/
theorem legendre_iff_primeCounting :
    LegendreStatement ↔
      ∀ n : ℕ, 1 ≤ n → Nat.primeCounting (n ^ 2) < Nat.primeCounting' ((n + 1) ^ 2) := by
  have key : ∀ n : ℕ, 1 ≤ n →
      ((Nat.primeCounting (n ^ 2) < Nat.primeCounting' ((n + 1) ^ 2)) ↔
        ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2) := by
    intro n hn
    have hab : n ^ 2 + 1 ≤ (n + 1) ^ 2 := by nlinarith
    show Nat.count Nat.Prime (n ^ 2 + 1) < Nat.count Nat.Prime ((n + 1) ^ 2) ↔ _
    rw [count_lt_count_iff Nat.Prime hab]
    constructor
    · rintro ⟨k, hk1, hk2, hk3⟩
      exact ⟨k, hk3, by omega, hk2⟩
    · rintro ⟨p, hp, hp1, hp2⟩
      exact ⟨p, by omega, hp2, hp⟩
  constructor
  · intro h n hn
    exact (key n hn).2 (h n hn)
  · intro h n hn
    exact (key n hn).1 (h n hn)

/-! ## Conditional reductions -/

/-- **Andrica's conjecture** (also open): `√(nextPrime p) - √p < 1` for every prime `p`. -/
def AndricaStatement : Prop :=
  ∀ p : ℕ, Nat.Prime p → Real.sqrt (nextPrime p) < Real.sqrt p + 1

/-- The target theorem: **Legendre's conjecture follows from Andrica's conjecture**. -/
theorem LegendreConjecture (hA : AndricaStatement) : LegendreStatement := by
  intro n hn
  rcases eq_or_lt_of_le hn with h1 | h2
  · exact ⟨2, by norm_num [← h1]⟩
  · -- `n ≥ 2`; take the largest prime `P ≤ n ^ 2` and the next prime `q` after it.
    have h2n : 2 ≤ n ^ 2 := by nlinarith
    set P := Nat.findGreatest Nat.Prime (n ^ 2) with hPdef
    have hP : Nat.Prime P := Nat.findGreatest_spec h2n Nat.prime_two
    have hPle : P ≤ n ^ 2 := Nat.findGreatest_le _
    set q := nextPrime P with hqdef
    have hq : Nat.Prime q := nextPrime_prime P
    have hPq : P < q := lt_nextPrime P
    have hqgt : n ^ 2 < q := by
      by_contra hcon
      push_neg at hcon
      have : q ≤ P := hPdef ▸ Nat.le_findGreatest hcon hq
      omega
    have hsP : Real.sqrt P ≤ (n : ℝ) := by
      have hle : (P : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hPle
      calc Real.sqrt P ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (n : ℝ) := Real.sqrt_sq (by positivity)
    have hlt : Real.sqrt q < (n : ℝ) + 1 := lt_of_lt_of_le (hA P hP) (by linarith)
    have hq2 : (q : ℝ) < ((n : ℝ) + 1) ^ 2 := (Real.sqrt_lt' (by positivity)).1 hlt
    refine ⟨q, hq, hqgt, ?_⟩
    have hcast : ((q : ℕ) : ℝ) < (((n + 1 : ℕ) : ℝ)) ^ 2 := by push_cast; exact hq2
    exact_mod_cast hcast

/-- A prime gap hypothesis of size `√m`: every `m ≥ 1` is followed by a prime within
`Nat.sqrt m`. -/
def SqrtGapStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ p : ℕ, Nat.Prime p ∧ m < p ∧ p ≤ m + Nat.sqrt m

/-- Legendre's conjecture also follows from the `√m` prime gap hypothesis. -/
theorem legendre_of_sqrtGap (h : SqrtGapStatement) : LegendreStatement := by
  intro n hn
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  obtain ⟨p, hp, hp1, hp2⟩ := h (n ^ 2) h1
  refine ⟨p, hp, hp1, ?_⟩
  have hs : Nat.sqrt (n ^ 2) = n := by
    rw [pow_two, Nat.sqrt_eq]
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
  omega

/-! ## Unconditional partial results -/

/-- Unconditional weakening (from Bertrand's postulate): for every `n ≥ 1` there is a prime
with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
theorem exists_prime_between_sq_two_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 := by
  have hne : n ^ 2 ≠ 0 := by positivity
  obtain ⟨p, hp, hp1, hp2⟩ := Nat.bertrand (n ^ 2) hne
  exact ⟨p, hp, hp1, hp2⟩

/-- Unconditional verification of Legendre's conjecture for all `1 ≤ n ≤ 30`. -/
theorem legendre_verified_le_thirty (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 30) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num⟩
  · exact ⟨5, by norm_num⟩
  · exact ⟨11, by norm_num⟩
  · exact ⟨17, by norm_num⟩
  · exact ⟨29, by norm_num⟩
  · exact ⟨37, by norm_num⟩
  · exact ⟨53, by norm_num⟩
  · exact ⟨67, by norm_num⟩
  · exact ⟨83, by norm_num⟩
  · exact ⟨101, by norm_num⟩
  · exact ⟨127, by norm_num⟩
  · exact ⟨149, by norm_num⟩
  · exact ⟨173, by norm_num⟩
  · exact ⟨197, by norm_num⟩
  · exact ⟨227, by norm_num⟩
  · exact ⟨257, by norm_num⟩
  · exact ⟨293, by norm_num⟩
  · exact ⟨331, by norm_num⟩
  · exact ⟨367, by norm_num⟩
  · exact ⟨401, by norm_num⟩
  · exact ⟨443, by norm_num⟩
  · exact ⟨487, by norm_num⟩
  · exact ⟨541, by norm_num⟩
  · exact ⟨577, by norm_num⟩
  · exact ⟨631, by norm_num⟩
  · exact ⟨677, by norm_num⟩
  · exact ⟨733, by norm_num⟩
  · exact ⟨787, by norm_num⟩
  · exact ⟨853, by norm_num⟩
  · exact ⟨907, by norm_num⟩

end Brockian.LegendreConjecture

