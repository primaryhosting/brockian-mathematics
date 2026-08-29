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
import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Legendre's conjecture — that for every `n ≥ 1` there is a prime strictly between `n ^ 2` and
`(n + 1) ^ 2` — is a well-known open problem.  This file therefore contains:

* `Brockian.LegendreConjecture.LegendreStatement`, the formal statement of the conjecture;
* several *equivalent* reformulations (contrapositive form, a counting form using
  `Finset` cardinalities, and a form using the prime counting function `π`);
* `Brockian.LegendreConjecture.LegendreConjecture`, a Lean-checked **conditional reduction**:
  Legendre's conjecture follows from the (also open, but formally weaker-looking) statement
  that every interval `(m, m + √m]` contains a prime;
* `Brockian.LegendreConjecture.legendre_of_le_hundred`, an unconditional verification of the
  conjecture for all `1 ≤ n ≤ 100`.
-/

namespace Brockian.LegendreConjecture

open Finset

/-- The statement of Legendre's conjecture: for every `n ≥ 1` there is a prime `p` with
`n ^ 2 < p < (n + 1) ^ 2`. -/
def LegendreStatement : Prop :=
  ∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- The statement that every interval `(m, m + √m]` with `m ≥ 1` contains a prime.  This is a
short-interval prime-gap hypothesis; it is open, but it implies Legendre's conjecture (see
`LegendreConjecture`). -/
def PrimeInSqrtInterval : Prop :=
  ∀ m : ℕ, 0 < m → ∃ p : ℕ, p.Prime ∧ m < p ∧ p ≤ m + Nat.sqrt m

/-- A perfect square `m ^ 2` with `2 ≤ m` is never prime. -/
theorem not_prime_sq {m : ℕ} (hm : 2 ≤ m) : ¬ (m ^ 2).Prime := by
  rw [pow_two]
  exact Nat.not_prime_mul (by omega) (by omega)

/-- Contrapositive / "no prime-free square interval" form of Legendre's conjecture. -/
theorem legendre_iff_no_prime_free_interval :
    LegendreStatement ↔ ¬ ∃ n : ℕ, 0 < n ∧ ∀ p : ℕ, p.Prime → ¬ (n ^ 2 < p ∧ p < (n + 1) ^ 2) := by
  constructor
  · rintro h ⟨n, hn, hno⟩
    obtain ⟨p, hp, h1, h2⟩ := h n hn
    exact hno p hp ⟨h1, h2⟩
  · intro h n hn
    by_contra hc
    exact h ⟨n, hn, by
      intro p hp ⟨h1, h2⟩
      exact hc ⟨p, hp, h1, h2⟩⟩

/-- Counting form of Legendre's conjecture: each interval `(n ^ 2, (n + 1) ^ 2)` contains a
positive number of primes. -/
theorem legendre_iff_card_pos :
    LegendreStatement ↔
      ∀ n : ℕ, 0 < n → 0 < #{p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2) | p.Prime} := by
  constructor
  · intro h n hn
    obtain ⟨p, hp, h1, h2⟩ := h n hn
    exact Finset.card_pos.2 ⟨p, by simp [Finset.mem_filter, Finset.mem_Ioo, hp, h1, h2]⟩
  · intro h n hn
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (h n hn)
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hp
    exact ⟨p, hp.2, hp.1.1, hp.1.2⟩

/-- Splitting the counting function `Nat.count` over an initial segment. -/
theorem count_eq_count_add_card {p : ℕ → Prop} [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p b = Nat.count p a + #{k ∈ Finset.Ico a b | p k} := by
  rw [Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range, Finset.range_eq_Ico,
    ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) hab,
    Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter
    (Finset.Ico_disjoint_Ico_consecutive 0 a b)

/-- Strict growth of `Nat.count` between two points is equivalent to the existence of a witness
in the corresponding half-open interval. -/
theorem count_lt_count_iff {p : ℕ → Prop} [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p a < Nat.count p b ↔ ∃ k, a ≤ k ∧ k < b ∧ p k := by
  rw [count_eq_count_add_card hab]
  constructor
  · intro h
    have : 0 < #{k ∈ Finset.Ico a b | p k} := by omega
    obtain ⟨k, hk⟩ := Finset.card_pos.1 this
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk
    exact ⟨k, hk.1.1, hk.1.2, hk.2⟩
  · rintro ⟨k, h1, h2, h3⟩
    have : 0 < #{k ∈ Finset.Ico a b | p k} :=
      Finset.card_pos.2 ⟨k, by simp [Finset.mem_filter, Finset.mem_Ico, h1, h2, h3]⟩
    omega

/-- Prime-counting form of Legendre's conjecture: `π (n ^ 2) < π ((n + 1) ^ 2)` for all `n ≥ 1`. -/
theorem legendre_iff_primeCounting :
    LegendreStatement ↔ ∀ n : ℕ, 0 < n → Nat.primeCounting (n ^ 2) < Nat.primeCounting ((n + 1) ^ 2) := by
  constructor
  · intro h n hn
    obtain ⟨p, hp, h1, h2⟩ := h n hn
    have hle : n ^ 2 + 1 ≤ (n + 1) ^ 2 + 1 := by nlinarith
    refine (count_lt_count_iff (p := Nat.Prime) hle).2 ⟨p, by omega, by omega, hp⟩
  · intro h n hn
    have hle : n ^ 2 + 1 ≤ (n + 1) ^ 2 + 1 := by nlinarith
    obtain ⟨k, h1, h2, h3⟩ := (count_lt_count_iff (p := Nat.Prime) hle).1 (h n hn)
    refine ⟨k, h3, by omega, ?_⟩
    rcases Nat.lt_or_ge k ((n + 1) ^ 2) with h | h
    · exact h
    · have hk : k = (n + 1) ^ 2 := by omega
      rw [hk] at h3
      exact absurd h3 (not_prime_sq (by omega))

/-- **Conditional reduction of Legendre's conjecture.**  Legendre's conjecture — a prime strictly
between consecutive squares — follows from the short-interval prime hypothesis
`PrimeInSqrtInterval`, which asserts a prime in `(m, m + √m]` for every `m ≥ 1`.

Legendre's conjecture itself is a well-known open problem, so this is a conditional statement. -/
theorem LegendreConjecture (h : PrimeInSqrtInterval) : LegendreStatement := by
  intro n hn
  have hm : 0 < n ^ 2 := by positivity
  obtain ⟨p, hp, h1, h2⟩ := h (n ^ 2) hm
  refine ⟨p, hp, h1, ?_⟩
  have hsqrt : Nat.sqrt (n ^ 2) = n := Nat.sqrt_eq' n
  rw [hsqrt] at h2
  nlinarith

/-- Unconditional verification of Legendre's conjecture for all `1 ≤ n ≤ 100`. -/
theorem legendre_of_le_hundred (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 100) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨53, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨149, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨173, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨197, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨227, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨257, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨293, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨331, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨367, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨401, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨443, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨487, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨541, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨577, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨631, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨677, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨787, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨853, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨907, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨967, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1031, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1091, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1163, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1297, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1373, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1447, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1523, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1601, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1693, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1777, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1861, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨1949, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2027, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2129, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2213, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2309, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2503, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2609, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2707, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2819, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨2917, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3037, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3137, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3251, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3371, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3491, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3607, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3727, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3847, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨3989, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4099, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4357, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4493, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4637, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4783, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨4903, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5051, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5189, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5333, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5477, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5639, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5779, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5939, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6089, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6247, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6421, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6563, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6733, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨6899, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7057, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7229, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7411, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7573, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7753, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨7927, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8287, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8467, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8663, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨8837, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9029, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9221, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9413, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9613, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨9803, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨10007, by norm_num, by norm_num, by norm_num⟩

/-- Unconditional weakening of Legendre's conjecture, from Bertrand's postulate: for every
`n ≥ 1` there is a prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
theorem prime_between_sq_and_two_sq (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 :=
  Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)

/-- Since Legendre's conjecture is verified for `n ≤ 100`, it is equivalent to its restriction
to `n ≥ 101`. -/
theorem legendre_iff_large :
    LegendreStatement ↔
      ∀ n : ℕ, 101 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  constructor
  · intro h n hn
    exact h n (by omega)
  · intro h n hn
    rcases Nat.lt_or_ge n 101 with hlt | hge
    · exact legendre_of_le_hundred n hn (by omega)
    · exact h n hge

end Brockian.LegendreConjecture

