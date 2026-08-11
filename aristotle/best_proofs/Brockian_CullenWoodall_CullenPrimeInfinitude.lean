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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires all `import` commands to appear before any
other command, including module docstrings, so the mandated header comment above
is placed immediately after the single `import Mathlib` line.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th **Cullen number** `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The set of indices `n` for which the Cullen number `C n` is prime. -/
def cullenPrimeIndices : Set ℕ := {n : ℕ | Nat.Prime (cullen n)}

/-- `C 1 = 3` is prime, so the set of Cullen prime indices is nonempty. -/
theorem one_mem_cullenPrimeIndices : 1 ∈ cullenPrimeIndices := by
  simp only [cullenPrimeIndices, Set.mem_setOf_eq, cullen]
  norm_num

/-- `C 2 = 9` is not prime. -/
theorem two_not_mem_cullenPrimeIndices : 2 ∉ cullenPrimeIndices := by
  simp only [cullenPrimeIndices, Set.mem_setOf_eq, cullen]
  decide

/-!
## The statement

Whether there are infinitely many Cullen primes is a well-known open problem, so the
theorem `CullenPrimeInfinitude` below is stated as a *conditional reduction*: from the
hypothesis that Cullen primes occur beyond every bound one obtains the infinitude of
the set of Cullen prime indices.  The converse implication is
`cullenPrimeIndices_unbounded_of_infinite`, so the two formulations are provably
equivalent (`cullenPrimeIndices_infinite_iff`).

Unconditionally we prove that composite Cullen numbers occur beyond every bound: for
every odd prime `p` we have `p ∣ C (p - 1)` and `C (p - 1) > p`, hence `C (p - 1)` is
composite (`not_prime_cullen_prime_sub_one`, `infinite_cullen_composite_indices`).
-/

/-- **Conditional reduction for the Cullen prime infinitude conjecture.**
If Cullen primes occur beyond every bound, then the set of indices `n` such that
`n * 2 ^ n + 1` is prime is infinite. -/
theorem CullenPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (cullen n)) :
    cullenPrimeIndices.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨n, hn, hp⟩ := h a
  exact ⟨n, hp, hn⟩

/-- Converse of `CullenPrimeInfinitude`. -/
theorem cullenPrimeIndices_unbounded_of_infinite (h : cullenPrimeIndices.Infinite) :
    ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (cullen n) := by
  intro N
  obtain ⟨n, hn, hgt⟩ := h.exists_gt N
  exact ⟨n, hgt, hn⟩

/-- The two formulations of the conjecture agree. -/
theorem cullenPrimeIndices_infinite_iff :
    cullenPrimeIndices.Infinite ↔ ∀ N : ℕ, ∃ n, N < n ∧ Nat.Prime (cullen n) :=
  ⟨cullenPrimeIndices_unbounded_of_infinite, CullenPrimeInfinitude⟩

/-- For `1 ≤ n` the Cullen number `C n` is at least `3`. -/
theorem three_le_cullen {n : ℕ} (hn : 1 ≤ n) : 3 ≤ cullen n := by
  have h2 : 2 ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have : 1 * 2 ≤ n * 2 ^ n := Nat.mul_le_mul hn (by simpa using h2)
  simp only [cullen]
  omega

/-- A trial-division criterion: if no prime `q` with `q ^ 2 ≤ C n` divides `C n`,
then `C n` is prime. -/
theorem prime_cullen_of_no_small_prime_factor {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ q : ℕ, q.Prime → q ^ 2 ≤ cullen n → ¬ q ∣ cullen n) :
    Nat.Prime (cullen n) := by
  by_contra hnp
  have h3 := three_le_cullen hn
  have hq : Nat.Prime (cullen n).minFac := Nat.minFac_prime (by omega)
  exact h _ hq (Nat.minFac_sq_le_self (by omega) hnp) (Nat.minFac_dvd _)

/-- **A trial-division form of the conditional reduction.** If, beyond every bound,
there is an index `n` such that no prime `q` with `q ^ 2 ≤ C n` divides `C n`, then
there are infinitely many Cullen primes. -/
theorem CullenPrimeInfinitude_of_no_small_prime_factor
    (h : ∀ N : ℕ, ∃ n, N < n ∧ ∀ q : ℕ, q.Prime → q ^ 2 ≤ cullen n → ¬ q ∣ cullen n) :
    cullenPrimeIndices.Infinite := by
  refine CullenPrimeInfinitude fun N => ?_
  obtain ⟨n, hn, hq⟩ := h N
  exact ⟨n, hn, prime_cullen_of_no_small_prime_factor (by omega) hq⟩

/-!
## Unconditional partial results: infinitely many composite Cullen numbers
-/

/-- For an odd prime `p`, Fermat's little theorem gives `p ∣ C (p - 1)`,
since `C (p - 1) ≡ (-1) * 1 + 1 = 0 [MOD p]`. -/
theorem dvd_cullen_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ cullen (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : 1 ≤ p := hp.one_lt.le
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have hferm : ((2 : ℕ) : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2
  rw [← ZMod.natCast_eq_zero_iff]
  have hcast : ((cullen (p - 1) : ℕ) : ZMod p)
      = (((p : ℕ) : ZMod p) - 1) * ((2 : ℕ) : ZMod p) ^ (p - 1) + 1 := by
    simp only [cullen, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one,
      Nat.cast_sub h1]
  rw [hcast, hferm, ZMod.natCast_self]
  ring

/-- For an odd prime `p`, the Cullen number `C (p - 1)` is strictly larger than `p`. -/
theorem lt_cullen_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p < cullen (p - 1) := by
  have h3 : 3 ≤ p := by
    have h2 := hp.two_le
    rcases Nat.lt_or_ge p 3 with h | h
    · interval_cases p
      · omega
    · exact h
  have hpow : 2 ^ 2 ≤ 2 ^ (p - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmul : (p - 1) * 4 ≤ (p - 1) * 2 ^ (p - 1) := Nat.mul_le_mul_left _ (by omega)
  simp only [cullen]
  omega

/-- For an odd prime `p`, the Cullen number `C (p - 1)` is composite. -/
theorem not_prime_cullen_prime_sub_one {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ Nat.Prime (cullen (p - 1)) := by
  intro hprime
  have hdvd := dvd_cullen_sub_one hp hp2
  have heq := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
  exact absurd heq (Nat.ne_of_lt (lt_cullen_sub_one hp hp2))

/-- **Unconditional partial result.** There are infinitely many `n` for which the
Cullen number `n * 2 ^ n + 1` is *not* prime. -/
theorem infinite_cullen_composite_indices :
    {n : ℕ | ¬ Nat.Prime (cullen n)}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (a + 3)
  have hp2 : p ≠ 2 := by omega
  exact ⟨p - 1, not_prime_cullen_prime_sub_one hp hp2, by omega⟩

end Brockian.CullenWoodall

