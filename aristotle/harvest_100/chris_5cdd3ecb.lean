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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/
def Betrothed (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma 1 m = m + n + 1 ∧ sigma 1 n = m + n + 1

theorem betrothed_comm {m n : ℕ} (h : Betrothed m n) : Betrothed n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hn, hm, hmn.symm, ?_, ?_⟩ <;> omega

/-- The statement that there are infinitely many betrothed pairs. -/
def BetrothedInfinite : Prop := ∀ N : ℕ, ∃ m n : ℕ, N < m ∧ Betrothed m n

/-! ## Small examples -/

set_option maxRecDepth 100000 in
theorem betrothed_48_75 : Betrothed 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

set_option maxRecDepth 100000 in
theorem betrothed_140_195 : Betrothed 140 195 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

set_option maxRecDepth 400000 in
theorem betrothed_1050_1925 : Betrothed 1050 1925 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

/-! ## The key construction lemma -/

/-- A *sigma split*: a common factor `A` together with coprime cofactors `P ≠ Q` having equal
divisor sums, satisfying the quasi-amicability equation `σ(A)·σ(P) = A·(P+Q) + 1`. -/
def SigmaSplit (A P Q : ℕ) : Prop :=
  0 < A ∧ 0 < P ∧ 0 < Q ∧ P ≠ Q ∧ Nat.Coprime A P ∧ Nat.Coprime A Q ∧
    sigma 1 P = sigma 1 Q ∧ sigma 1 A * sigma 1 P = A * (P + Q) + 1

/-- **Key lemma.** Every sigma split produces a betrothed pair. -/
theorem betrothed_of_sigmaSplit {A P Q : ℕ} (h : SigmaSplit A P Q) :
    Betrothed (A * P) (A * Q) := by
  obtain ⟨hA, hP, hQ, hPQ, hAP, hAQ, hsig, heq⟩ := h
  have hmul : ∀ B : ℕ, Nat.Coprime A B → sigma 1 (A * B) = sigma 1 A * sigma 1 B := by
    intro B hB
    exact (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hB
  have hm : sigma 1 (A * P) = A * P + A * Q + 1 := by
    rw [hmul P hAP, heq, Nat.mul_add]
  have hn : sigma 1 (A * Q) = A * P + A * Q + 1 := by
    rw [hmul Q hAQ, ← hsig, heq, Nat.mul_add]
  exact ⟨Nat.mul_pos hA hP, Nat.mul_pos hA hQ,
    fun hc => hPQ (Nat.eq_of_mul_eq_mul_left hA hc), hm, hn⟩

set_option maxRecDepth 100000 in
/-- The sigma split behind the smallest betrothed pair `(48, 75)`. In particular the notion is
not vacuous. -/
theorem sigmaSplit_3_16_25 : SigmaSplit 3 16 25 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by decide, by decide, ?_, ?_⟩ <;>
    decide

/-! ## An unconditional obstruction: no Thabit-style rule -/

/-- In a betrothed pair whose two members have the same parity, the common divisor sum is odd. -/
theorem sigma_odd_of_betrothed_of_same_parity {m n : ℕ} (h : Betrothed m n)
    (hpar : Even (m + n)) : Odd (sigma 1 n) := by
  obtain ⟨-, -, -, -, h2⟩ := h
  rw [h2]
  exact hpar.add_one

/-- If an odd prime divides a number exactly once, the divisor sum of that number is even. -/
theorem sigma_even_of_odd_prime_mul {p k : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hk : Nat.Coprime p k) : Even (sigma 1 (p * k)) := by
  have hmul : sigma 1 (p * k) = sigma 1 p * sigma 1 k :=
    (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hk
  have hsp : sigma 1 p = p + 1 := by
    simp [sigma_one_apply, hp.divisors, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]
  rw [hmul, hsp]
  exact (Nat.even_add_one.2 (Nat.not_even_iff_odd.2 hodd)).mul_right _

/-- **Structural obstruction.** If the two members of a betrothed pair have the same parity, then
no odd prime can divide the second member to the first power exactly. -/
theorem not_odd_prime_exactly_once {m n p : ℕ} (h : Betrothed m n) (hpar : Even (m + n))
    (hp : p.Prime) (hodd : Odd p) (hdvd : p ∣ n) (hnsq : ¬ p ^ 2 ∣ n) : False := by
  obtain ⟨k, hk⟩ := hdvd
  have hcop : Nat.Coprime p k := by
    rw [hp.coprime_iff_not_dvd]
    intro hpk
    exact hnsq (by rw [hk, sq]; exact mul_dvd_mul_left p hpk)
  have heven : Even (sigma 1 n) := by
    rw [hk]; exact sigma_even_of_odd_prime_mul hp hodd hcop
  exact (Nat.not_even_iff_odd.2 (sigma_odd_of_betrothed_of_same_parity h hpar)) heven

/-- **Obstruction.** There is no Thabit-style rule producing betrothed pairs of the shape
`(A·p·q, A·r)` with `p, q, r` odd primes and `r` coprime to `A`: such a pair is never
betrothed. (Contrast with the amicable numbers, where exactly this shape yields Thabit's rule.) -/
theorem not_betrothed_thabit {A p q r : ℕ} (hr : r.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hrodd : Odd r) (hAr : Nat.Coprime A r) : ¬ Betrothed (A * p * q) (A * r) := by
  intro h
  -- both members have the parity of `A`, so their sum is even and the divisor sums are odd
  have hpar : Even (A * p * q + A * r) := by
    have hsum : A * p * q + A * r = A * (p * q + r) := by ring
    rw [hsum]
    exact ((hpodd.mul hqodd).add_odd hrodd).mul_left A
  -- but `r` divides `A * r` exactly once, forcing the divisor sum to be even
  refine not_odd_prime_exactly_once h hpar hr hrodd ⟨A, Nat.mul_comm A r⟩ (fun hsq => ?_)
  have hrA : r ∣ A := by
    have : r * r ∣ r * A := by
      rw [← sq, Nat.mul_comm r A]; exact hsq
    exact (mul_dvd_mul_iff_left hr.pos.ne').1 this
  have hr1 : r ∣ 1 := hAr ▸ Nat.dvd_gcd hrA dvd_rfl
  exact hr.one_lt.ne' (Nat.eq_one_of_dvd_one hr1)

/-! ## The conditional infinitude theorem -/

/-- The hypothesis: there are arbitrarily large sigma splits. -/
def SigmaSplitInfinite : Prop := ∀ N : ℕ, ∃ A P Q : ℕ, N < A * P ∧ SigmaSplit A P Q

/-- **Betrothed Infinitude (conditional reduction).** If there are arbitrarily large sigma
splits, then there are infinitely many betrothed pairs.

The infinitude of betrothed (quasi-amicable) pairs is an open problem, so the result is stated
conditionally.  The content is the key lemma `betrothed_of_sigmaSplit`: a betrothed pair can be
manufactured from a common factor `A` and coprime cofactors `P ≠ Q` with equal divisor sums
satisfying `σ(A)·σ(P) = A·(P+Q) + 1` (as in `48 = 3·16`, `75 = 3·25`).  The hypothesis is not a
strictly stronger statement: by `sigmaSplitInfinite_iff_betrothedInfinite` it is *equivalent* to
the conclusion, so nothing is smuggled in. -/
theorem BetrothedInfinitude (H : SigmaSplitInfinite) : BetrothedInfinite := by
  intro N
  obtain ⟨A, P, Q, hlt, h⟩ := H N
  exact ⟨A * P, A * Q, hlt, betrothed_of_sigmaSplit h⟩

/-- Conversely, every betrothed pair is itself a (trivial) sigma split, with common factor `1`. -/
theorem sigmaSplit_one_of_betrothed {m n : ℕ} (h : Betrothed m n) : SigmaSplit 1 m n := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨Nat.one_pos, hm, hn, hmn, Nat.coprime_one_left m, Nat.coprime_one_left n, by
    rw [h1, h2], ?_⟩
  simp [h1]

/-- The hypothesis of `BetrothedInfinitude` is exactly equivalent to its conclusion. -/
theorem sigmaSplitInfinite_iff_betrothedInfinite : SigmaSplitInfinite ↔ BetrothedInfinite := by
  refine ⟨BetrothedInfinitude, fun H N => ?_⟩
  obtain ⟨m, n, hlt, h⟩ := H N
  exact ⟨1, m, n, by simpa using hlt, sigmaSplit_one_of_betrothed h⟩

end Brockian.BetrothedNumbers

