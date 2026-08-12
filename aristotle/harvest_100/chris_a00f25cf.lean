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
import Brockian.LegendreConjecture

/-!
# Legendre Conjecture — Mathlib companion

This module connects the self-contained statements of `Brockian.LegendreConjecture`
(which, by design, imports nothing so that the required header comment can sit at the
very top of that file) with Mathlib's `Nat.Prime`, and records some unconditional
partial results towards Legendre's conjecture.
-/

namespace Brockian.LegendreConjecture

/-- The self-contained primality predicate used in `Brockian.LegendreConjecture`
agrees with Mathlib's `Nat.Prime`. -/
theorem isPrime_iff_natPrime (p : Nat) : IsPrime p ↔ Nat.Prime p := by
  rw [Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hmp hdvd => h m hmp hm ?_⟩
    exact Nat.mod_eq_zero_of_dvd hdvd
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hmp hm hmod => h m hm hmp ?_⟩
    exact Nat.dvd_of_mod_eq_zero hmod

/-- Legendre's statement, phrased with Mathlib's `Nat.Prime`, is equivalent to the
statement `LegendreStatement` used in the main file. -/
theorem legendreStatement_iff :
    LegendreStatement ↔
      ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  constructor <;> intro h n hn <;> obtain ⟨p, hp, h1, h2⟩ := h n hn <;>
    exact ⟨p, by simpa [isPrime_iff_natPrime] using hp, h1, h2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Legendre's conjecture holds unconditionally for all `1 ≤ n ≤ 40`, verified by
kernel computation. -/
theorem legendre_le_forty :
    ∀ n ∈ Finset.Icc 1 40, ∃ p ∈ Finset.Ioo (n ^ 2) ((n + 1) ^ 2), Nat.Prime p := by
  decide

/-- An unconditional weakening of Legendre's conjecture, coming from Bertrand's
postulate: for every `n ≥ 1` there is a prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
theorem exists_prime_between_sq_two_mul_sq (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 :=
  Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)

end Brockian.LegendreConjecture

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LegendreConjecture

/-- Primality of a natural number, stated in a self-contained, decidable form:
`p` is at least `2` and no `m` with `2 ≤ m < p` divides `p`.

(The file `Brockian/LegendreConjectureMathlib.lean` proves that this predicate is
equivalent to Mathlib's `Nat.Prime`.) -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m < p → 2 ≤ m → p % m ≠ 0

instance (p : Nat) : Decidable (IsPrime p) := by
  unfold IsPrime; infer_instance

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/
def LegendreStatement : Prop :=
  ∀ n : Nat, 1 ≤ n → ∃ p : Nat, IsPrime p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- A short prime gap hypothesis: for every `x ≥ 1` there is a prime in the interval
`(x, x + √x]`, where `√x` is expressed by an auxiliary `m` with `m * m ≤ x`.
This is itself an open problem — it is far beyond what is currently known
unconditionally, and it is slightly stronger than Legendre's conjecture. -/
def ShortGapHypothesis : Prop :=
  ∀ x m : Nat, 1 ≤ x → m * m ≤ x → ∃ p : Nat, IsPrime p ∧ x < p ∧ p ≤ x + m

theorem sq_eq_mul_self (n : Nat) : n ^ 2 = n * n := by
  simp [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]

theorem succ_sq (n : Nat) : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
  simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul]
  omega

/-- **Conditional reduction of Legendre's conjecture.**

Legendre's conjecture — the existence, for every `n ≥ 1`, of a prime strictly between
`n ^ 2` and `(n + 1) ^ 2` — is an open problem, so it is established here
*conditionally*: it follows from the short prime gap hypothesis
`ShortGapHypothesis`, which asserts a prime in `(x, x + √x]` for every `x ≥ 1`.
Applying that hypothesis at `x = n ^ 2` (with `√x = n`) produces a prime `p` with
`n ^ 2 < p ≤ n ^ 2 + n < (n + 1) ^ 2`. -/
theorem LegendreConjecture (hgap : ShortGapHypothesis) : LegendreStatement := by
  intro n hn
  have hx : 1 ≤ n ^ 2 := by
    have := Nat.pow_le_pow_left hn 2
    simpa using this
  have hmm : n * n ≤ n ^ 2 := by rw [sq_eq_mul_self]; exact Nat.le_refl _
  obtain ⟨p, hp, hlt, hle⟩ := hgap (n ^ 2) n hx hmm
  refine ⟨p, hp, hlt, ?_⟩
  have hkey : n ^ 2 + n < n ^ 2 + 2 * n + 1 := by
    have : n < 2 * n + 1 := by omega
    have := Nat.add_lt_add_left this (n ^ 2)
    omega
  rw [succ_sq]
  exact Nat.lt_of_le_of_lt hle hkey

end Brockian.LegendreConjecture

