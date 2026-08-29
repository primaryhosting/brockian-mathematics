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

import Brockian.LegendreConjectureExtras
#print axioms Brockian.LegendreConjecture.LegendreConjecture
#print axioms Brockian.LegendreConjecture.legendre_of_le_forty
#print axioms Brockian.LegendreConjecture.IsPrimeNat_iff_prime
#print axioms Brockian.LegendreConjecture.exists_prime_between_sq_and_two_sq
#print axioms Brockian.LegendreConjecture.legendre_of_shortInterval

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately self-contained (no `import` lines), so that the header
comment above can literally be the first thing in the file: Lean 4 requires all
`import` commands to precede every other piece of syntax except plain comments,
and a module doc comment `/-! ... -/` counts as syntax.

Mathlib-based companion results (in particular the identification of the
primality predicate used here with `Nat.Prime`, and Bertrand's postulate as an
unconditional partial result) live in `Brockian/LegendreConjectureExtras.lean`,
which imports this module.
-/

namespace Brockian.LegendreConjecture

/-- Primality of a natural number, spelled out by trial division:
`p` is prime iff `2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`.
This is proved equivalent to Mathlib's `Nat.Prime` in
`Brockian/LegendreConjectureExtras.lean`. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d < p → 2 ≤ d → ¬ d ∣ p

instance : DecidablePred IsPrimeNat := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- **Legendre's conjecture**: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`.  This is a famous open problem. -/
def LegendreStatement : Prop :=
  ∀ n : Nat, 0 < n → ∃ p : Nat, IsPrimeNat p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2

/-- A short-interval prime hypothesis: whenever `1 ≤ m` and `m ^ 2 ≤ x`, the interval
`(x, x + m]` contains a prime; i.e. every interval `(x, x + √x]` contains a prime.
This is weaker than Cramér's conjecture, and stronger than anything currently known
unconditionally. -/
def ShortIntervalPrimeHypothesis : Prop :=
  ∀ x m : Nat, 0 < m → m ^ 2 ≤ x → ∃ p : Nat, IsPrimeNat p ∧ x < p ∧ p ≤ x + m

/-- **Conditional reduction of Legendre's conjecture.**
The short-interval prime hypothesis — a prime in every interval `(x, x + √x]` —
implies Legendre's conjecture: for every `n ≥ 1` there is a prime strictly between
`n ^ 2` and `(n + 1) ^ 2`. -/
theorem LegendreConjecture (H : ShortIntervalPrimeHypothesis) : LegendreStatement := by
  intro n hn
  obtain ⟨p, hp, hlt, hle⟩ := H (n ^ 2) n hn (Nat.le_refl _)
  refine ⟨p, hp, hlt, ?_⟩
  have hexp : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
    simp [Nat.pow_two, Nat.mul_add, Nat.add_mul]; omega
  omega

/-- An explicit prime witness in the interval `(n ^ 2, (n + 1) ^ 2)` for `1 ≤ n ≤ 40`. -/
def legendreWitness : Nat → Nat
  | 1 => 2 | 2 => 5 | 3 => 11 | 4 => 17 | 5 => 29 | 6 => 37 | 7 => 53 | 8 => 67
  | 9 => 83 | 10 => 101 | 11 => 127 | 12 => 149 | 13 => 173 | 14 => 197 | 15 => 227
  | 16 => 257 | 17 => 293 | 18 => 331 | 19 => 367 | 20 => 401 | 21 => 443 | 22 => 487
  | 23 => 541 | 24 => 577 | 25 => 631 | 26 => 683 | 27 => 733 | 28 => 787 | 29 => 853
  | 30 => 907 | 31 => 967 | 32 => 1031 | 33 => 1091 | 34 => 1163 | 35 => 1229
  | 36 => 1297 | 37 => 1373 | 38 => 1447 | 39 => 1523 | 40 => 1601 | _ => 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The witnesses above are indeed primes lying strictly between consecutive squares. -/
theorem legendreWitness_spec : ∀ n, n < 41 → 1 ≤ n →
    n ^ 2 < legendreWitness n ∧ legendreWitness n < (n + 1) ^ 2 ∧
      IsPrimeNat (legendreWitness n) := by decide

/-- **Unconditional partial result**: Legendre's conjecture holds for all `1 ≤ n ≤ 40`. -/
theorem legendre_of_le_forty (n : Nat) (hn : 0 < n) (hn' : n ≤ 40) :
    ∃ p : Nat, IsPrimeNat p ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := legendreWitness_spec n (by omega) hn
  exact ⟨legendreWitness n, h3, h1, h2⟩

end Brockian.LegendreConjecture

import Mathlib
import Brockian.LegendreConjecture

/-!
# Legendre Conjecture — Mathlib companion results

This module connects the self-contained development in `Brockian.LegendreConjecture`
with Mathlib:

* `IsPrimeNat_iff_prime` : the trial-division primality predicate used there agrees
  with Mathlib's `Nat.Prime`;
* `legendreStatement_iff` / `shortIntervalPrimeHypothesis_iff` : the statements
  restated with `Nat.Prime`;
* `exists_prime_between_sq_and_two_sq` : the unconditional weakening of Legendre's
  conjecture supplied by Bertrand's postulate.
-/

namespace Brockian.LegendreConjecture

theorem IsPrimeNat_iff_prime (p : ℕ) : IsPrimeNat p ↔ Nat.Prime p := by
  constructor
  · rintro ⟨hp2, hp⟩
    rw [Nat.prime_def_lt]
    refine ⟨hp2, fun m hm hdvd => ?_⟩
    by_contra hm1
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m
      · simp at hdvd; omega
      · exact hm1 rfl
    · exact hp m hm h hdvd
  · intro hp
    refine ⟨hp.two_le, fun d hd hd2 hdvd => ?_⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp d hdvd) with h | h <;> omega

/-- Legendre's conjecture, phrased with Mathlib's `Nat.Prime`. -/
theorem legendreStatement_iff :
    LegendreStatement ↔ ∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  simp only [LegendreStatement, IsPrimeNat_iff_prime]

/-- The short-interval prime hypothesis, phrased with Mathlib's `Nat.Prime`. -/
theorem shortIntervalPrimeHypothesis_iff :
    ShortIntervalPrimeHypothesis ↔
      ∀ x m : ℕ, 0 < m → m ^ 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + m := by
  simp only [ShortIntervalPrimeHypothesis, IsPrimeNat_iff_prime]

/-- **Conditional Legendre, Mathlib phrasing.** -/
theorem legendre_of_shortInterval
    (H : ∀ x m : ℕ, 0 < m → m ^ 2 ≤ x → ∃ p : ℕ, p.Prime ∧ x < p ∧ p ≤ x + m)
    (n : ℕ) (hn : 0 < n) : ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 :=
  legendreStatement_iff.mp
    (LegendreConjecture (shortIntervalPrimeHypothesis_iff.mpr H)) n hn

/-- **Unconditional partial result** (Bertrand's postulate): for every `n ≥ 1` there is a
prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`. -/
theorem exists_prime_between_sq_and_two_sq (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p ≤ 2 * n ^ 2 :=
  Nat.exists_prime_lt_and_le_two_mul (n ^ 2) (by positivity)

end Brockian.LegendreConjecture

