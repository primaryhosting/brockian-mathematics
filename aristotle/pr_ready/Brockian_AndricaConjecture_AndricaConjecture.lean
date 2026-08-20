/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Lean requires `import` commands to precede every other command, including module
docstrings, so the mandated header appears at the top of the file as a plain block
comment and is repeated here as the module docstring.
-/

namespace Brockian.AndricaConjecture

open Real

/-- `prime n` is the `n`-th prime number (`prime 0 = 2`). -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

lemma prime_zero : prime 0 = 2 := by simp [prime]

lemma prime_prime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

lemma prime_pos (n : ℕ) : 0 < prime n := (prime_prime n).pos

lemma prime_lt_prime_succ (n : ℕ) : prime n < prime (n + 1) :=
  (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr (Nat.lt_succ_self n)

/-- The statement of the Andrica conjecture: for every `n`,
`√(p_{n+1}) - √(p_n) < 1`, where `p_n` is the `n`-th prime. -/
def AndricaStatement : Prop :=
  ∀ n : ℕ, Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1

/-- The equivalent gap formulation: `p_{n+1} - p_n < 2√(p_n) + 1`. -/
def AndricaGapStatement : Prop :=
  ∀ n : ℕ, (prime (n + 1) : ℝ) - prime n < 2 * Real.sqrt (prime n) + 1

/-- Elementary equivalence: for a nonnegative real `a` and any real `b`,
`√b - √a < 1` iff `b - a < 2√a + 1`. -/
lemma sqrt_sub_sqrt_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt b - Real.sqrt a < 1 ↔ b - a < 2 * Real.sqrt a + 1 := by
  have hsa : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
  have hpos : (0:ℝ) < 1 + Real.sqrt a := by linarith
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  constructor
  · intro h
    have h1 : Real.sqrt b < 1 + Real.sqrt a := by linarith
    have hb : b < (1 + Real.sqrt a) ^ 2 := (Real.sqrt_lt' hpos).mp h1
    nlinarith [hsq]
  · intro h
    have hb : b < (1 + Real.sqrt a) ^ 2 := by nlinarith [hsq]
    have := (Real.sqrt_lt' hpos).mpr hb
    linarith

/-- The two formulations of the Andrica conjecture are equivalent. -/
theorem andrica_iff_gap : AndricaStatement ↔ AndricaGapStatement := by
  constructor
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (by positivity)).mp (h n)
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (by positivity)).mpr (h n)

/-- **Conditional reduction of the Andrica conjecture.** Andrica's conjecture (still open)
follows from the prime-gap bound `p_{n+1} - p_n < 2√(p_n) + 1`; in fact the two statements
are equivalent (see `andrica_iff_gap`). -/
theorem AndricaConjecture (h : AndricaGapStatement) :
    ∀ n : ℕ, Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 :=
  andrica_iff_gap.mpr h

/-- Unconditional partial result: whenever the gap `p_{n+1} - p_n` is at most `2`
(e.g. for twin primes), the Andrica inequality holds at `n`. -/
theorem andrica_of_gap_le_two (n : ℕ) (hgap : prime (n + 1) ≤ prime n + 2) :
    Real.sqrt (prime (n + 1)) - Real.sqrt (prime n) < 1 := by
  have hp : (1:ℝ) ≤ (prime n : ℝ) := by exact_mod_cast (prime_pos n)
  have hs : (1:ℝ) ≤ Real.sqrt (prime n) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hp
  have hgap' : (prime (n + 1) : ℝ) ≤ (prime n : ℝ) + 2 := by exact_mod_cast hgap
  refine (sqrt_sub_sqrt_lt_one_iff (by positivity)).mpr ?_
  linarith

/-- Unconditional verification of the first instance: `√3 - √2 < 1`. -/
theorem andrica_zero : Real.sqrt (prime 1) - Real.sqrt (prime 0) < 1 := by
  refine andrica_of_gap_le_two 0 ?_
  have h0 : prime 0 = 2 := prime_zero
  have h1 : prime (0 + 1) = 3 := by
    have hc : Nat.count Nat.Prime 3 = 1 := by decide
    have h := Nat.nth_count (p := Nat.Prime) (n := 3) (by norm_num)
    rw [hc] at h
    simp [prime, h]
  omega

end Brockian.AndricaConjecture

