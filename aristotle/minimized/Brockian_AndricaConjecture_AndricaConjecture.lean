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

import Mathlib

/-!
# Andrica Conjecture
Category: Brockian Conjecture
Target: Brockian.AndricaConjecture.AndricaConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.AndricaConjecture

open Real

/-- `primeSeq n` is the `n`-th prime number (`primeSeq 0 = 2`). -/

noncomputable def primeSeq (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- Andrica's conjecture: `√p_{n+1} - √p_n < 1` for every `n`. -/

def AndricaStatement : Prop :=
  ∀ n : ℕ, Real.sqrt (primeSeq (n + 1)) - Real.sqrt (primeSeq n) < 1

/-- The prime-gap reformulation of Andrica's conjecture:
`p_{n+1} - p_n < 2√p_n + 1` for every `n`. -/

def GapStatement : Prop :=
  ∀ n : ℕ, (primeSeq (n + 1) : ℝ) - primeSeq n < 2 * Real.sqrt (primeSeq n) + 1

/-- Elementary equivalence: for nonnegative reals, `√b - √a < 1` iff `b - a < 2√a + 1`. -/

theorem sqrt_sub_sqrt_lt_one_iff {a b : ℝ} (ha : 0 ≤ a) :
    Real.sqrt b - Real.sqrt a < 1 ↔ b - a < 2 * Real.sqrt a + 1 := by
  have hpos : 0 < Real.sqrt a + 1 := by positivity
  have hsq : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  constructor
  · intro h
    have h' : Real.sqrt b < Real.sqrt a + 1 := by linarith
    have := (Real.sqrt_lt' hpos).1 h'
    nlinarith [this, hsq]
  · intro h
    have hb : b < (Real.sqrt a + 1) ^ 2 := by nlinarith [hsq]
    have := (Real.sqrt_lt' hpos).2 hb
    linarith

/-- **Reduction of the Andrica conjecture to a prime-gap bound.**

Andrica's conjecture (`√p_{n+1} - √p_n < 1` for all `n`) is equivalent to the
statement that the `n`-th prime gap satisfies `p_{n+1} - p_n < 2√p_n + 1`.

Andrica's conjecture is an open problem, so this is a Lean-checked equivalent
reformulation rather than an unconditional proof. -/

theorem AndricaConjecture : AndricaStatement ↔ GapStatement := by
  constructor
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (a := (primeSeq n : ℝ)) (b := (primeSeq (n + 1) : ℝ))
      (Nat.cast_nonneg _)).1 (h n)
  · intro h n
    exact (sqrt_sub_sqrt_lt_one_iff (a := (primeSeq n : ℝ)) (b := (primeSeq (n + 1) : ℝ))
      (Nat.cast_nonneg _)).2 (h n)

/-- Every prime in the sequence is at least `2`. -/
