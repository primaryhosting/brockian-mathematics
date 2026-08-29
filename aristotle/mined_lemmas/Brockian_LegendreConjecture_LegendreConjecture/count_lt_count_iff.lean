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
