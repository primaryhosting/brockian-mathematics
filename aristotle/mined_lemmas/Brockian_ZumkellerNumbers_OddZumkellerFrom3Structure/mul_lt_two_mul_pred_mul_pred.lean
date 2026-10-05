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
/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is *Zumkeller* if its set of divisors can be split into
two blocks having the same sum. -/

theorem mul_lt_two_mul_pred_mul_pred {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hpo : Odd p) (hqo : Odd q) (hne : p ≠ q) :
    p * q < 2 * ((p - 1) * (q - 1)) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = 2 * a + 3 := by
    obtain ⟨k, hk⟩ := hpo; exact ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = 2 * b + 3 := by
    obtain ⟨k, hk⟩ := hqo; exact ⟨k - 1, by omega⟩
  have h1 : 1 ≤ a + b := by omega
  rw [show 2 * a + 3 - 1 = 2 * a + 2 from by omega, show 2 * b + 3 - 1 = 2 * b + 2 from by omega]
  nlinarith

/-- A Zumkeller number is abundant-or-perfect: `2 * n ≤ σ(n)`. -/
