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
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `Solvable n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural denominators. -/

theorem solvable_mul (k n : ℕ) (hk : 0 < k) (h : Solvable n) : Solvable (k * n) := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := h
  refine ⟨k * x, k * y, k * z, Nat.mul_pos hk hx, Nat.mul_pos hk hy, Nat.mul_pos hk hz, ?_⟩
  have e0 : (4 : ℚ) / ((k * n : ℕ) : ℚ) = (4 / (n : ℚ)) / (k : ℚ) := by
    push_cast; rw [div_div, mul_comm]
  have e1 : ∀ w : ℕ, (1 : ℚ) / ((k * w : ℕ) : ℚ) = (1 / (w : ℚ)) / (k : ℚ) := by
    intro w; push_cast; rw [div_div, mul_comm]
  rw [e0, e1, e1, e1, div_add_div_same, div_add_div_same, h]

/-- Divisibility form of the scaling lemma. -/
