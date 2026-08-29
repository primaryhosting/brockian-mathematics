/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace CS

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/

lemma convex_comb_le {α : Type*} [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α)
    {f : α → ℝ} {m : ℝ} (h : ∀ a, f a ≤ m) : ∑ a, w a * f a ≤ m := by
  obtain ⟨h0, h1⟩ := hw
  calc ∑ a, w a * f a ≤ ∑ a, w a * m :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (h0 a)
    _ = m := by rw [← Finset.sum_mul, h1, one_mul]

/-- Exchanging the order of averaging: averaging the randomized cost over inputs is the same as
averaging the distributional cost over algorithms. -/
