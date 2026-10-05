/-
# Balance Nullspace
Category: Chemistry
Target: Chem.balance_nullspace
Verification: pending
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

namespace Chem

/-! ## A ℚ-linear functional that is positive on a finite family of positive reals -/

/-- Given finitely many *positive* real numbers `x s`, there is a `ℚ`-linear functional
`f : ℝ →ₗ[ℚ] ℚ` which is positive on all of them.  (Such an `f` is a rational
"approximation of the identity" on the `ℚ`-span of the `x s`.) -/

theorem exists_pos_rat_null {E S : Type*} [Fintype S] (A : Matrix E S ℤ) (x : S → ℝ)
    (hx : ∀ s, 0 < x s) (h : ∀ e, ∑ s, (A e s : ℝ) * x s = 0) :
    ∃ y : S → ℚ, (∀ s, 0 < y s) ∧ ∀ e, ∑ s, (A e s : ℚ) * y s = 0 := by
  obtain ⟨f, hf⟩ := exists_ratLinearMap_pos x hx
  refine ⟨fun s => f (x s), hf, fun e => ?_⟩
  have h0 : ∑ s, f (((A e s : ℚ) : ℝ) * x s) = 0 := by
    rw [← map_sum]
    have h1 : ∑ s, ((A e s : ℚ) : ℝ) * x s = 0 := by push_cast; exact h e
    rw [h1, map_zero]
  have h3 : ∑ s, (A e s : ℚ) * f (x s) = ∑ s, f (((A e s : ℚ) : ℝ) * x s) :=
    Finset.sum_congr rfl fun s _ => by rw [← Rat.smul_def, map_smul, smul_eq_mul]
  rw [h3, h0]

/-! ## Clearing denominators -/

