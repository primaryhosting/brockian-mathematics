/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A probability distribution on a finite type. -/

lemma isOpen_lowBox (t : ℝ) : IsOpen (lowBox I t) := by
  have : lowBox I t = ⋂ i : I, (fun y : I → ℝ => y i) ⁻¹' (Set.Iio t) := by
    ext y; simp [lowBox]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (continuous_apply i).isOpen_preimage _ isOpen_Iio

omit [Fintype I] [DecidableEq I] in
