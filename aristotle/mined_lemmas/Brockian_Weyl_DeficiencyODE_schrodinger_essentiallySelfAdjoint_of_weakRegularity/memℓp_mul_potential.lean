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

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The required header comment is placed immediately after `import Mathlib`, since Lean 4 does not
-- allow a module doc comment to precede the `import` commands.)

open scoped LinearPMap ComplexConjugate

noncomputable section

namespace Brockian.Weyl.DeficiencyODE

/-- The Hilbert space `ℓ²(ℤ, ℂ)` of square-summable two-sided sequences. -/
abbrev L2Z : Type := lp (fun _ : ℤ => ℂ) 2

/-- A densely defined operator is *essentially self-adjoint* when its adjoint is self-adjoint;
equivalently, when its closure is its unique self-adjoint extension. -/

theorem memℓp_mul_potential (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) :
    Memℓp (fun n => (V n : ℂ) * f n) 2 := by
  refine memℓp_gen ?_
  have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (norm_nonneg _) _)
    (fun n => ?_) (hf.mul_left (C ^ (2 : ENNReal).toReal))
  have h1 : ‖(V n : ℂ) * f n‖ = |V n| * ‖f n‖ := by simp [Complex.norm_real]
  rw [h1, Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
  gcongr
  exact hV n

/-- Multiplication by a bounded real potential, as a linear map on `ℓ²(ℤ, ℂ)`. -/
