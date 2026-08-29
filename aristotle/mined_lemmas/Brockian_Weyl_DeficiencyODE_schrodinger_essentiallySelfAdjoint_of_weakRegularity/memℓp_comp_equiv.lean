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

theorem memℓp_comp_equiv (f : L2Z) (e : ℤ ≃ ℤ) : Memℓp (fun n => f (e n)) 2 := by
  refine memℓp_gen ?_
  have hf : Summable fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal :=
    (lp.memℓp f).summable (by norm_num)
  exact (e.summable_iff (f := fun n : ℤ => ‖f n‖ ^ (2 : ENNReal).toReal)).2 hf

/-- Reindexing `ℓ²(ℤ, ℂ)` along a permutation of `ℤ`, as a linear map. -/
