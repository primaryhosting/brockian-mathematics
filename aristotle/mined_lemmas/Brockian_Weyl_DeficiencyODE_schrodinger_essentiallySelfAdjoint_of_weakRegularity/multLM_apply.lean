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

@[simp] theorem multLM_apply (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) (f : L2Z) (n : ℤ) :
    multLM V C hV f n = (V n : ℂ) * f n := rfl

/-- Multiplication by a bounded real potential, as a bounded operator on `ℓ²(ℤ, ℂ)`. -/
