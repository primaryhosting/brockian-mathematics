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

theorem schrodingerCLM_isSelfAdjoint (V : ℤ → ℝ) (C : ℝ) (hV : ∀ n, |V n| ≤ C) :
    IsSelfAdjoint (schrodingerCLM V C hV) :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 (schrodingerCLM_isSymmetric V C hV)

/-! ### Main result -/

/-- **Essential self-adjointness of the discrete Schrödinger operator under weak regularity.**

Let `V : ℤ → ℝ` be a potential which is only assumed *bounded* (weak regularity: no continuity,
smoothness or decay is required), and let `T` be the Schrödinger operator
`(T f) n = 2 f n - f (n+1) - f (n-1) + V n * f n` defined on the (dense) subspace of finitely
supported sequences in `ℓ²(ℤ, ℂ)`. Then `T` is essentially self-adjoint: its adjoint is
self-adjoint, so `T` has a unique self-adjoint extension, namely its closure. -/
