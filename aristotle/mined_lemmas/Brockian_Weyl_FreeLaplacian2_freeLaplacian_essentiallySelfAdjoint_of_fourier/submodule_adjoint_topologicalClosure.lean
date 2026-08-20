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
# The basic criterion for essential self-adjointness

This file develops the abstract operator-theoretic input for `Brockian.Weyl.FreeLaplacian2`:
a densely defined symmetric operator on a complex Hilbert space whose two deficiency ranges
`Ran (T + i)` and `Ran (T - i)` are dense has self-adjoint closure, i.e. it is
*essentially self-adjoint*.
-/

namespace Brockian.Weyl

open LinearPMap Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `x ↦ T x + z • x` on the domain of `T`. -/

theorem submodule_adjoint_topologicalClosure (g : Submodule ℂ (H × H)) :
    g.topologicalClosure.adjoint = g.adjoint := by
  ext x
  simp only [Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    exact h a b (Submodule.le_topologicalClosure g hab)
  · intro h a b hab
    have hcont : Continuous fun p : H × H => inner ℂ p.2 x.1 - inner ℂ p.1 x.2 := by fun_prop
    have hset : (g : Set (H × H)) ⊆ {p : H × H | inner ℂ p.2 x.1 - inner ℂ p.1 x.2 = 0} :=
      fun p hp => h p.1 p.2 hp
    simpa using closure_minimal hset (isClosed_eq hcont continuous_const) hab

omit [CompleteSpace H] in
/-- The domain of the closure of a densely defined operator is dense. -/
