import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/

theorem block_one {R A : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] :
    (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then (1 : Matrix A A ℂ) p.2 q.2 else 0)
      = 1 := by
  ext p q
  by_cases h : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [Matrix.one_apply, h, h2, Prod.ext_iff]

/-- The rank of a block-diagonal matrix with `|R|` copies of `g` is `|R| * rank g`
(the inequality we need). -/
