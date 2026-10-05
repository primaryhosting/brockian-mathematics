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

theorem rank_transpose_complex {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℂ) : Mᵀ.rank = M.rank := by
  have h : Mᵀ = (Mᴴ).map (starRingEnd ℂ) := by
    ext p q
    simp
  rw [h, rank_map_conj, Matrix.rank_conjTranspose]

/-! ## The tensor flattening rank inequality -/

/-- For a three-index tensor `f p b c`, the rank of the flattening that groups `(b, c)` together
is at most the product of the ranks of the flattenings that isolate `b` and `c`.
This is the linear-algebra substitute for subadditivity of entropy. -/
