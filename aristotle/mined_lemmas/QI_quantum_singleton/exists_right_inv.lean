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

theorem exists_right_inv {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
    (Y : Matrix (Fin r) n ℂ) (h : Y.rank = r) : ∃ S : Matrix n (Fin r) ℂ, Y * S = 1 := by
  classical
  have hr : LinearMap.range Y.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using h
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Y.mulVecLin hr
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h3 : LinearMap.toMatrix' (Y.mulVecLin ∘ₗ g) = LinearMap.toMatrix' LinearMap.id := by
    rw [hg]
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulVecLin] at h3
  simpa using h3

/-- Rank is unchanged by multiplication with a nonzero scalar. -/
