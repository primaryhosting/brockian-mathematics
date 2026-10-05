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

theorem exists_left_inv {m : Type} [Fintype m] [DecidableEq m] {r : ℕ}
    (X : Matrix m (Fin r) ℂ) (h : X.rank = r) : ∃ L : Matrix (Fin r) m ℂ, L * X = 1 := by
  classical
  have hker : LinearMap.ker X.mulVecLin = ⊥ := by
    have h2 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [show Module.finrank ℂ (LinearMap.range X.mulVecLin) = r from h] at h2
    simp only [Module.finrank_fin_fun] at h2
    have h3 : Module.finrank ℂ (LinearMap.ker X.mulVecLin) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective X.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h3 : LinearMap.toMatrix' (g ∘ₗ X.mulVecLin) = LinearMap.toMatrix' LinearMap.id := by
    rw [hg]
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulVecLin] at h3
  simpa using h3

/-- A matrix with full row rank has a right inverse. -/
