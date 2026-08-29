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

theorem rank_map_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).rank = M.rank := by
  have key : ∀ N : Matrix m n ℂ, (N.map (starRingEnd ℂ)).rank ≤ N.rank := by
    intro N
    obtain ⟨X, Y, h⟩ := exists_rank_factorization N
    have hmap : N.map (starRingEnd ℂ)
        = (X.map (starRingEnd ℂ)) * (Y.map (starRingEnd ℂ)) := by
      conv_lhs => rw [h]
      rw [Matrix.map_mul]
    rw [hmap]
    calc ((X.map (starRingEnd ℂ)) * (Y.map (starRingEnd ℂ))).rank
        ≤ (X.map (starRingEnd ℂ)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin N.rank) := Matrix.rank_le_card_width _
      _ = N.rank := by simp
  refine le_antisymm (key M) ?_
  have h2 := key (M.map (starRingEnd ℂ))
  have hid : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
    ext p q
    simp
  rwa [hid] at h2

/-- The rank of the transpose, over `ℂ`. -/
