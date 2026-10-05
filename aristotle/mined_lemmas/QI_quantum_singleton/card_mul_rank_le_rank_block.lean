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

theorem card_mul_rank_le_rank_block {R A : Type} [Fintype R] [DecidableEq R] [Fintype A]
    [DecidableEq A] (g : Matrix A A ℂ) :
    Fintype.card R * g.rank ≤
      (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then g p.2 q.2 else 0).rank := by
  classical
  obtain ⟨X, Y, hXY⟩ := exists_rank_factorization g
  have hX : X.rank = g.rank := by
    refine le_antisymm (by simpa using X.rank_le_card_width) ?_
    calc g.rank = (X * Y).rank := by rw [← hXY]
      _ ≤ X.rank := Matrix.rank_mul_le_left X Y
  have hY : Y.rank = g.rank := by
    refine le_antisymm (by simpa using Y.rank_le_card_height) ?_
    calc g.rank = (X * Y).rank := by rw [← hXY]
      _ ≤ Y.rank := Matrix.rank_mul_le_right X Y
  obtain ⟨L, hL⟩ := exists_left_inv X hX
  obtain ⟨S, hS⟩ := exists_right_inv Y hY
  set BX : Matrix (R × A) (R × Fin g.rank) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then X p.2 q.2 else 0 with hBXdef
  set BY : Matrix (R × Fin g.rank) (R × A) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then Y p.2 q.2 else 0 with hBYdef
  set BL : Matrix (R × Fin g.rank) (R × A) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then L p.2 q.2 else 0 with hBLdef
  set BS : Matrix (R × A) (R × Fin g.rank) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then S p.2 q.2 else 0 with hBSdef
  have hBXY : BX * BY = Matrix.of fun (p : R × A) (q : R × A) =>
      if p.1 = q.1 then g p.2 q.2 else 0 := by
    rw [hBXdef, hBYdef, block_mul, ← hXY]
  have hBL' : BL * BX = 1 := by rw [hBLdef, hBXdef, block_mul, hL, block_one]
  have hBS' : BY * BS = 1 := by rw [hBYdef, hBSdef, block_mul, hS, block_one]
  have h1 : (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then g p.2 q.2 else 0) * BS
      = BX := by rw [← hBXY, Matrix.mul_assoc, hBS', Matrix.mul_one]
  calc Fintype.card R * g.rank
      = (1 : Matrix (R × Fin g.rank) (R × Fin g.rank) ℂ).rank := by
        rw [Matrix.rank_one, Fintype.card_prod, Fintype.card_fin]
    _ = (BL * BX).rank := by rw [hBL']
    _ ≤ BX.rank := Matrix.rank_mul_le_right BL BX
    _ = ((Matrix.of fun (p : R × A) (q : R × A) =>
          if p.1 = q.1 then g p.2 q.2 else 0) * BS).rank := by rw [h1]
    _ ≤ _ := Matrix.rank_mul_le_left _ _

/-- Entrywise complex conjugation preserves the rank. -/
