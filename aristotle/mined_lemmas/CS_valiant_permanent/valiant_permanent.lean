import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/

theorem valiant_permanent :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (M : Matrix V V ℕ), (∀ i j, M i j ≤ 1) →
        M.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, M i (σ i) = 1}) ∧
    (∀ (n : ℕ) (W : Matrix (Fin n) (Fin n) ℕ),
        ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
          N = n + ∑ i, ∑ j, W i j ∧ (∀ i j, B i j ≤ 1) ∧ B.permanent = W.permanent) := by
  classical
  refine ⟨fun V _ _ M h => permanent_eq_card_witnesses M h, fun n W => ?_⟩
  obtain ⟨e⟩ := Fintype.truncEquivFin (Vtx W)
  refine ⟨Fintype.card (Vtx W), (gadget W).submatrix e.symm e.symm, card_Vtx W, ?_, ?_⟩
  · intro i j
    exact gadget_zeroOne W _ _
  · rw [permanent_submatrix_equiv e.symm (gadget W)]
    exact permanent_gadget W

/-- Every natural number occurs as the permanent of a 0/1 matrix: the permanent of 0/1 matrices,
as a counting function, is onto `ℕ`. -/
