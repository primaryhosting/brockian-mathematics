/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring before `import`; the required header is repeated verbatim
-- as the module docstring immediately below the import.)

import Mathlib

/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open scoped TensorProduct

/-! ## The arithmetic side: Mordell–Weil rank -/

/-- The Mordell–Weil group `E(ℚ)` of an integral Weierstrass model `W`, i.e. the group of
rational nonsingular points of the base change of `W` to `ℚ`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type := (W.baseChange ℚ).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the dimension of `ℚ ⊗ℤ E(ℚ)` over `ℚ`.
For a finitely generated abelian group this is exactly the rank of its free part. -/

theorem subsingleton_rat_tensor_of_isTorsion (M : Type) [AddCommGroup M]
    (h : AddMonoid.IsTorsion M) : Subsingleton (ℚ ⊗[ℤ] M) := by
  constructor
  have key : ∀ x : ℚ ⊗[ℤ] M, x = 0 := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        obtain ⟨n, hn, hnm⟩ : ∃ n : ℕ, 0 < n ∧ (n : ℤ) • m = 0 := by
          refine ⟨addOrderOf m, ?_, ?_⟩
          · exact (h m).addOrderOf_pos
          · simp
        have hq : q = (n : ℤ) • (q / (n : ℚ)) := by
          have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
          rw [zsmul_eq_mul]
          push_cast
          field_simp
        calc q ⊗ₜ[ℤ] m = ((n : ℤ) • (q / (n : ℚ))) ⊗ₜ[ℤ] m := by rw [← hq]
          _ = (q / (n : ℚ)) ⊗ₜ[ℤ] ((n : ℤ) • m) := TensorProduct.smul_tmul _ _ _
          _ = 0 := by rw [hnm, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  intro a b
  rw [key a, key b]

/-- **Base case of BSD (arithmetic side).** If the Mordell–Weil group `E(ℚ)` is torsion — that is,
`E` has rank `0` in the naive sense that every rational point has finite order — then the
Mordell–Weil rank as defined above is `0`. -/
