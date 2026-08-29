/-
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28 requires `import` to precede any module docstring, so the header above is a plain
-- block comment; the identical module docstring is repeated immediately after the imports.)

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
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The arithmetic side: Mordell–Weil rank

An elliptic curve over `ℚ` is presented by an integral Weierstrass model
`W : WeierstrassCurve ℤ` (a global minimal model, see `Frontier.IsGlobalMinimal`).  Its group of
rational points is the Mordell–Weil group `(W.map (Int.castRingHom ℚ)).toAffine.Point`, and its
rank is the dimension of the `ℚ`-vector space `ℚ ⊗_ℤ E(ℚ)`. -/

/-- The Mordell–Weil group `E(ℚ)` of the elliptic curve defined by the integral Weierstrass
model `W`. -/
abbrev RationalPoints (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The (algebraic) rank of `E(ℚ)`, defined as `dim_ℚ (ℚ ⊗_ℤ E(ℚ))`.  For a finitely generated
abelian group this is the usual Mordell–Weil rank. -/

theorem finrank_rat_tensor_eq_zero (M : Type) [AddCommGroup M] [Finite M] :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = 0 := by
  have : Subsingleton (ℚ ⊗[ℤ] M) := by
    constructor
    intro x y
    suffices h : ∀ z : ℚ ⊗[ℤ] M, z = 0 by rw [h x, h y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q m =>
        have hcard : (Nat.card M) • m = 0 := card_nsmul_eq_zero'
        have h1 : q = ((Nat.card M : ℤ)) • (q / (Nat.card M : ℚ)) := by
          have hne : ((Nat.card M : ℚ)) ≠ 0 := by
            simpa using (Nat.card_pos (α := M)).ne'
          push_cast [zsmul_eq_mul]
          field_simp
        rw [h1, TensorProduct.smul_tmul, natCast_zsmul, hcard, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact Module.finrank_zero_of_subsingleton

/-- If `E(ℚ)` is finite then the Mordell–Weil rank is `0`. -/
