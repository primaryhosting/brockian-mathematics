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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-!
## The arithmetic side: the Mordell–Weil rank

We work with an integral Weierstrass model `W : WeierstrassCurve ℤ` with nonzero
discriminant; the associated elliptic curve over `ℚ` is the base change
`W.map (Int.castRingHom ℚ)`, whose group of rational points is
`(W.map (Int.castRingHom ℚ)).toAffine.Point` (affine nonsingular points together with
the point at infinity).
-/

/-- The Mordell–Weil group `E(ℚ)` of the integral Weierstrass model `W`. -/
abbrev MordellWeil (W : WeierstrassCurve ℤ) : Type :=
  (W.map (Int.castRingHom ℚ)).toAffine.Point

/-- The Mordell–Weil rank of `E(ℚ)`, defined as the `ℚ`-dimension of `ℚ ⊗_ℤ E(ℚ)`
(equivalently, the rank of the free part of the finitely generated abelian group `E(ℚ)`). -/

theorem mwRank_eq_zero_of_torsion {W : WeierstrassCurve ℤ}
    (h : ∀ P : MordellWeil W, ∃ n : ℕ, n ≠ 0 ∧ n • P = 0) : mwRank W = 0 := by
  have hsub : Subsingleton (TensorProduct ℤ ℚ (MordellWeil W)) := by
    constructor
    suffices hz : ∀ z : TensorProduct ℤ ℚ (MordellWeil W), z = 0 by
      intro x y; rw [hz x, hz y]
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rfl
    | tmul q P =>
        obtain ⟨n, hn, hnP⟩ := h P
        have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        have hq : ((n : ℤ) • (q / n) : ℚ) = q := by
          rw [zsmul_eq_mul]; push_cast; field_simp
        calc (q ⊗ₜ[ℤ] P : TensorProduct ℤ ℚ (MordellWeil W))
            = ((n : ℤ) • (q / n)) ⊗ₜ[ℤ] P := by rw [hq]
          _ = (q / n) ⊗ₜ[ℤ] ((n : ℤ) • P) := TensorProduct.smul_tmul _ _ _
          _ = 0 := by
              rw [show ((n : ℤ) • P) = (n : ℕ) • P by simp, hnP, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  exact Module.finrank_zero_of_subsingleton

/-- **Base case of BSD.** If `E(ℚ)` is a torsion group, then BSD for `E` is equivalent to
the non-vanishing `L(E, 1) ≠ 0`. -/
