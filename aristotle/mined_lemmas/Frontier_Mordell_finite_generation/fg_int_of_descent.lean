import Mathlib

/-!
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open scoped Classical

/-- Multiplication by `m : ℕ` on an additive commutative group, as a group homomorphism. -/

theorem fg_int_of_descent : AddGroup.FG ℤ := by
  refine fg_of_descent 2 le_rfl finite_quotient_int_two (fun n => ((n : ℝ)) ^ 2)
    (fun Q => ⟨2 * ((Q : ℝ)) ^ 2, fun P => by push_cast; nlinarith [sq_nonneg ((P : ℝ) - Q)]⟩)
    ⟨0, fun P => by
      have h : (((2 : ℕ) • P : ℤ) : ℝ) = 2 * (P : ℝ) := by simp
      show ((2 : ℕ) : ℝ) ^ 2 * ((P : ℝ)) ^ 2 - 0 ≤ (((2 : ℕ) • P : ℤ) : ℝ) ^ 2
      rw [h]; norm_num; nlinarith [sq_nonneg ((P : ℝ))]⟩ finite_sublevel_int_sq

/-! ## Mordell's theorem for elliptic curves over `ℚ` -/

/-- **Mordell's theorem** (reduction to the weak Mordell–Weil theorem and the theory of heights).

Let `W` be an elliptic curve over `ℚ` and let `W.toAffine.Point` be its group of rational points.
Assume:

* (weak Mordell–Weil) the quotient `E(ℚ) / m E(ℚ)` is finite for some `m ≥ 2`;
* there is a height function `h` on `E(ℚ)` satisfying the standard estimates: it is quasi-quadratic
  under translation by a fixed point and under multiplication by `m`, and has finite sublevel sets.

Then `E(ℚ)` is a finitely generated abelian group.

(The `W.IsElliptic` hypothesis is part of the statement of Mordell's theorem, even though the
descent argument below only uses the group structure on `W.toAffine.Point`, which Mathlib provides
for any Weierstrass curve over a field.) -/
