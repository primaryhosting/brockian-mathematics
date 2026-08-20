import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command in a file, and a
module docstring `/-! ... -/` may not precede it.  The requested header is therefore placed
immediately after the single `import Mathlib` line, which is as close to the beginning of the
file as the language permits.

Mathlib coverage: as of this Mathlib revision there is no Hasse-Weil L-function of an elliptic
curve, no Mordell-Weil theorem, and no BSD statement (`Mathlib/NumberTheory/LSeries/` covers
only Riemann/Hurwitz zeta and Dirichlet L-functions; `Mathlib/AlgebraicGeometry/EllipticCurve/`
provides the group of nonsingular points `WeierstrassCurve.Affine.Point` but nothing analytic).
So no existing lemma closes or nearly closes this goal; the analytic input is isolated below in
the structure `Frontier.LFunctionDatum`, and the Mordell-Weil theorem appears as the explicit
hypothesis `Module.Finite ℤ (MordellWeil E)`.
-/

open scoped Classical

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The Mordell–Weil group `E(ℚ)` of an elliptic curve given by an integral Weierstrass
equation `E` over `ℤ`: the group of nonsingular rational points of the base change of `E`
to `ℚ`, in affine coordinates (including the point at infinity). -/
abbrev MordellWeil (E : WeierstrassCurve ℤ) : Type :=
  (E.map (Int.castRingHom ℚ)).toAffine.Point

/-- The algebraic rank of `E`: the rank of the finitely generated abelian group `E(ℚ)`. -/

theorem a_eq (D₁ D₂ : LFunctionDatum E) {n : ℕ} (hn : n ≠ 0) : D₁.a n = D₂.a n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp _ => exact D₁.a_prime_pow_eq D₂ hp k
  | zero => exact absurd rfl hn
  | one => rw [D₁.a_one, D₂.a_one]
  | coprime x y hx hy hxy ihx ihy =>
      rw [D₁.a_mul x y hxy, D₂.a_mul x y hxy, ihx (by omega), ihy (by omega)]

/-- Consequently any two L-function data for the same curve define the same L-series on the
half-plane of absolute convergence. -/
