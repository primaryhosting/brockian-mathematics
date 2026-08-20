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

theorem a_prime_eq (D₁ D₂ : LFunctionDatum E) {p : ℕ} (hp : p.Prime) : D₁.a p = D₂.a p := by
  by_cases hd : ((p : ℤ) ∣ E.Δ)
  · rw [D₁.a_prime_bad p hp hd, D₂.a_prime_bad p hp hd]
  · rw [D₁.a_prime_good p hp hd, D₂.a_prime_good p hp hd]

/-- The coefficients at prime powers are determined by the curve. -/
