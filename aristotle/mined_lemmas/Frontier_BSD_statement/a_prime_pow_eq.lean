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

theorem a_prime_pow_eq (D₁ D₂ : LFunctionDatum E) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    D₁.a (p ^ k) = D₂.a (p ^ k) := by
  have hp1 : D₁.a p = D₂.a p := D₁.a_prime_eq D₂ hp
  by_cases hd : ((p : ℤ) ∣ E.Δ)
  · rw [D₁.a_prime_pow_bad p k hp hd, D₂.a_prime_pow_bad p k hp hd, hp1]
  · induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k with
      | 0 => simp [D₁.a_one, D₂.a_one]
      | 1 => simpa using hp1
      | (m + 2) =>
        rw [D₁.a_prime_pow_good p m hp hd, D₂.a_prime_pow_good p m hp hd,
          ih (m + 1) (by omega), ih m (by omega), hp1]

/-- **Uniqueness of the Hasse–Weil coefficients.** Any two L-function data for the same
integral Weierstrass model have the same Dirichlet coefficients (at every `n ≠ 0`; the value
at `n = 0` is irrelevant for the L-series). -/
