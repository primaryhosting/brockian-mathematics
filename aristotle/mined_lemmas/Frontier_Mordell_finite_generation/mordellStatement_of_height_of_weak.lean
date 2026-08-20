/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
(The header above is a plain block comment rather than a module docstring, since Lean 4
does not allow a module docstring to precede the `import` commands.)

# Mordell's theorem: finite generation of `E(ℚ)`

We formalize the statement that the group of rational points of an elliptic curve over `ℚ`
is finitely generated, and we prove the *descent step* of the classical proof: an abelian
group equipped with a height function satisfying the standard axioms and whose quotient by
`2A` is finite is finitely generated.  Specializing to `E(ℚ)` gives
`Frontier.Mordell_finite_generation`, a Lean-checked reduction of Mordell's theorem to the
weak Mordell–Weil theorem together with the existence of a height function.
-/

namespace Frontier

universe u

/-- Abstract height data on an abelian group `A`, modelled on the naive/canonical height
of an elliptic curve over `ℚ`:

* the height is nonnegative;
* there are only finitely many points of bounded height (Northcott property);
* translation by a fixed point distorts the height by a bounded factor;
* duplication multiplies the height by roughly `4`.
-/
structure HeightFunction (A : Type u) [AddCommGroup A] where
  /-- The height function itself. -/
  toFun : A → ℝ
  /-- Heights are nonnegative. -/
  nonneg : ∀ P, 0 ≤ toFun P
  /-- Northcott property: finitely many points of bounded height. -/
  finite_of_le : ∀ C : ℝ, {P : A | toFun P ≤ C}.Finite
  /-- Quasi-additivity of the height under translation by a fixed point. -/
  translate : ∀ Q : A, ∃ c : ℝ, ∀ P : A, toFun (P + Q) ≤ 2 * toFun P + c
  /-- Quasi-quadraticity of the height under duplication. -/
  duplication : ∃ c : ℝ, ∀ P : A, 4 * toFun P ≤ toFun (2 • P) + c

/-- The subgroup `2A` of an abelian group `A`. -/

theorem mordellStatement_of_height_of_weak
    (H : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → Nonempty (HeightFunction E.toAffine.Point))
    (W : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → WeakMordellWeil E.toAffine.Point) :
    MordellStatement := by
  intro E hE
  obtain ⟨height⟩ := H E hE
  exact fg_of_heightFunction_of_weakMordellWeil height (W E hE)

/-- **Mordell's theorem, as a Lean-checked reduction.**

The group `E(ℚ)` of rational points of an elliptic curve `E` over `ℚ` is finitely
generated, *given* the two standard inputs of the classical proof:

* the weak Mordell–Weil theorem for `E`, i.e. finiteness of `E(ℚ)/2E(ℚ)`;
* a height function on `E(ℚ)` with the standard properties (nonnegativity, the
  Northcott finiteness property, quasi-additivity under translation, and
  quasi-quadraticity under duplication).

The mathematical content proved here is the infinite-descent step, which turns these two
inputs into finite generation. -/
