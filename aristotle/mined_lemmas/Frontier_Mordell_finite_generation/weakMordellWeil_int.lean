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

lemma weakMordellWeil_int : WeakMordellWeil ℤ := by
  classical
  refine Finite.of_surjective (α := Bool)
    (fun b => QuotientAddGroup.mk (s := twoSubgroup ℤ) (if b then 1 else 0)) ?_
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H k =>
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨false, ?_⟩
      simp only [if_neg (by simp : ¬ (false = true))]
      refine QuotientAddGroup.eq.mpr ?_
      exact mem_twoSubgroup_iff.mpr ⟨m, by rw [two_nsmul]; omega⟩
    · refine ⟨true, ?_⟩
      refine QuotientAddGroup.eq.mpr ?_
      exact mem_twoSubgroup_iff.mpr ⟨m, by simp only [if_true]; rw [two_nsmul]; omega⟩

/-- Sanity check (non-vacuity): the descent theorem applies to `ℤ`. -/
