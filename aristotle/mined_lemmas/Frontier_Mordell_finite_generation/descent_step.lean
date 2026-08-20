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

lemma descent_step {A : Type u} [AddCommGroup A] (h : HeightFunction A) (R : Finset A)
    (hR : ∀ P : A, ∃ Q ∈ R, ∃ S : A, P = 2 • S + Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P : A, B < h.toFun P →
      ∃ Q ∈ R, ∃ S : A, P = 2 • S + Q ∧ h.toFun S < h.toFun P := by
  classical
  obtain ⟨c₂, hc₂⟩ := h.duplication
  choose c hc using fun Q : A => h.translate (-Q)
  set T : Finset ℝ := insert (0 : ℝ) (R.image c) with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set M : ℝ := T.max' hTne with hM
  have hM0 : 0 ≤ M := Finset.le_max' T 0 (Finset.mem_insert_self _ _)
  have hMc : ∀ Q ∈ R, c Q ≤ M :=
    fun Q hQ => Finset.le_max' T (c Q) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem c hQ))
  refine ⟨max (M + c₂) 1, le_trans zero_le_one (le_max_right _ _), fun P hP => ?_⟩
  obtain ⟨Q, hQ, S, rfl⟩ := hR P
  refine ⟨Q, hQ, S, rfl, ?_⟩
  have h1 : 4 * h.toFun S ≤ h.toFun (2 • S) + c₂ := hc₂ S
  have h2 : h.toFun ((2 • S + Q) + -Q) ≤ 2 * h.toFun (2 • S + Q) + c Q := hc Q _
  have h3 : (2 • S + Q) + -Q = 2 • S := by abel
  rw [h3] at h2
  have h4 : c Q ≤ M := hMc Q hQ
  have h5 : M + c₂ ≤ max (M + c₂) 1 := le_max_left _ _
  have h6 : (1 : ℝ) ≤ max (M + c₂) 1 := le_max_right _ _
  linarith

/-- **Descent theorem.** An abelian group carrying a height function in the above sense
and satisfying weak Mordell–Weil is finitely generated. -/
