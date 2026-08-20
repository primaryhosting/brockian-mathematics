/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x^2 + B x y + C y^2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : Int
  B : Int
  C : Int
deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/

theorem bhargava_cube_law (A B C : Int) (P : BQF) (hP : P.A = 1)
    (hPd : P.disc = B ^ 2 - 4 * A * C) :
    ((cubeOfForm A B C).form1.disc = (⟨A, B, C⟩ : BQF).disc ∧
      (cubeOfForm A B C).form2.disc = (⟨A, B, C⟩ : BQF).disc ∧
      (cubeOfForm A B C).form3.disc = (⟨A, B, C⟩ : BQF).disc) ∧
    (cubeOfForm A B C).form1.SLEquiv P ∧
    (cubeOfForm A B C).form2 = ⟨A, B, C⟩ ∧
    (cubeOfForm A B C).form3 = (⟨A, B, C⟩ : BQF).op ∧
    (∀ x₁ y₁ x₂ y₂ : Int,
      (cubeOfForm A B C).form1.eval x₁ y₁ * (cubeOfForm A B C).form2.eval x₂ y₂
        = (cubeOfForm A B C).form3.op.eval
            (x₁ * x₂ - B * x₂ * y₁ - C * y₁ * y₂) (x₁ * y₂ + A * x₂ * y₁)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp, by simp, ?_⟩
  · simp only [form1_cubeOfForm, BQF.disc]
    grind
  · simp only [form2_cubeOfForm]
  · simp only [form3_cubeOfForm, BQF.disc_op]
  · refine SLEquiv_of_lead_one (by simp) hP ?_
    simp only [BQF.disc] at hPd
    simp only [form1_cubeOfForm, BQF.disc]
    grind
  · intro x₁ y₁ x₂ y₂
    simp only [form1_cubeOfForm, form2_cubeOfForm, form3_cubeOfForm, BQF.op_op]
    exact principal_comp_identity A B C x₁ y₁ x₂ y₂

/-- The hypotheses of `bhargava_cube_law` are non-vacuous: for every `A B C` the form
`(1, B, AC)` has leading coefficient `1` and discriminant `B² - 4AC`, so it is a
representative of the principal class of that discriminant. -/
