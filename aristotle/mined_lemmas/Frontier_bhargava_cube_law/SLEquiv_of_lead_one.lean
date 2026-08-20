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

theorem SLEquiv_of_lead_one {Q Q' : BQF} (hQ : Q.A = 1) (hQ' : Q'.A = 1)
    (hd : Q.disc = Q'.disc) : Q.SLEquiv Q' := by
  obtain ⟨A, B, C⟩ := Q
  obtain ⟨A', B', C'⟩ := Q'
  simp only at hQ hQ'
  subst hQ; subst hQ'
  simp only [BQF.disc] at hd
  have h : B ^ 2 - B' ^ 2 = 4 * (C - C') := by grind
  obtain ⟨k, hk⟩ := exists_two_mul_sub h
  subst hk
  have hC : C' = C - k * B + k ^ 2 := by grind
  subst hC
  refine ⟨1, -k, 0, 1, by grind, ?_⟩
  intro x y
  simp only [BQF.eval]
  grind

/-! ## The base case of the cube law -/

/-- The Bhargava cube attached to a binary quadratic form `Q = (A, B, C)`.  It encodes
the multiplication map `𝒪 × I → I` for the ideal `I = ⟨A, B - ω⟩` of the quadratic
ring `𝒪 = ℤ[ω]`, `ω² = B ω - A C`, whose norm form is `Q`. -/
