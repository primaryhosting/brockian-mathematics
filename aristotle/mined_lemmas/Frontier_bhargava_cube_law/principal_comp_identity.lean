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

theorem principal_comp_identity (A B C x₁ y₁ x₂ y₂ : Int) :
    (⟨1, -B, A * C⟩ : BQF).eval x₁ y₁ * (⟨A, B, C⟩ : BQF).eval x₂ y₂
      = (⟨A, B, C⟩ : BQF).eval (x₁ * x₂ - B * x₂ * y₁ - C * y₁ * y₂)
          (x₁ * y₂ + A * x₂ * y₁) := by
  simp only [BQF.eval]
  grind

/-- **Bhargava's cube law (base case).**

Let `Q = (A, B, C)` be an integral binary quadratic form of discriminant
`D = B² - 4AC`, and let `P` be any form of discriminant `D` with leading coefficient
`1`, i.e. any representative of the principal class.  Then the Bhargava cube
`cubeOfForm A B C` has three binary quadratic forms `Q₁, Q₂, Q₃` with:

* all three of discriminant `D`;
* `Q₁` properly equivalent to `P` (the identity class);
* `Q₂ = Q`;
* `Q₃ = Qᵒᵖ`, a representative of the inverse class of `Q`;
* the Gauss composition identity `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(r, s)` for explicit
  integral bilinear forms `r, s` in `(x₁,y₁)` and `(x₂,y₂)`.

Thus `[Q₁] · [Q₂] · [Q₃] = 1` in the class group of forms of discriminant `D`: the
three forms of the cube compose to the identity.  This is Bhargava's cube law in the
base case, where the composition performed is Gauss composition with the principal
form. -/
