/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

variable {n : ℕ}

/-- The standard symplectic vector space `ℝ^(2n+2)`, realised as the Euclidean space with
index set `Fin (n+1) ⊕ Fin (n+1)`: the `Sum.inl` coordinates are the positions `q₀,…,qₙ`
and the `Sum.inr` coordinates are the conjugate momenta `p₀,…,pₙ`. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (x_{qᵢ} y_{pᵢ} - x_{pᵢ} y_{qᵢ})`. -/

lemma surjective_of_preserves_omegaForm (Ψ : SymplecticSpace n →ₗ[ℝ] SymplecticSpace n)
    (hsymp : ∀ x y : SymplecticSpace n, omegaForm (Ψ x) (Ψ y) = omegaForm x y) :
    Function.Surjective Ψ := by
  refine LinearMap.injective_iff_surjective.mp ?_
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine eq_zero_of_omegaForm_eq_zero (fun y => ?_)
  rw [← hsymp x y, hx]
  simp [omegaForm]

/-- **Gromov's nonsqueezing theorem (linear symplectic case).**

If a linear symplectomorphism `Ψ` of the standard symplectic vector space `ℝ^{2n+2}` maps the
open ball of radius `r` into the symplectic cylinder
`Z(R) = {z | z_{q₀}² + z_{p₀}² < R²}`, then necessarily `r ≤ R`.

In other words, a ball can never be symplectically squeezed into a thinner cylinder whose
cross-section is spanned by a conjugate pair of coordinates. -/
