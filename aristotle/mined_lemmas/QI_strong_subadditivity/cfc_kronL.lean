import RequestProject.SSA.PartialTrace

/-!
# Strong Subadditivity
Category: Frontier Qi
Target: QI.strong_subadditivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
(The header comment above has to follow the `import` line: Lean requires `import` commands to
come first in a file.)

The von Neumann entropy `S(A) = -Tr (A log A)` of a positive definite matrix on a threefold
tensor product `α ⊗ β ⊗ γ` satisfies the Lieb–Ruskai inequality

`S(ρ_ABC) + S(ρ_B) ≤ S(ρ_AB) + S(ρ_BC)`.

The proof goes through Lindblad's joint convexity of the Umegaki relative entropy
(itself deduced from Ando's joint concavity of the operator geometric mean) and the
resulting monotonicity of the relative entropy under partial traces.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-! ### Relative entropy against `1 ⊗ Y` -/


lemma cfc_kronL {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    (1 : Matrix n n ℂ) ⊗ₖ cfc f A = cfc f ((1 : Matrix n n ℂ) ⊗ₖ A) :=
  StarAlgHomClass.map_cfc (R := ℝ) (S := ℂ) (kronHomL n m) f A hf kronHomL_continuous hA

end QI

import Mathlib

/-!
# Setup for the strong subadditivity development

Basic instances and helper lemmas about positive matrices, used throughout.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Matrices over `ℂ` form a C⋆-algebra (with the ℓ²-operator norm). -/
noncomputable instance matrixCStarAlgebra : CStarAlgebra (Matrix n n ℂ) where

end QI

import RequestProject.SSA.Dyadic
import RequestProject.SSA.Entropy

/-!
# The Kronecker lift and joint convexity of relative entropy

Multiplication operators `A ↦ A ⊗ 1` and `B ↦ 1 ⊗ Bᵀ` commute, so the iterated geometric
means of the lifted pair compute `Tr (A ^ (1 - 2⁻ᵐ) * B ^ (2⁻ᵐ))`.  Joint concavity of the
geometric mean therefore gives joint concavity of these trace functionals, and letting
`m → ∞` yields the joint convexity of the relative entropy.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder BigOperators Kronecker
open Matrix

set_option maxHeartbeats 1000000

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The quadratic form at the "vectorised identity" -/

/-- The vectorised identity matrix. -/
