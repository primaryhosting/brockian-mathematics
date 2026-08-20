import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/

theorem kadison_schwarz {K : ι → Matrix m n ℂ} (hK : IsTracePreserving K) (X : Matrix m m ℂ) :
    (krausDual K (Xᴴ * X) - (krausDual K X)ᴴ * (krausDual K X)).PosSemidef := by
  have h1 := kadison_schwarz_isometry (krausStack K) (krausStack_isometry hK)
    (Matrix.blockDiagonal fun _ : ι => X)
  rw [← krausDual_eq_stack K X] at h1
  have h2 : (Matrix.blockDiagonal fun _ : ι => X)ᴴ * (Matrix.blockDiagonal fun _ : ι => X)
      = Matrix.blockDiagonal fun _ : ι => Xᴴ * X := by
    rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
  rw [h2, ← krausDual_eq_stack K (Xᴴ * X)] at h1
  exact h1

end QI

import Mathlib

/-!
# Basic definitions for the quantum data-processing inequality

We work with finite dimensional quantum systems, described by complex matrices.

* `QI.relEntropy ρ σ` is the Umegaki quantum relative entropy `Tr ρ (log ρ - log σ)`,
  where the matrix logarithm is the continuous functional calculus applied to `Real.log`.
* `QI.krausMap K` is the quantum channel with Kraus operators `K`,
  and `QI.krausDual K` is its adjoint (Heisenberg picture) map.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- The Umegaki quantum relative entropy `Tr ρ (log ρ - log σ)`. -/
