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

theorem energy_krausMap_le (hK : IsTracePreserving K) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef)
    (ht : 0 ≤ t) (X : Matrix m m ℂ) :
    energy (krausMap K ρ) (krausMap K σ) t X ≤ energy ρ σ t (krausDual K X) := by
  have hlin : Matrix.trace (krausMap K ρ * X) = Matrix.trace (ρ * krausDual K X) := by
    rw [Matrix.trace_mul_comm (krausMap K ρ) X, ← trace_krausDual_mul K X ρ,
      Matrix.trace_mul_comm]
  have h2 : (Matrix.trace ((krausDual K X)ᴴ * krausDual K X * ρ)).re
      ≤ (Matrix.trace (Xᴴ * X * krausMap K ρ)).re := by
    have hmono := trace_mul_re_mono (kadison_schwarz hK X) hρ
    rw [trace_krausDual_mul K (Xᴴ * X) ρ] at hmono
    exact hmono
  have h1 : (Matrix.trace ((krausDual K X)ᴴ * σ * krausDual K X)).re
      ≤ (Matrix.trace (Xᴴ * krausMap K σ * X)).re := by
    have hks := kadison_schwarz hK Xᴴ
    simp only [krausDual_conjTranspose, Matrix.conjTranspose_conjTranspose] at hks
    have hmono := trace_mul_re_mono hks hσ
    rw [trace_krausDual_mul K (X * Xᴴ) σ] at hmono
    have e1 : Matrix.trace ((krausDual K X)ᴴ * σ * krausDual K X)
        = Matrix.trace (krausDual K X * (krausDual K X)ᴴ * σ) := by
      rw [Matrix.trace_mul_comm ((krausDual K X)ᴴ * σ) (krausDual K X), ← Matrix.mul_assoc]
    have e2 : Matrix.trace (X * Xᴴ * krausMap K σ) = Matrix.trace (Xᴴ * krausMap K σ * X) := by
      rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    rw [e1, ← e2, krausDual_conjTranspose]
    exact hmono
  simp only [energy, hlin]
  have := mul_le_mul_of_nonneg_left h2 ht
  linarith [h1, this]

