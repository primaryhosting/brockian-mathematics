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

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/

theorem kadison_schwarz' (Y : Matrix m m ℂ) :
    (Φ.adjoint (Y * Yᴴ) - Φ.adjoint Y * (Φ.adjoint Y)ᴴ).PosSemidef := by
  have h := Φ.kadison_schwarz (Yᴴ)
  rwa [Matrix.conjTranspose_conjTranspose, Φ.adjoint_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at h

end Channel

end QI

import RequestProject.QI.Variational

/-!
# Quantum relative entropy and its spectral formulas

This file defines the matrix logarithm `QI.mlog` (via the continuous functional calculus) and
the Umegaki relative entropy

`QI.relEntropy ρ σ = Re tr (ρ (log ρ - log σ))`.

It then computes, for positive definite `ρ σ`, both `relEntropy ρ σ` and the variational
quantity `QI.Rval ρ σ t` in terms of the spectral data of `ρ` and `σ`:
if `ρ = U diag(p) U*`, `σ = V diag(q) V*` and `W = V* U`, then

* `relEntropy ρ σ = ∑ i j, ‖W i j‖² * (p j * (log (p j) - log (q i)))`,
* `Rval ρ σ t = ∑ i j, ‖W i j‖² * (p j ^ 2 / (q i + t * p j))`.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix logarithm of a hermitian matrix, defined by the continuous functional calculus.
(Recall the junk-value convention `Real.log 0 = 0`.) -/
