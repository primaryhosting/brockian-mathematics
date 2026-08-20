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

theorem Rval_apply_le (Φ : Channel n m ι) (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (ht : 0 ≤ t)
    {B₀ : Matrix n n ℂ} (hB₀ : σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ) :
    Rval (Φ.apply ρ) (Φ.apply σ) t ≤ Rval ρ σ t := by
  rw [Rval_eq_of_sylvester hρ hσ ht hB₀, ← Qform_eq_of_sylvester hρ.isHermitian hB₀]
  exact ciSup_le fun B =>
    le_trans (Qform_apply_le Φ hρ hσ ht B) (Qform_le_of_sylvester hρ hσ ht hB₀ _)

end QI

import Mathlib

/-!
# Basic finite-dimensional quantum-information setup

This file sets up:

* elementary facts about traces of products of positive semidefinite matrices;
* quantum channels in Kraus form (`QI.Channel`), their action `Φ.apply` on states and
  the adjoint (Heisenberg picture) map `Φ.adjoint`;
* the Kadison–Schwarz inequality for the adjoint map.

By the Choi–Kraus theorem, the maps of the form `Φ.apply` for `Φ : QI.Channel n m ι` are
exactly the completely positive trace preserving (CPTP) maps from `n × n` matrices to
`m × m` matrices.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-! ### Traces of products of positive semidefinite matrices -/

/-- The trace of a product of two positive semidefinite matrices is a nonnegative real. -/
