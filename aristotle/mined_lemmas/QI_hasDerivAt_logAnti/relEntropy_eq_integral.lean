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

theorem relEntropy_eq_integral (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    relEntropy ρ σ = ∫ t in Ioi (0 : ℝ), (Rval ρ σ t - (Matrix.trace ρ).re / (1 + t)) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => relIntegrand_eq_sum hρ hσ (le_of_lt ht))]
  rw [MeasureTheory.integral_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun i _ =>
      (integrableOn_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul _]
  rw [relEntropy_eq_sum hρ.isHermitian hσ.isHermitian]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finset_sum _ fun i _ =>
    (integrableOn_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_const_mul,
    integral_scalar (hρ.eigenvalues_pos j) (hσ.eigenvalues_pos i)]

end QI

import RequestProject.QI.Basic

/-!
# A variational quantity that is monotone under quantum channels

For positive semidefinite matrices `ρ σ` and a parameter `t ≥ 0` we consider the quadratic
functional
`Qform ρ σ t B = 2 Re tr(ρ B) - Re tr(Bᴴ σ B) - t Re tr(Bᴴ B ρ)`
and its supremum `Rval ρ σ t = ⨆ B, Qform ρ σ t B`.

In terms of the relative modular operator `Δ X = σ X ρ⁻¹` acting on the Hilbert–Schmidt space,
`Rval ρ σ t = ⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫`; the supremum is attained at the solution `B₀`
of the Sylvester equation `σ B₀ + t B₀ ρ = ρ`.

The main results are:

* `QI.Qform_le_of_sylvester`, `QI.Qform_eq_of_sylvester`: a solution of the Sylvester
  equation maximises `Qform`, with value `Re tr(ρ B₀)`;
* `QI.Qform_apply_le`: `Qform (Φ ρ) (Φ σ) t B ≤ Qform ρ σ t (Φ* B)` for a channel `Φ`
  (a consequence of the Kadison–Schwarz inequality);
* `QI.Rval_apply_le`: `Rval (Φ ρ) (Φ σ) t ≤ Rval ρ σ t`, i.e. `Rval` is monotone under
  quantum channels.
-/

namespace QI

open Matrix
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- The quadratic functional whose supremum is the resolvent form of the relative modular
operator. -/
