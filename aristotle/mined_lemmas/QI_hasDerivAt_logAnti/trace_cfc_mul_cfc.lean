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

theorem trace_cfc_mul_cfc {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (f g : ℝ → ℝ) :
    Matrix.trace (cfc f ρ * cfc g σ)
      = ((∑ j, ∑ i, f (hρ.eigenvalues j) * g (hσ.eigenvalues i) *
          ‖((star (hσ.eigenvectorUnitary : Matrix n n ℂ)) *
            (hρ.eigenvectorUnitary : Matrix n n ℂ)) i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [cfc_eq_conj hρ f, cfc_eq_conj hσ g, trace_conj_diag, trace_diag_conj]
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Function.comp_apply,
    show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
  rw [conj_mul_self]
  push_cast
  ring

variable {ρ σ : Matrix n n ℂ}

/-- The overlap matrix `W = V* U` between the eigenbases of `ρ` (columns of `U`) and of `σ`
(columns of `V`). -/
