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

theorem relEntropy_spectral {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy ρ σ =
      ∑ k, ∑ j, eigenOverlap hρ hσ j k *
        (hρ.eigenvalues k * Real.log (hρ.eigenvalues k) -
          hρ.eigenvalues k * Real.log (hσ.eigenvalues j)) := by
  simp only [eigenOverlap]
  have hcol := fun k => sum_norm_sq_col _ (eigen_overlap_isometry hρ hσ) k
  rw [relEntropy, trace_mul_cfc_log_self hρ, trace_mul_cfc_log_other hρ hσ,
    ← Complex.ofReal_sub, Complex.ofReal_re, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
        (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2 *
        (hρ.eigenvalues k * Real.log (hρ.eigenvalues k) -
          hρ.eigenvalues k * Real.log (hσ.eigenvalues j))
      = (∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2) *
          (hρ.eigenvalues k * Real.log (hρ.eigenvalues k)) -
        ∑ j, ‖((hσ.eigenvectorUnitary : Matrix n n ℂ)ᴴ *
          (hρ.eigenvectorUnitary : Matrix n n ℂ)) j k‖ ^ 2 *
          (hρ.eigenvalues k * Real.log (hσ.eigenvalues j)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, hcol k, one_mul]

end QI

import RequestProject.QI.Entropy
import RequestProject.QI.ScalarIntegral

/-!
# Integral representation of the relative entropy

`relEntropy ρ σ = ∫_0^∞ (Gfun ρ σ t - (Tr ρ) / (1 + t)) dt` for `ρ` positive semidefinite and
`σ` positive definite.
-/

set_option maxHeartbeats 1000000

open Matrix MeasureTheory Filter Set
open scoped ComplexOrder MatrixOrder Topology

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ σ : Matrix n n ℂ}

/-- The `(k, j)` term of the integrand. -/
