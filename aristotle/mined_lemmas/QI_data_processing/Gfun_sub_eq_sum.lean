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

theorem Gfun_sub_eq_sum (hρ : ρ.PosSemidef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    Gfun ρ σ t - (Matrix.trace ρ).re / (1 + t)
      = ∑ k, ∑ j, entropyIntegrand hρ hσ k j t := by
  rw [Gfun_spectral hρ hσ ht, trace_re_eq_sum_eigenvalues hρ, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∑ j, entropyIntegrand hρ hσ k j t
      = (∑ j, eigenOverlap hρ.isHermitian hσ.isHermitian j k *
          ((hρ.isHermitian.eigenvalues k) ^ 2 /
            (hσ.isHermitian.eigenvalues j + t * hρ.isHermitian.eigenvalues k))) -
        (∑ j, eigenOverlap hρ.isHermitian hσ.isHermitian j k) *
          (hρ.isHermitian.eigenvalues k / (1 + t)) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp only [entropyIntegrand]; ring
  rw [e, sum_eigenOverlap hρ.isHermitian hσ.isHermitian k, one_mul]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

