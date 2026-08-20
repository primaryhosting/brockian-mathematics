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

theorem Gfun_krausMap_le (hK : IsTracePreserving K) (hρ : ρ.PosSemidef) (hσ : σ.PosDef)
    (ht : 0 ≤ t) :
    Gfun (krausMap K ρ) (krausMap K σ) t ≤ Gfun ρ σ t := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨X, rfl⟩
  refine le_trans (energy_krausMap_le hK hρ hσ.posSemidef ht X) ?_
  exact le_csSup (bddAbove_energy hρ hσ ht) ⟨krausDual K X, rfl⟩

end Mono

end QI

import RequestProject.QI.Variational

/-!
# Spectral formula for the relative entropy

`relEntropy ρ σ` is expressed through the eigenvalues of `ρ` and `σ` and the overlap matrix
of their eigenbases.  This is the classical relative entropy of the Nussbaum–Szkoła
distributions attached to the pair `(ρ, σ)`.
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Trace of a product of two matrices given by their spectral decompositions. -/
