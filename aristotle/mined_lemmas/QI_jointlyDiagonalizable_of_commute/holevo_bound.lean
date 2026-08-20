import Mathlib
import RequestProject.Holevo

/-!
# Simultaneous diagonalization of a commuting family of Hermitian matrices

The main result `QI.jointlyDiagonalizable_of_commute` shows that a family of pairwise commuting
Hermitian matrices is diagonal in a common orthonormal basis, i.e. satisfies
`QI.JointlyDiagonalizable`.
-/

open Matrix LinearMap
open scoped Function

namespace QI

variable {n X : Type*} [Fintype n] [DecidableEq n]


theorem holevo_bound {p : X → ℝ} {ρ : X → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    accessibleInfo p ρ ≤ holevoChi p ρ :=
  holevo_bound_of_jointlyDiagonalizable hens
    (jointlyDiagonalizable_of_commute ρ (fun x => (hens.state x).psd.1) hcomm)

end QI

import Mathlib
import RequestProject.ClassicalInfo

/-!
# The Holevo bound

Finite-dimensional quantum states are modelled as positive semidefinite complex matrices of
unit trace, measurements as POVMs, and the von Neumann entropy through the eigenvalues of the
density matrix.

The main results are:

* `QI.measInfo_le_holevoChi_of_jointlyDiagonalizable` : the mutual information between the
  classical label of an ensemble and the outcome of *any* POVM measurement performed on it is at
  most the Holevo χ quantity of the ensemble;
* `QI.holevo_bound_of_jointlyDiagonalizable` : the accessible information of an ensemble (the
  supremum of the above over all POVMs) is at most its Holevo χ quantity.

The versions phrased for commuting ensembles, `QI.measInfo_le_holevoChi` and `QI.holevo_bound`,
are in `RequestProject.SimulDiag`.

**Scope.** Both results are proved here for ensembles whose states share a common orthonormal
eigenbasis (`QI.JointlyDiagonalizable`), equivalently for ensembles of pairwise commuting states;
the measurement is an arbitrary POVM. The proof reduces the bound, via the joint spectral
decomposition, to the classical data-processing inequality `QI.classical_holevo`.
The general (noncommuting) case of Holevo's theorem rests on the monotonicity of the quantum
relative entropy under measurements, which is not available in Mathlib and is not developed here.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace QI

variable {n X Y : Type*} [Fintype n] [DecidableEq n] [Fintype X] [Fintype Y]

/-! ### Basic definitions -/

/-- A finite-dimensional quantum state (density matrix). -/
structure IsState (ρ : Matrix n n ℂ) : Prop where
  psd : ρ.PosSemidef
  trace_one : ρ.trace = 1

/-- A POVM with outcomes in `Y`. -/
structure IsPOVM (E : Y → Matrix n n ℂ) : Prop where
  psd : ∀ y, (E y).PosSemidef
  sum_eq_one : ∑ y, E y = 1

/-- An ensemble: a probability distribution `p` on `X` together with states `ρ x`. -/
structure IsEnsemble (p : X → ℝ) (ρ : X → Matrix n n ℂ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x, p x = 1
  state : ∀ x, IsState (ρ x)

/-- The von Neumann entropy (in nats) of a density matrix, defined as the Shannon entropy of its
spectrum. -/
