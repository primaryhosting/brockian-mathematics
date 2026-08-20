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


theorem holevo_bound_of_jointlyDiagonalizable {p : X → ℝ} {ρ : X → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hdiag : JointlyDiagonalizable ρ) :
    accessibleInfo p ρ ≤ holevoChi p ρ := by
  refine csSup_le ?_ ?_
  · refine ⟨measInfo p ρ (fun _ : Fin 1 => (1 : Matrix n n ℂ)), 1,
      (fun _ : Fin 1 => (1 : Matrix n n ℂ)), ⟨fun _ => Matrix.PosSemidef.one, by simp⟩, rfl⟩
  · rintro b ⟨m, E, hE, rfl⟩
    exact measInfo_le_holevoChi_of_jointlyDiagonalizable hens hE hdiag

end QI

import Mathlib

/-!
# Classical information-theoretic core

This file develops the elementary classical facts that underlie the Holevo bound:

* `QI.shannonEntropy` : Shannon entropy of a finite probability vector;
* `QI.relEntropy` : the Kullback-Leibler divergence of two finite nonnegative vectors;
* `QI.log_sum_ineq` : the log-sum inequality;
* `QI.relEntropy_channel_le` : the data-processing inequality for the KL divergence
  under a classical (column-stochastic) channel;
* `QI.mutualInfo_eq_sum_relEntropy` : mutual information as an average divergence;
* `QI.classical_holevo` : the classical Holevo/data-processing bound.

All entropies use natural logarithms (nats).
-/

open scoped BigOperators

namespace QI

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]

/-- Shannon entropy of a finite (probability) vector, in nats. -/
