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


theorem measInfo_le_holevoChi {p : X → ℝ} {ρ : X → Matrix n n ℂ} {E : Y → Matrix n n ℂ}
    (hens : IsEnsemble p ρ) (hE : IsPOVM E) (hcomm : ∀ x x', Commute (ρ x) (ρ x')) :
    measInfo p ρ E ≤ holevoChi p ρ :=
  measInfo_le_holevoChi_of_jointlyDiagonalizable hens hE
    (jointlyDiagonalizable_of_commute ρ (fun x => (hens.state x).psd.1) hcomm)

/-- **Holevo bound**: the accessible information of an ensemble of pairwise commuting states is
at most its Holevo χ quantity. -/
