import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/

theorem rank_omega_le : rank ZFSet.omega.{u} ≤ Ordinal.omega0 := by
  show PSet.rank PSet.omega ≤ _
  rw [PSet.omega, PSet.rank]
  refine Ordinal.iSup_le fun a => ?_
  rw [rank_ofNat]
  exact Order.succ_le_of_lt (Ordinal.nat_lt_omega0 _)

