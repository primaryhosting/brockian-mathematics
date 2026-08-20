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

theorem powerset_mem_vonNeumann (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x ∈ vonNeumann κ.ord) : x.powerset ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  rw [rank_powerset]
  exact (isSuccLimit_ord hκ).succ_lt hx

