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

theorem sUnion_mem_vonNeumann {o : Ordinal.{u}} {x : ZFSet.{u}} (hx : x ∈ vonNeumann o) :
    (⋃₀ x) ∈ vonNeumann o := by
  rw [ZFSet.mem_vonNeumann] at *
  exact (rank_sUnion_le x).trans_lt hx

