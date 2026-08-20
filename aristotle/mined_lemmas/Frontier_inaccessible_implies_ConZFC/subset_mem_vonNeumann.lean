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

theorem subset_mem_vonNeumann {o : Ordinal.{u}} {x y : ZFSet.{u}} (h : x ⊆ y)
    (hy : y ∈ vonNeumann o) : x ∈ vonNeumann o :=
  mem_vonNeumann_of_subset h hy

