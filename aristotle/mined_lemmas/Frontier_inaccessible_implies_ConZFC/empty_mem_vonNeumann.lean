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

theorem empty_mem_vonNeumann (hκ : κ.IsInaccessible) : (∅ : ZFSet.{u}) ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, rank_empty]
  exact (isSuccLimit_ord hκ).bot_lt

