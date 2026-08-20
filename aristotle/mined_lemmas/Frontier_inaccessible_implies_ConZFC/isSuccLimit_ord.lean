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

theorem isSuccLimit_ord (hκ : κ.IsInaccessible) : IsSuccLimit κ.ord :=
  Cardinal.isSuccLimit_ord hκ.aleph0_lt.le

/-! ## Closure properties of `V_κ` for `κ` inaccessible -/

