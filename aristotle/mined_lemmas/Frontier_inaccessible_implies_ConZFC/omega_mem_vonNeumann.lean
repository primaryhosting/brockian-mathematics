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

theorem omega_mem_vonNeumann (hκ : κ.IsInaccessible) : ZFSet.omega.{u} ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann]
  refine rank_omega_le.trans_lt ?_
  have : (ℵ₀ : Cardinal.{u}).ord < κ.ord := Cardinal.ord_lt_ord.mpr hκ.aleph0_lt
  rwa [Cardinal.ord_aleph0] at this

/-- Replacement: `V_κ` is closed under images of its elements, for `κ` inaccessible.  This is
where the regularity of `κ` is used. -/
