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

theorem preBeth_lt_of_isInaccessible (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → preBeth o < κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
    intro ho
    rw [Cardinal.preBeth]
    have he : (⨆ a : Iio o, (2 : Cardinal.{u}) ^ preBeth a)
        = ⨆ i : o.ToType, (2 : Cardinal.{u}) ^ preBeth ((Ordinal.ToType.mk (o := o)).symm i) :=
      (Equiv.iSup_comp (g := fun a : Iio o => (2 : Cardinal.{u}) ^ preBeth a)
        (Ordinal.ToType.mk (o := o)).symm.toEquiv).symm
    rw [he]
    refine Ordinal.iSup_lt ?_ fun i => ?_
    · rw [mk_toType, hκ.isRegular.cof_eq]
      exact Cardinal.lt_ord.mp ho
    · exact hκ.isStrongLimit.two_power_lt (IH _ ((Ordinal.ToType.mk (o := o)).symm i).2
        (((Ordinal.ToType.mk (o := o)).symm i).2.trans ho))

/-- Every set in `V_κ` has cardinality less than `κ`, for `κ` inaccessible. -/
