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

def LSet : Language := ⟨fun _ => Empty, memRel⟩

/-- Any `ZFSet` is an `LSet`-structure, with the relation symbol interpreted as membership. -/
instance zfStructure (A : ZFSet.{u}) : LSet.Structure A where
  funMap {_} f := Empty.elim f
  RelMap {n} r := match n, r with
    | 2, .mem => fun v => ((v 0 : A) : ZFSet) ∈ ((v 1 : A) : ZFSet)

/-- `t₁ ∈ t₂` as a bounded formula of `LSet`. -/
