/-
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type admits a well-order, i.e. a relation on `α`
which is `IsWellOrder` (trichotomous, transitive, and well-founded), and hence induces a linear
order on `α`.

Closed by Mathlib's instance `IsWellOrder.subtype_nonempty`. -/

theorem exists_wellorder (α : Type*) :
    ∃ r : α → α → Prop, Std.Trichotomous r ∧ IsTrans α r ∧ WellFounded r := by
  obtain ⟨r, hr⟩ := wellordering α
  exact ⟨r, hr.toTrichotomous, hr.toIsTrans, hr.wf⟩

/-- Every type carries a linear order whose `<` relation is well-founded. -/
