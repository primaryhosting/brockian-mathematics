import Mathlib

/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace SetTheory

/-- **Zermelo's well-ordering theorem.** Every type `α` admits a well-order: there exists a
relation `r` on `α` which is a `IsWellOrder`, i.e. a trichotomous, transitive, well-founded
relation (equivalently, a linear order whose `<` is well-founded). -/

theorem exists_wellOrder_relation (α : Type*) :
    ∃ r : α → α → Prop, Std.Trichotomous r ∧ IsTrans α r ∧ WellFounded r := by
  obtain ⟨r, hr⟩ := wellordering α
  exact ⟨r, inferInstance, inferInstance, hr.wf⟩

end SetTheory

