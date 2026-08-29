import Mathlib
/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem.** Every type admits a well-order: there exists a
relation `r` on `α` which is a well-order, i.e. a trichotomous, transitive, well-founded
relation (equivalently, a linear order on `α` whose strict order is well-founded). -/

theorem wellordering' (α : Type*) :
    ∃ r : α → α → Prop, Std.Trichotomous r ∧ IsTrans α r ∧ WellFounded r := by
  obtain ⟨r, hr⟩ := wellordering α
  exact ⟨r, hr.toTrichotomous, hr.toIsTrans, hr.wf⟩

/-- Every type admits a `LinearOrder` structure which is a well-order, i.e. whose strict
order `<` is well-founded. -/
