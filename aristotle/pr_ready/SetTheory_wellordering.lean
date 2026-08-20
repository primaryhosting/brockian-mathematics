/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Statement: Every type admits a well-order: for any type alpha, there exists a linear order and a well-founded relation on alpha (Zermelo's well-ordering theorem). Prove: for all alpha, Nonempty { r : alpha -> alpha -> Prop // IsWellOrder alpha r }. (Use Mathlib's well-ordering / IsWellOrder existence.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace SetTheory

/-- **Zermelo's well-ordering theorem.** Every type `α` admits a well-order: there exists a
relation `r` on `α` which is a `IsWellOrder`, i.e. a trichotomous, transitive, well-founded
relation (equivalently, a linear order whose `<` is well-founded). -/
theorem wellordering (α : Type*) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  IsWellOrder.subtype_nonempty

/-- Explicit form: every type carries a linear order for which `<` is well-founded. -/
theorem exists_linearOrder_wellFoundedLT (α : Type*) :
    ∃ _ : LinearOrder α, WellFoundedLT α :=
  exists_wellOrder α

/-- Unbundled consequence: every type admits a relation which is a linear order (trichotomous
and transitive) and is well founded. -/
theorem exists_wellOrder_relation (α : Type*) :
    ∃ r : α → α → Prop, Std.Trichotomous r ∧ IsTrans α r ∧ WellFounded r := by
  obtain ⟨r, hr⟩ := wellordering α
  exact ⟨r, inferInstance, inferInstance, hr.wf⟩

end SetTheory

