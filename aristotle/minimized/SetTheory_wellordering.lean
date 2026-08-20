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

theorem wellordering (α : Type*) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  IsWellOrder.subtype_nonempty

/-- Explicit form: every type carries a linear order for which `<` is well-founded. -/
