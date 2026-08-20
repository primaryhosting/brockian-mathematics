import Mathlib
/-!
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type admits a well-order.

For any type `α` there exists a relation `r : α → α → Prop` which is a well-order
(`IsWellOrder α r`, i.e. `r` is trichotomous, transitive and well-founded).

This is exactly Mathlib's instance `IsWellOrder.subtype_nonempty`. -/

theorem wellordering (α : Type*) : Nonempty { r : α → α → Prop // IsWellOrder α r } :=
  IsWellOrder.subtype_nonempty

/-- An explicit unpacking of `SetTheory.wellordering`: every type carries a linear order
whose strict part `<` is well-founded. -/
