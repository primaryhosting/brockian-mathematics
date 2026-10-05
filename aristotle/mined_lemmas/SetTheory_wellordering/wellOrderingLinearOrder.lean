/-
# Wellordering
Category: Frontier Wave 2 (deeper machinery)
Target: SetTheory.wellordering
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace SetTheory

/-- **Zermelo's well-ordering theorem**: every type carries a well-order.
Formally, for any type `α` there exists a relation `r : α → α → Prop`
which is a well-order: it is trichotomous, transitive and well-founded,
and hence induces a linear order on `α`. -/

noncomputable def wellOrderingLinearOrder (α : Type*) : LinearOrder α :=
  linearOrderOfSTO (WellOrderingRel : α → α → Prop)

/-- The order-theoretic form of the well-ordering theorem: every type admits a
linear order whose strict part is well-founded. -/
