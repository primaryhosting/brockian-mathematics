import Mathlib

set_option maxHeartbeats 1000000

/-!
# Common machinery for the Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for a quantum system with Hilbert space `E`
assigns to every unit vector (equivalently, to every rank-one projection, i.e. to every
"yes/no question" about the system) a definite truth value, in a way that does not depend on
the context in which the corresponding measurement is performed, and which respects the
quantum-mechanical sum rule: in every complete family of mutually orthogonal rank-one
projections — that is, in every orthonormal basis — exactly one projection is assigned the
value `true`.

We model such an assignment by a function `f : E → Bool`, the sum rule being the hypothesis
`∀ b : Fin n → E, Orthonormal ℝ b → ∃! i, f (b i) = true` (in an `n`-dimensional space an
orthonormal family indexed by `Fin n` is exactly an orthonormal basis).

This file collects the pieces used in dimensions three and four.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- "Exactly one `true`" in a triple, expressed as a count. -/

lemma inner_cr_self (u v : E3) : ⟪cr u v, cr u v⟫ = ⟪u, u⟫ * ⟪v, v⟫ - ⟪u, v⟫ ^ 2 := by
  rw [inner_e3 (cr u v), inner_e3 u u, inner_e3 v v, inner_e3 u v,
    (cr_apply u v).1, (cr_apply u v).2.1, (cr_apply u v).2.2]; ring

/-- The counting relation attached to an orthogonal triple of nonzero vectors. -/
