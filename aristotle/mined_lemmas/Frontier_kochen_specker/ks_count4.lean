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

lemma ks_count4 {E : Type*} (f : E → Bool) (u : Fin 4 → E) (h : ∃! i, f (u i) = true) :
    (f (u 0)).toNat + (f (u 1)).toNat + (f (u 2)).toNat + (f (u 3)).toNat = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j, j ≠ i → f (u j) = false := by
    intro j hj
    by_contra hc
    exact hj (hu j (by simpa using hc))
  fin_cases i <;> simp_all

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Normalisation of a vector (the zero vector is mapped to itself). -/
