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

lemma orthonormal_nrm {ι : Type*} (v : ι → E) (hne : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : Orthonormal ℝ (fun i => nrm (v i)) := by
  constructor
  · intro i
    simpa [nrm] using norm_smul_inv_norm (𝕜 := ℝ) (hne i)
  · intro i j hij
    simp [nrm, real_inner_smul_left, real_inner_smul_right, ho i j hij]

end Frontier

import RequestProject.KSCore

/-!
# Kochen–Specker in dimension three (Peres' 33 rays)

This file rules out a noncontextual `{0,1}`-valued assignment on the unit vectors of `ℝ³`.
The configuration used is Peres' set of 33 rays, whose coordinates are `0, ±1, ±√2`.
Thirteen of the orthogonal triples of the configuration must each carry exactly one `true`,
and 33 further orthogonal pairs of rays cannot both carry `true` (any orthogonal pair extends,
via the cross product, to an orthogonal triple).  These 46 constraints are contradictory.
-/

namespace Frontier

open scoped RealInnerProductSpace

/-- Three-dimensional real Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The real inner product on `E3`, in coordinates. -/
