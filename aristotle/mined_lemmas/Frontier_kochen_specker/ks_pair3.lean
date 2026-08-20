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

lemma ks_pair3 (f : E3 → Bool)
    (h : ∀ b : Fin 3 → E3, Orthonormal ℝ b → ∃! i, f (b i) = true)
    (w0 w1 : E3) (n0 : ⟪w0, w0⟫ ≠ 0) (n1 : ⟪w1, w1⟫ ≠ 0) (h01 : ⟪w0, w1⟫ = 0) :
    (f (nrm w0)).toNat + (f (nrm w1)).toNat ≤ 1 := by
  have h2 : ⟪cr w0 w1, cr w0 w1⟫ ≠ 0 := by
    rw [inner_cr_self, h01]
    simpa using mul_ne_zero n0 n1
  have := ks_ctx3 f h w0 w1 (cr w0 w1) n0 n1 h2 h01 (inner_cr_left w0 w1) (inner_cr_right w0 w1)
  omega

/-- `√2`. -/
