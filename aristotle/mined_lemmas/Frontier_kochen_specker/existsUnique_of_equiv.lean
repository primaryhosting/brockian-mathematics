/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

The Kochen–Specker theorem states that in a Hilbert space of dimension at least three there is
no noncontextual hidden-variable assignment: one cannot assign to every ray a value in `{0, 1}`,
independently of the measurement context, in such a way that every orthonormal basis contains
exactly one ray of value `1`.

We formalise the four dimensional case, which is the base case admitting a purely combinatorial
(parity) proof, due to Cabello, Estebaranz and García-Alcaine: there are `18` vectors in
`ℝ⁴` arranged into `9` orthogonal frames so that every vector lies in exactly two frames.
Summing the value `1` over the nine frames counts each vector twice, giving `9 = 2 * k`,
which is impossible.

The main statement is `Frontier.kochen_specker`, with `Frontier.kochen_specker_basis` an
equivalent restatement in terms of `OrthonormalBasis`.
-/

set_option maxHeartbeats 1000000

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A family of four vectors which is *orthogonal and nondegenerate*: the inner product of
`v i` and `v j` vanishes exactly when `i ≠ j`.  Equivalently, the `v i` are nonzero and
pairwise orthogonal. -/

lemma existsUnique_of_equiv {A B : Type*} (e : A ≃ B) {p : A → Prop}
    (h : ∃! y, p (e.symm y)) : ∃! x, p x := by
  obtain ⟨y, hy, hu⟩ := h
  refine ⟨e.symm y, hy, fun x hx => ?_⟩
  have hxy : e x = y := hu (e x) (by simpa using hx)
  rw [← hxy, Equiv.symm_apply_apply]

/-- **Kochen–Specker theorem in every finite dimension `n ≥ 4`.**
If `E` is a real inner product space of finite dimension at least four, there is no
noncontextual assignment of values in `{0, 1}` (here `Bool`) to the vectors of `E` such that
every orthonormal basis of `E` contains exactly one vector of value `1`. -/
