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

lemma count_eq_one {A : Type*} (F : A → Bool) (v : Fin 4 → A)
    (h : ∃! i, F (v i) = true) :
    (if F (v 0) = true then 1 else 0) + (if F (v 1) = true then 1 else 0) +
      (if F (v 2) = true then 1 else 0) + (if F (v 3) = true then 1 else 0) = 1 := by
  obtain ⟨i, hi, hu⟩ := h
  have key : ∀ j : Fin 4, F (v j) = true ↔ j = i :=
    fun j => ⟨fun hj => hu j hj, fun hj => hj ▸ hi⟩
  rw [if_congr (key 0) rfl rfl, if_congr (key 1) rfl rfl, if_congr (key 2) rfl rfl,
    if_congr (key 3) rfl rfl]
  fin_cases i <;> decide

/-- Normalising an orthogonal frame yields an orthonormal family. -/
