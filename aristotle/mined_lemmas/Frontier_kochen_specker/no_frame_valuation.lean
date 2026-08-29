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

theorem no_frame_valuation (F : EuclideanSpace ℝ (Fin 4) → Bool) :
    ¬ ∀ v : Fin 4 → EuclideanSpace ℝ (Fin 4), OrthFrame v → ∃! i, F (v i) = true := by
  intro h
  set x : Fin 18 → ℕ := fun k => if F (ksv k) = true then 1 else 0 with hx
  have e : ∀ j : Fin 9, x (ksb j 0) + x (ksb j 1) + x (ksb j 2) + x (ksb j 3) = 1 :=
    fun j => count_eq_one F _ (h _ (ksb_orthFrame j))
  have e0 := e 0
  have e1 := e 1
  have e2 := e 2
  have e3 := e 3
  have e4 := e 4
  have e5 := e 5
  have e6 := e 6
  have e7 := e 7
  have e8 := e 8
  simp only [ksb, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.cons_val] at e0 e1 e2 e3 e4 e5 e6 e7 e8
  omega

/-- **Kochen–Specker theorem** (base case, dimension four).
There is no noncontextual hidden-variable assignment: there is no function `f` assigning to
every vector of a four dimensional real Hilbert space a value in `{0, 1}` (here `Bool`),
depending on the vector alone and not on the measurement context, such that in every
orthonormal basis exactly one vector receives the value `1`. -/
