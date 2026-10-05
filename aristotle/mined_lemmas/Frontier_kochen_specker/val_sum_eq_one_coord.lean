import Mathlib

/-!
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The state space of a single quantum system of (Hilbert space) dimension `4`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- A *noncontextual hidden-variable assignment* (a Kochen–Specker colouring) is a map that
assigns to every unit vector (equivalently, to every rank-one orthogonal projection) a
definite truth value `0`/`1`, in such a way that for every orthonormal basis exactly one
basis vector receives the value `1`.

Note that in dimension `4` an orthonormal family indexed by `Fin 4` is automatically an
orthonormal *basis* (see `Frontier.orthonormal_four_spans`), so the quantification below is
exactly the quantification over all orthonormal bases. -/

theorem val_sum_eq_one_coord {f : E4 → Bool} (hf : KSAssignment f)
    (a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4 : ℝ)
    (h : (a1 * a1 + a2 * a2 + a3 * a3 + a4 * a4 ≠ 0) ∧
         (b1 * b1 + b2 * b2 + b3 * b3 + b4 * b4 ≠ 0) ∧
         (c1 * c1 + c2 * c2 + c3 * c3 + c4 * c4 ≠ 0) ∧
         (d1 * d1 + d2 * d2 + d3 * d3 + d4 * d4 ≠ 0) ∧
         (a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4 = 0) ∧
         (a1 * c1 + a2 * c2 + a3 * c3 + a4 * c4 = 0) ∧
         (a1 * d1 + a2 * d2 + a3 * d3 + a4 * d4 = 0) ∧
         (b1 * c1 + b2 * c2 + b3 * c3 + b4 * c4 = 0) ∧
         (b1 * d1 + b2 * d2 + b3 * d3 + b4 * d4 = 0) ∧
         (c1 * d1 + c2 * d2 + c3 * d3 + c4 * d4 = 0)) :
    val f (!₂[a1, a2, a3, a4] : E4) + val f (!₂[b1, b2, b3, b4] : E4)
      + val f (!₂[c1, c2, c3, c4] : E4) + val f (!₂[d1, d2, d3, d4] : E4) = 1 := by
  obtain ⟨ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd⟩ := h
  exact val_sum_eq_one hf _ _ _ _ (vec_ne_zero ha) (vec_ne_zero hb) (vec_ne_zero hc)
    (vec_ne_zero hd) (by rw [inner_vec]; exact hab) (by rw [inner_vec]; exact hac)
    (by rw [inner_vec]; exact had) (by rw [inner_vec]; exact hbc) (by rw [inner_vec]; exact hbd)
    (by rw [inner_vec]; exact hcd)

/-!
## The Kochen–Specker theorem

We use the 18-vector, 9-basis configuration of Cabello, Estebaranz and García-Alcaine in
`ℝ⁴`.  Each of the eighteen vectors occurs in exactly two of the nine orthogonal bases.
Summing "exactly one `1` per basis" over the nine bases gives `9`, but the same sum counts
each vector twice, hence is even — a contradiction.
-/

/-- **Kochen–Specker theorem** (dimension four, the base case of the statement in every
dimension `≥ 3`).

There is no noncontextual hidden-variable assignment for a quantum system of dimension `4`:
no `{0,1}`-valued function on unit vectors can assign the value `1` to exactly one member of
every orthonormal basis. -/
