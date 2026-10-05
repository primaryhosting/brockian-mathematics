import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

lemma dimTwo_orthogonal_complement {P Q : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProj P)
    (hQ : IsProj Q) (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hP1 : P ≠ 1 := by
    rintro rfl; exact hQ0 (by simpa using hPQ)
  have hQ1 : Q ≠ 1 := by
    rintro rfl; exact hP0 (by simpa using hPQ)
  have htP : P.trace = 1 := ((dimTwo_proj_trichotomy hP).resolve_left hP0).resolve_left hP1
  have htQ : Q.trace = 1 := ((dimTwo_proj_trichotomy hQ).resolve_left hQ0).resolve_left hQ1
  have htsum : (P + Q).trace = 2 := by rw [Matrix.trace_add, htP, htQ]; norm_num
  rcases dimTwo_proj_trichotomy (hP.add hQ hPQ) with h | h | h
  · rw [h] at htsum; simp at htsum
  · exact h
  · rw [h] at htsum; norm_num at htsum

/-- The `(0,0)` entry of a `2 × 2` projection is real and, together with the `(0,1)` entry,
satisfies `a² + |b|² = a`. -/
