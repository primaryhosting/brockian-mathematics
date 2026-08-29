import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

lemma ngonEigen_five_two : ngonEigen 5 2 = -(1 + Real.sqrt 5) / 2 := by
  have hval : (2 : ZMod 5).val = 2 := by decide
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hx : (2 : ℝ) * Real.pi * ((2 : ZMod 5).val : ℝ) / (5 : ℕ) = 2 * (2 * (Real.pi / 5)) := by
    rw [hval]; push_cast; ring
  rw [ngonEigen, hx, Real.cos_two_mul, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

end Pentagon

/-- Generalisation of the `D₅` pentagon isotypic decomposition to arbitrary `n`-gons.

For every `n ≥ 1` and every `j : ZMod n`:
* the isotypic component `ngonIsotypic n j = span {χ_j, χ_{-j}}` is invariant under all
  rotations of the `n`-gon and under the reflection, i.e. it is a `D_n`-subrepresentation;
* the cycle adjacency operator acts on it as the scalar `2 cos (2π j / n)`;
* when `j ≠ -j` the two characters are linearly independent, so the component has
  dimension exactly `2` (an irreducible two-dimensional `D_n`-representation).

Specialising to the pentagon `n = 5` recovers the two golden-ratio eigenvalues
`(√5 - 1)/2` (for `j = 1`) and `-(1 + √5)/2` (for `j = 2`). -/
