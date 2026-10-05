/-
# Kochen Specker
Category: Frontier Physics
Target: Frontier.kochen_specker
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain comment and is repeated as the module docstring below.)

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## The Kochen–Specker theorem

A *noncontextual hidden-variable assignment* for quantum mechanics in dimension `d`
assigns, to every one-dimensional projector (equivalently, to every nonzero vector of
`ℝ^d`, or of `ℂ^d`), a definite truth value `0`/`1`, in a way that does not depend on
which measurement context the projector is being measured in.  The only constraint
imposed by quantum mechanics is that, for every orthogonal basis `b₀, …, b_{d-1}`
(i.e. every complete measurement context), *exactly one* of the corresponding
projectors gets the value `1`.

The Kochen–Specker theorem says that for `d ≥ 3` no such assignment exists.  Here we
formalize the theorem in dimension `d = 4`, which is the standard "base case" admitting
a short combinatorial proof: the 18-vector, 9-basis configuration of
Cabello–Estebaranz–García-Alcaine.  Each of the 18 vectors occurs in exactly two of the
9 orthogonal bases, so summing the "exactly one `1` per basis" constraint over the nine
bases gives `9 = 2 · (number of vectors valued 1)`, an odd number equal to an even one.

The vector space is modelled as `Fin 4 → ℝ` with the standard inner product
`⟪v, w⟫ = ∑ k, v k * w k`, and a context is any 4-tuple of pairwise orthogonal nonzero
vectors (necessarily an orthogonal basis of `ℝ⁴`).  The assignment is modelled as an
arbitrary function `f` from vectors to `Bool`; noncontextuality is expressed by the fact
that `f` depends only on the vector, not on the context in which it appears.
-/

namespace Frontier

/-- The 18 vectors of the Cabello–Estebaranz–García-Alcaine Kochen–Specker
configuration in `ℝ⁴`. -/

theorem kochen_specker :
    ¬ ∃ f : (Fin 4 → ℝ) → Bool,
        ∀ b : Fin 4 → (Fin 4 → ℝ),
          (∀ i, b i ≠ 0) →
          (∀ i j, i ≠ j → ∑ k, b i k * b j k = 0) →
          ∃! i, f (b i) = true := by
  rintro ⟨f, hf⟩
  have key : ∀ n : Fin 9, ∑ i, (if f (ksVec (ksBasis n i)) then 1 else 0) = 1 := fun n =>
    sum_indicator_eq_one _
      (hf (fun i => ksVec (ksBasis n i)) (ksVec_ne_zero n) (ksBasis_orthogonal n))
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  have h6 := key 6
  have h7 := key 7
  have h8 := key 8
  simp only [Fin.sum_univ_four, ksBasis, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  -- Each of the eighteen vectors occurs in exactly two bases, so the nine equations
  -- sum to `2 * (total number of vectors valued 1) = 9`, which is impossible.
  omega

/-!
## Every dimension `n ≥ 4`

The dimension-4 result propagates to all higher dimensions.  The naive argument — embed
a 4-dimensional context into `ℝⁿ` by padding it with fixed standard basis vectors — is
not quite enough, because the valuation could put the value `1` on one of the padding
vectors and `0` on everything in the 4-dimensional block.  This is ruled out by first
looking at the standard basis context: exactly one standard basis vector `e_{i₀}` is
valued `1`, so choosing the 4-dimensional block to *contain* the coordinate `i₀` (by
conjugating with the transposition swapping `i₀` and `0`) makes every padding vector
valued `0`.
-/

variable {n : ℕ}

/-- The vector of `ℝⁿ` obtained from a vector of `ℝ⁴` by placing its coordinates in the
four coordinates of `ℝⁿ` that the permutation `τ` sends to `0, 1, 2, 3`, and filling the
remaining coordinates with `0`. -/
