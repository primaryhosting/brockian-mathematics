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

lemma padv_ne_zero (hn : 4 ≤ n) (τ : Equiv.Perm (Fin n)) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    padv τ v ≠ 0 := by
  obtain ⟨m, hm⟩ := Function.ne_iff.1 hv
  refine Function.ne_iff.2 ⟨τ.symm (Fin.castLE hn m), ?_⟩
  rw [padv_apply hn]
  simpa using hm

/-- Padding preserves inner products. -/
