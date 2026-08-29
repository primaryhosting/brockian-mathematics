/-
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- comment and is repeated as the module docstring below.)

import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
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

namespace QI

open scoped ComplexConjugate

variable {m n : ℕ}

/-- The amplitude matrix of a bipartite pure state, i.e. its coordinates in the product basis. -/

lemma orthonormal_iff_coord {r : ℕ} {ι : Type*} [Fintype ι] (e : Fin r → EuclideanSpace ℂ ι) :
    Orthonormal ℂ e ↔ ∀ i j, ∑ p, conj (e i p) * e j p = if i = j then (1 : ℂ) else 0 := by
  rw [orthonormal_iff_ite (𝕜 := ℂ)]
  constructor
  · intro h i j; rw [← inner_coord]; exact h i j
  · intro h i j; rw [inner_coord]; exact h i j

