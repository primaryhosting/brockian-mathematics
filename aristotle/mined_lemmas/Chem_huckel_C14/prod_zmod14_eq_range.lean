/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The standard additive character `ZMod 14 → ℂ`, `j ↦ exp (2πI j / 14)`. -/

lemma prod_zmod14_eq_range {M : Type*} [CommMonoid M] (g : ZMod 14 → M) :
    ∏ k : ZMod 14, g k = ∏ k ∈ Finset.range 14, g (k : ZMod 14) := by
  refine Finset.prod_nbij' (fun k => k.val) (fun k => (k : ZMod 14)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simpa using ZMod.val_lt a
  · intro a _; exact Finset.mem_univ _
  · intro a _; simp
  · intro a ha; exact ZMod.val_natCast_of_lt (Finset.mem_range.mp ha)
  · intro a _; simp

/-! ### Main theorem -/

/-- **Hückel theory for `C₁₄`.**  The adjacency matrix of the cycle graph `C₁₄` has
eigenvalues `2 cos (2πk/14)` for `k = 0, …, 13`:  each vector
`j ↦ exp (2πI jk/14)` is a nonzero eigenvector with eigenvalue `2 cos (2πk/14)`, and the
characteristic polynomial of the adjacency matrix is exactly
`∏_{k=0}^{13} (X - 2 cos (2πk/14))`, so there are no other eigenvalues. -/
