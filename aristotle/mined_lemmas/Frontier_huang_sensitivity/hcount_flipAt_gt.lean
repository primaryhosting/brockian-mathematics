import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

namespace Frontier

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/

lemma hcount_flipAt_gt (x : Cube n) {i k : Fin n} (h : i < k) :
    hcount (flipAt x i) k = hcount x k := by
  unfold hcount
  congr 1
  apply Finset.filter_congr
  intro j _
  have hj : ∀ _hjk : k < j, j ≠ i := fun hjk => ne_of_gt (lt_trans h hjk)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (hj h1)] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (hj h1)]⟩

