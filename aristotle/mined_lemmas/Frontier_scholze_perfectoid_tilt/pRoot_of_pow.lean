/-
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Scholze Perfectoid Tilt
Category: Frontier — Fields Medal Work
Target: Frontier.scholze_perfectoid_tilt
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

/-! ## The tilt: inverse limit along Frobenius -/

section Tilt

variable (p : ℕ) (R : Type*) [CommRing R] [Fact p.Prime] [CharP R p]

/-- The **tilt** of a commutative ring `R` of characteristic `p`: the inverse limit
`lim_{x ↦ x^p} R`, realised as the subring of sequences `f : ℕ → R` satisfying
`f (n+1) ^ p = f n`. -/

@[simp] lemma pRoot_of_pow (x : R) : pRoot hperf (x ^ p) = x := by
  have h : pRoot hperf (frobenius R p x) = x :=
    (RingEquiv.ofBijective (frobenius R p) hperf).symm_apply_apply x
  rw [frobenius_def] at h
  exact h

/-- For a perfect ring `R` of characteristic `p`, the canonical map `R → R♭`,
`x ↦ (x, x^{1/p}, x^{1/p²}, …)`, is a ring isomorphism whose inverse is the sharp map. -/
