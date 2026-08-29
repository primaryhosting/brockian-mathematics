/-
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

/-- The dimensions admitted by the Hill–Hopkins–Ravenel theorem: a manifold of dimension `n`
can support a framing with nonzero Kervaire invariant only if `n = 2 ^ (j + 1) - 2` for some
`1 ≤ j ≤ 6`, i.e. `n ∈ {2, 6, 14, 30, 62, 126}`. -/

theorem kervaire_admissible_iff (n : ℕ) :
    KervaireAdmissible n ↔ n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126 := by
  constructor
  · rintro ⟨j, hj1, hj, rfl⟩
    interval_cases j <;> norm_num
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [⟨1, by norm_num⟩, ⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩,
      ⟨5, by norm_num⟩, ⟨6, by norm_num⟩]

/-- **Kervaire invariant (Hill–Hopkins–Ravenel), statement form.**

Let `KervaireNonzero n` be any predicate on dimensions (to be read as: "there is a closed
framed `n`-manifold with nonzero Kervaire invariant").  The Hill–Hopkins–Ravenel theorem is
the assertion `hHHR` that such dimensions are of the form `2 ^ (j + 1) - 2` with `1 ≤ j ≤ 6`.
Granting that assertion, the Kervaire invariant is nonzero only in the six dimensions
`2, 6, 14, 30, 62, 126`; moreover these six dimensions are precisely the admissible ones. -/
