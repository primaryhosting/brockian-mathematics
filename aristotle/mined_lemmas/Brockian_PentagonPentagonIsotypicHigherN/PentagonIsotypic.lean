import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
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

namespace Brockian

/-- The cosine coordinate of the `k`-th "isotypic" vector for the regular `n`-gon:
the function `m ↦ cos (2πkm/n)` on the vertices `m` of the `n`-gon. -/

theorem PentagonIsotypic (k m : ℤ) :
    ngonCos 5 k (m + 1) =
        Real.cos (2 * Real.pi * k / 5) * ngonCos 5 k m
          - Real.sin (2 * Real.pi * k / 5) * ngonSin 5 k m ∧
      ngonCos 5 k (m + 5) = ngonCos 5 k m ∧
      (¬ ((5 : ℤ) ∣ k) → ∑ j ∈ Finset.range 5, ngonCos 5 k j = 0) := by
  obtain ⟨h1, -, -, -, h5, -, -, h8⟩ := PentagonPentagonIsotypicHigherN 5 (by norm_num) k m
  refine ⟨by simpa using h1, by simpa using h5, ?_⟩
  intro hk
  exact (h8 (by simpa using hk)).1

end Brockian

