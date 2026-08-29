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
open scoped Classical

namespace Brockian

variable {n : ℕ} [NeZero n]

/-- The `k`-th character of the vertex set `ZMod n` of the regular `n`-gon:
`χ_k(j) = exp (2πi k j / n)`. -/

theorem pentagon_isotypic_decomposition (f : ZMod 5 → ℂ) :
    f = ngonProj 5 0 f + (ngonProj 5 1 f + ngonProj 5 4 f)
          + (ngonProj 5 2 f + ngonProj 5 3 f)
      ∧ ngonRefl 5 (ngonProj 5 1 f + ngonProj 5 4 f)
          = ngonProj 5 4 (ngonRefl 5 f) + ngonProj 5 1 (ngonRefl 5 f)
      ∧ ngonRefl 5 (ngonProj 5 2 f + ngonProj 5 3 f)
          = ngonProj 5 3 (ngonRefl 5 f) + ngonProj 5 2 (ngonRefl 5 f) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := sum_ngonProj (n := 5) f
    rw [show (Finset.univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} from by decide] at h
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton] at h
    linear_combination (norm := abel) -h
  · have h1 := ngonRefl_ngonProj (n := 5) 1 f
    have h4 := ngonRefl_ngonProj (n := 5) 4 f
    rw [show (-1 : ZMod 5) = 4 from by decide] at h1
    rw [show (-4 : ZMod 5) = 1 from by decide] at h4
    have hadd : ngonRefl 5 (ngonProj 5 1 f + ngonProj 5 4 f)
        = ngonRefl 5 (ngonProj 5 1 f) + ngonRefl 5 (ngonProj 5 4 f) := rfl
    rw [hadd, h1, h4]
  · have h2 := ngonRefl_ngonProj (n := 5) 2 f
    have h3 := ngonRefl_ngonProj (n := 5) 3 f
    rw [show (-2 : ZMod 5) = 3 from by decide] at h2
    rw [show (-3 : ZMod 5) = 2 from by decide] at h3
    have hadd : ngonRefl 5 (ngonProj 5 2 f + ngonProj 5 3 f)
        = ngonRefl 5 (ngonProj 5 2 f) + ngonRefl 5 (ngonProj 5 3 f) := rfl
    rw [hadd, h2, h3]

end Brockian

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

