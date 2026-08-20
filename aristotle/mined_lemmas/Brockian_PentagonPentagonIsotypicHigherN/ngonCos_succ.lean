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

lemma ngonCos_succ (hn : n ≠ 0) :
    ngonCos n k (m + 1) =
      Real.cos (2 * Real.pi * k / n) * ngonCos n k m
        - Real.sin (2 * Real.pi * k / n) * ngonSin n k m := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have harg : 2 * Real.pi * (k : ℝ) * ((m : ℝ) + 1) / n
      = 2 * Real.pi * (k : ℝ) * m / n + 2 * Real.pi * (k : ℝ) / n := by
    field_simp
  simp only [ngonCos, ngonSin]
  push_cast
  rw [harg, Real.cos_add]
  ring

