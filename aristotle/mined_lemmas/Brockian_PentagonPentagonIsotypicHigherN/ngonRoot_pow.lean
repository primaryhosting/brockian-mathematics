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

lemma ngonRoot_pow (n : ℕ) (k : ℤ) (j : ℕ) (hn : n ≠ 0) :
    (ngonRoot n k) ^ j = Complex.exp (((2 * Real.pi * k * j / n : ℝ) : ℂ) * Complex.I) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [ngonRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

