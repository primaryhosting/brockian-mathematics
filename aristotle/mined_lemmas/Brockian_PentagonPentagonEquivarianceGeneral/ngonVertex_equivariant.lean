/-
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pentagon Pentagon Equivariance General
Category: Brockian Corpus
Target: Brockian.PentagonPentagonEquivarianceGeneral
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

namespace Brockian

open Complex

/-! ## The regular `n`-gon and its dihedral symmetries

We realize the regular `n`-gon in the complex plane as the set of `n`-th roots of unity,
indexed by `ZMod n`.  The dihedral group `DihedralGroup n` acts on the index set `ZMod n`
combinatorially (`r i` rotates the labels by `i`, `sr i` reflects them) and on the plane `ℂ`
geometrically (`r i` is multiplication by `ζ ^ i`, `sr i` is that rotation followed by complex
conjugation).  The main theorem states that the vertex map is equivariant for these two actions,
for every `n ≥ 1`; the classical pentagon (`D₅`) statement is the special case `n = 5`.
-/

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/

theorem ngonVertex_equivariant (n : ℕ) [NeZero n] (g : DihedralGroup n) (k : ZMod n) :
    ngonVertex n (idxAction n g k) = planeAction n g (ngonVertex n k) := by
  cases g with
  | r i =>
      show ngonVertex n (k + i) = ngonVertex n i * ngonVertex n k
      rw [ngonVertex_add, mul_comm]
  | sr i =>
      show ngonVertex n (-i - k) = (starRingEnd ℂ) (ngonVertex n i * ngonVertex n k)
      have hik : (-i - k : ZMod n) = -(i + k) := by ring
      rw [← ngonVertex_add, conj_ngonVertex, hik]

/-- **Pentagon pentagon equivariance, general form.**

For every `n ≥ 1`, the regular `n`-gon `k ↦ exp (2 π i k / n)` (indexed by `ZMod n`) carries
a compatible pair of dihedral actions:

* `idxAction n` is an action of `DihedralGroup n` on the labels `ZMod n`;
* `planeAction n` is an action of `DihedralGroup n` on the plane `ℂ` by rotations and
  reflections (each of which preserves the unit circle);
* the vertex map is injective, lands on the unit circle, and is equivariant for these actions.

For `n = 5` this is exactly the D₅ pentagon representation statement. -/
