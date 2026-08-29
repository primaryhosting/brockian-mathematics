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

lemma planeAction_mul (n : ℕ) [NeZero n] (g h : DihedralGroup n) (z : ℂ) :
    planeAction n (g * h) z = planeAction n g (planeAction n h z) := by
  cases g with
  | r i => cases h with
    | r j =>
        show ngonVertex n (i + j) * z = ngonVertex n i * (ngonVertex n j * z)
        rw [ngonVertex_add, mul_assoc]
    | sr j =>
        show (starRingEnd ℂ) (ngonVertex n (j - i) * z)
            = ngonVertex n i * (starRingEnd ℂ) (ngonVertex n j * z)
        have hij : (-(j - i) : ZMod n) = i + -j := by ring
        rw [map_mul, map_mul, conj_ngonVertex, conj_ngonVertex, hij, ← mul_assoc,
          ← ngonVertex_add]
  | sr i => cases h with
    | r j =>
        show (starRingEnd ℂ) (ngonVertex n (i + j) * z)
            = (starRingEnd ℂ) (ngonVertex n i * (ngonVertex n j * z))
        rw [ngonVertex_add, mul_assoc]
    | sr j =>
        show ngonVertex n (j - i) * z
            = (starRingEnd ℂ) (ngonVertex n i * (starRingEnd ℂ) (ngonVertex n j * z))
        have hij : (j - i : ZMod n) = -i + j := by ring
        rw [map_mul, map_mul, map_mul, conj_ngonVertex, Complex.conj_conj, Complex.conj_conj,
          hij, ngonVertex_add, mul_assoc]

/-! ### Equivariance -/

/-- **Equivariance of the `n`-gon vertex map.**  For every `n ≥ 1`, every dihedral symmetry
`g` and every label `k`, moving the label and then taking the vertex agrees with taking the
vertex and then moving the point. -/
