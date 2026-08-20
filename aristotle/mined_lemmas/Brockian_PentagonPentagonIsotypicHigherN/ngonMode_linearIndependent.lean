/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-! ## Setup

We model a function on the vertices of a regular `n`-gon as a function `ℤ → ℝ` which is
`n`-periodic (the vertex labelled `j` is the vertex `j mod n`).  The dihedral group `D n`
acts by the rotation `j ↦ j + 1` and the reflection `j ↦ -j`.

The `k`-th *mode subspace* is the span of the two "Fourier" functions
`j ↦ cos (2πkj/n)` and `j ↦ sin (2πkj/n)`.  For the pentagon (`n = 5`) the modes `k = 1, 2`
are exactly the two two-dimensional isotypic components of the vertex representation of
`D 5`; the results below establish the corresponding statements for arbitrary `n`. -/

/-- The cosine Fourier mode of index `k` on the vertices of the `n`-gon. -/

lemma ngonMode_linearIndependent {n k : ℕ} (h : Real.sin (2 * π * k / n) ≠ 0) :
    LinearIndependent ℝ ![ngonCos n k, ngonSin n k] := by
  rw [linearIndependent_fin2]
  constructor
  · intro hcon
    apply h
    have := congrFun hcon 1
    simpa [ngonSin_one] using this
  · intro a hcon
    have h0 := congrFun hcon 0
    have h1 := congrFun hcon 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply,
      smul_eq_mul] at h0 h1
    rw [ngonCos_zero] at h0
    have ha : a = 0 := by
      have : ngonSin n k 0 = 0 := by simp [ngonSin]
      rw [this] at h0; simpa using h0.symm
    rw [ha] at h0
    simp at h0

