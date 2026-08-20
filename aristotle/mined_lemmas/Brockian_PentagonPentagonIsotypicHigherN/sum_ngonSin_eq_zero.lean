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

lemma sum_ngonSin_eq_zero (n : ℕ) (k : ℤ) (hn : n ≠ 0) (hk : ¬ ((n : ℤ) ∣ k)) :
    ∑ j ∈ Finset.range n, ngonSin n k j = 0 := by
  have h := sum_ngonRoot_pow_eq_zero n k hn hk
  have h2 : (∑ j ∈ Finset.range n, (ngonRoot n k) ^ j).im = 0 := by rw [h]; simp
  rw [Complex.im_sum] at h2
  rw [← h2]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [ngonRoot_pow n k j hn, Complex.exp_ofReal_mul_I_im, ngonSin]
  norm_num

end Orthogonality

/-- **Pentagon Pentagon Isotypic Higher N.**

The `D₅` pentagon picture generalizes to every regular `n`-gon with `n ≥ 3`.
For every frequency `k` the pair of vectors `(ngonCos n k, ngonSin n k)` indexed by the
vertices `m ∈ ℤ/n` spans a plane which is invariant under the dihedral action:
the rotation by one vertex acts on this plane as the planar rotation by the angle `2πk/n`
(items 1 and 2), the reflection `m ↦ -m` acts as the reflection fixing the cosine vector
and negating the sine vector (items 3 and 4), and both vectors are genuinely `n`-periodic,
i.e. well defined on the vertices of the `n`-gon (items 5 and 6).
Item 7 is the normalization `cos² + sin² = 1`, and item 8 says that for a frequency `k`
which is not a multiple of `n` this plane contains no trivial isotypic component:
both coordinate vectors sum to zero over the vertices. -/
