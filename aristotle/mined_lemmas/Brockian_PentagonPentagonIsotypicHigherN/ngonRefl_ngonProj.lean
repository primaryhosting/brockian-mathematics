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

lemma ngonRefl_ngonProj (k : ZMod n) (f : ZMod n → ℂ) :
    ngonRefl n (ngonProj n k f) = ngonProj n (-k) (ngonRefl n f) := by
  funext j
  simp only [ngonRefl, ngonProj_eq_smul_char, ngonCoef, ngonChar]
  have hchar : ZMod.stdAddChar (k * -j) = ZMod.stdAddChar (-k * j) := by ring_nf
  rw [hchar]
  congr 1
  congr 1
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ (fun m => ?_)
  simp only [Equiv.neg_apply, neg_neg]
  congr 2
  ring

/-- **Isotypic decomposition of the vertex representation of the regular `n`-gon.**

For every `n ≥ 1`, the space of complex functions on the vertices `ZMod n` of the regular
`n`-gon decomposes into the isotypic components of the dihedral group `D_n`, cut out by the
projections `ngonProj n k`.  The six conjuncts state, respectively:

* completeness: the projections sum to the identity;
* idempotence of each projection;
* orthogonality of distinct projections;
* each component is a rotation eigenspace with eigenvalue `χ_k(1)`;
* the reflection interchanges the `k`-th and `(-k)`-th components (so that
  `W_k ⊕ W_{-k}` is the `D_n`-isotypic plane);
* the projections act on characters as the expected Kronecker delta.

This generalizes the classical `D₅` pentagon statement (`n = 5`) to all `n`. -/
