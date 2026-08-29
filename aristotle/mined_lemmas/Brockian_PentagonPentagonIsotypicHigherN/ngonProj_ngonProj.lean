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

lemma ngonProj_ngonProj (k l : ZMod n) (f : ZMod n → ℂ) :
    ngonProj n k (ngonProj n l f) = if k = l then ngonProj n l f else 0 := by
  rw [ngonProj_eq_smul_char l f,
    ngonProj_const_smul k (ngonCoef n l f) (ngonChar n l), ngonProj_char]
  by_cases h : k = l
  · subst h; simp
  · simp only [h, if_false]
    funext j
    simp

/-- Completeness: the isotypic projections sum to the identity. -/
