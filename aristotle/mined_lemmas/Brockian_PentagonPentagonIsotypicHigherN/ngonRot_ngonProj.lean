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

lemma ngonRot_ngonProj (k : ZMod n) (f : ZMod n → ℂ) :
    ngonRot n (ngonProj n k f) = fun j => ngonChar n k 1 * ngonProj n k f j := by
  funext j
  simp only [ngonRot, ngonProj_eq_smul_char, ngonChar_add]
  ring

/-- The reflection of the `n`-gon interchanges the `k`-th and `(-k)`-th isotypic components. -/
