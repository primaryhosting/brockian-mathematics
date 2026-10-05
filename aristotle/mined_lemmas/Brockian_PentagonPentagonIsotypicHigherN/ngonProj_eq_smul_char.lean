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

lemma ngonProj_eq_smul_char (k : ZMod n) (f : ZMod n → ℂ) :
    ngonProj n k f = fun j => ngonCoef n k f * ngonChar n k j := by
  funext j
  simp only [ngonProj, ngonCoef]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have h : j - m = -m + j := by ring
  rw [h, ngonChar_add]
  ring

