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

lemma ngonProj_const_smul (k : ZMod n) (c : ℂ) (f : ZMod n → ℂ) :
    ngonProj n k (fun j => c * f j) = fun j => c * ngonProj n k f j := by
  funext j
  simp only [ngonProj, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

