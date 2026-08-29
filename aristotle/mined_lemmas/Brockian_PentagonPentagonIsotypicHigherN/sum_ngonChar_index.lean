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

lemma sum_ngonChar_index (j : ZMod n) :
    ∑ k : ZMod n, ngonChar n k j = if j = 0 then (n : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (R := ZMod n) (ψ := ZMod.stdAddChar) j
    (ZMod.isPrimitive_stdAddChar n)
  simp only [ngonChar] at h ⊢
  rw [h]
  simp [ZMod.card]

/-- Each isotypic projection lands in the line spanned by the corresponding character. -/
