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

lemma sum_ngonProj (f : ZMod n → ℂ) : ∑ k : ZMod n, ngonProj n k f = f := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  funext j
  rw [Finset.sum_apply]
  simp only [ngonProj]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have h1 : ∀ m : ZMod n, ∑ k : ZMod n, ngonChar n k (j - m) * f m
      = if m = j then (n : ℂ) * f j else 0 := by
    intro m
    rw [← Finset.sum_mul, sum_ngonChar_index]
    by_cases h : m = j
    · subst h; simp
    · have hne : j - m ≠ 0 := fun hc => h (sub_eq_zero.mp hc).symm
      simp [hne, h]
  rw [Finset.sum_congr rfl fun m _ => h1 m, Finset.sum_ite_eq' Finset.univ j]
  simp [hn]

/-- The `k`-th isotypic component is a rotation eigenspace with eigenvalue `χ_k(1)`. -/
