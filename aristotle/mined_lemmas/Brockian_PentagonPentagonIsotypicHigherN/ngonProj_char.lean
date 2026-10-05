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

lemma ngonProj_char (k l : ZMod n) :
    ngonProj n k (ngonChar n l) = if k = l then ngonChar n l else 0 := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hcoef : ngonCoef n k (ngonChar n l) = if k = l then 1 else 0 := by
    simp only [ngonCoef, ngonChar]
    have hm : ∀ m : ZMod n, ZMod.stdAddChar (k * -m) * ZMod.stdAddChar (l * m)
        = ZMod.stdAddChar ((l - k) * m) := by
      intro m
      rw [← AddChar.map_add_eq_mul]
      ring_nf
    rw [Finset.sum_congr rfl fun m _ => hm m]
    have h2 := sum_ngonChar (n := n) (l - k)
    simp only [ngonChar] at h2
    rw [h2]
    by_cases h : k = l
    · simp [h, hn]
    · have hne : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
      simp [hne, h]
  rw [ngonProj_eq_smul_char, hcoef]
  by_cases h : k = l
  · subst h; simp
  · simp only [h, if_false]
    funext j
    simp

