/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/

lemma fourier_inversion (v : ZMod 7 → ℂ) (j : ZMod 7) :
    ∑ k : ZMod 7, fcoef v k * chi7 (j * k) = 7 * v j := by
  have hstep : ∀ k : ZMod 7, fcoef v k * chi7 (j * k)
      = ∑ l : ZMod 7, v l * chi7 ((j - l) * k) := by
    intro k
    rw [fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hjl : (j - l) * k = -(l * k) + j * k := by ring
    rw [hjl, chi7_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_comm]
  have hinner : ∀ l : ZMod 7, ∑ k : ZMod 7, v l * chi7 ((j - l) * k)
      = if l = j then 7 * v l else 0 := by
    intro l
    rw [← Finset.mul_sum, sum_chi7_mul]
    by_cases h : l = j
    · subst h
      rw [if_pos (by ring), if_pos rfl]
      ring
    · rw [if_neg (by intro hc; exact h (by linear_combination -hc)), if_neg h]
      ring
  rw [Finset.sum_congr rfl (fun l _ => hinner l)]
  simp

/-- If `v` is an eigenvector for `μ`, each Fourier coefficient satisfies
`(μ - λₖ) cₖ = 0`. -/
