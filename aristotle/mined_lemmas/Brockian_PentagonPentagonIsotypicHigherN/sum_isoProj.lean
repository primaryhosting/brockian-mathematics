/-
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 does not allow a module docstring `/-! ... -/` before `import`; the header above is
-- the required header text as a plain block comment, and is repeated as a module docstring below.)

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

set_option maxHeartbeats 1000000

namespace Brockian

open Finset ZMod AddChar

variable {n : ℕ} [NeZero n]

/-- The rotation of the regular `n`-gon acting on complex functions on its vertex set
`ZMod n`: `(rotateVertices f) j = f (j + 1)`. -/

lemma sum_isoProj (f : ZMod n → ℂ) : ∑ k : ZMod n, isoProj k f = f := by
  funext j
  simp only [Finset.sum_apply]
  have hswap : ∑ k : ZMod n, isoProj k f j
      = (n : ℂ)⁻¹ * ∑ m : ZMod n, (∑ k : ZMod n, ZMod.stdAddChar ((j - m) * k)) * f m := by
    simp only [isoProj, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by rw [mul_comm (j - m) k]
  rw [hswap]
  simp only [sum_stdAddChar]
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl, ← mul_assoc, inv_mul_cancel₀ cast_card_ne_zero, one_mul]
  · intro m _ hm
    have : j - m ≠ 0 := fun hc => hm (sub_eq_zero.mp hc).symm
    rw [if_neg this, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Each isotypic projection is an eigenvector of the rotation, with eigenvalue
`charFun k 1`. -/
