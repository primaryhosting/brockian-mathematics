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

lemma isoProj_charFun (k l : ZMod n) :
    isoProj k (charFun l) = if k = l then charFun k else 0 := by
  funext j
  have hkey : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * charFun l m
      = ZMod.stdAddChar (k * j) * ZMod.stdAddChar ((l - k) * m) := by
    intro m
    have h1 : k * (j - m) = k * j + -(k * m) := by ring
    have h2 : (l - k) * m = l * m + -(k * m) := by ring
    rw [h1, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, charFun]
    ring
  simp only [isoProj, hkey, ← Finset.mul_sum, sum_stdAddChar]
  by_cases h : k = l
  · subst h
    rw [sub_self, if_pos rfl, if_pos rfl]
    simp only [charFun]
    field_simp
    rw [mul_comm, mul_div_assoc, div_self cast_card_ne_zero, mul_one]
  · have hlk : l - k ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    rw [if_neg hlk, if_neg h]
    simp

/-- Fourier inversion: the isotypic projections recover the original function. -/
