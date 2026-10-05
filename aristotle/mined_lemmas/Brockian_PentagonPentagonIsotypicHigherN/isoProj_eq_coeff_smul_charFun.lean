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

lemma isoProj_eq_coeff_smul_charFun (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k f = fun j => isoCoeff k f * charFun k j := by
  funext j
  have h : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * f m
      = ZMod.stdAddChar (k * j) * (ZMod.stdAddChar (-(k * m)) * f m) := by
    intro m
    have hm : k * (j - m) = k * j + -(k * m) := by ring
    rw [hm, AddChar.map_add_eq_mul, mul_assoc]
  simp only [isoProj, isoCoeff, charFun, h, ← Finset.mul_sum]
  ring

