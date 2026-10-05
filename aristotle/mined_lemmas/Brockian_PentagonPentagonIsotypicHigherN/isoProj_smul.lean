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

lemma isoProj_smul (c : ℂ) (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (fun j => c * f j) = fun j => c * isoProj k f j := by
  funext j
  have h : ∀ m : ZMod n, ZMod.stdAddChar (k * (j - m)) * (c * f m)
      = c * (ZMod.stdAddChar (k * (j - m)) * f m) := fun m => by ring
  simp only [isoProj, h, ← Finset.mul_sum]
  ring

/-- Projection of a character: `isoProj k (charFun l) = charFun k` if `k = l`, and `0`
otherwise. -/
