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

lemma reflect_isoProj (k : ZMod n) (f : ZMod n → ℂ) :
    isoProj k (reflectVertices f) = reflectVertices (isoProj (-k) f) := by
  funext j
  simp only [isoProj, reflectVertices]
  refine congrArg _ ?_
  refine Fintype.sum_equiv (Equiv.neg (ZMod n)) _ _ fun m => ?_
  simp only [Equiv.neg_apply]
  congr 2
  ring

/-- Idempotence and orthogonality of the isotypic projections. -/
