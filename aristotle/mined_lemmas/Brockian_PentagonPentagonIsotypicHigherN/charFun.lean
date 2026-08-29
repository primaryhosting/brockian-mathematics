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

noncomputable def charFun (k : ZMod n) : ZMod n → ℂ := fun j => ZMod.stdAddChar (k * j)

/-- The projection of a function on the vertices of the regular `n`-gon onto the
isotypic component of the rotation group for the character `charFun k`. -/
