import Mathlib

/-!
# Pentagon Pentagon Isotypic Higher N
Category: Brockian Corpus
Target: Brockian.PentagonPentagonIsotypicHigherN
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires every `import` to precede any module docstring, so the header
-- comment above sits immediately after the single `import Mathlib` line.

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Brockian

/-- The vertex space of the regular `n`-gon: complex-valued functions on the vertex
set `ZMod n`.  The dihedral group `D_n` acts on it through the rotation `ngonShift`
and the reflection `ngonRefl`. -/
abbrev NGon (n : ℕ) : Type := ZMod n → ℂ

/-- Rotation of the `n`-gon by `t` vertices, acting on functions by translation. -/

noncomputable def ngonIsotypic (n : ℕ) [NeZero n] (j : ZMod n) : Submodule ℂ (NGon n) :=
  Submodule.span ℂ {⇑(ngonChar n j), ⇑(ngonChar n (-j))}

/-- The eigenvalue `2 cos (2π j / n)` of the adjacency operator on the `j`-th isotypic
component.  For `n = 5` these are the two golden-ratio values `(√5-1)/2` and
`-(1+√5)/2`. -/
