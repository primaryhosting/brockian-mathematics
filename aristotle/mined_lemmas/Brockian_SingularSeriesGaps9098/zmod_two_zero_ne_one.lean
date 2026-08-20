/-
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment because Lean 4 does not permit a module
-- docstring before `import`; the same header is repeated as a module docstring below.)


import Mathlib

/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture: the singular series `𝔖(H)` is nonzero exactly for such `H`)
if for every prime `p` the reductions of the elements of `H` modulo `p` miss at least one
residue class. -/

theorem zmod_two_zero_ne_one : (0 : ZMod 2) ≠ 1 := by decide

/-- Every pair `{0, d}` with `d` even is admissible: modulo `2` both entries are `0`,
and for odd `p` the pigeonhole bound applies. -/
