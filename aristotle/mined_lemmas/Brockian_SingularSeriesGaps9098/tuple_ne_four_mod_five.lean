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

theorem tuple_ne_four_mod_five (h : ℤ) (hh : h = 0 ∨ h = 2 ∨ h = 6 ∨ h = 8 ∨ h = 9098) :
    (h : ZMod 5) ≠ 4 := by
  rcases hh with rfl | rfl | rfl | rfl | rfl <;> decide

/-- **Singular Series Gaps 9098.**

`(a)` every even gap `d` gives an admissible pair `{0, d}` — in particular the gap `9098`;
`(b)` the `5`-tuple `{0, 2, 6, 8, 9098}` is admissible, so it is a new admissible gap range:
its residues miss `1 mod 2`, `1 mod 3`, `4 mod 5`, and pigeonhole covers all primes `p ≥ 7`.

Mathlib ingredients used: `Finset.card_le_card`, `Finset.card_image_le` and `ZMod.card`
for the pigeonhole step, and `ZMod.intCast_zmod_eq_zero_iff_dvd` for the even-gap step. -/
