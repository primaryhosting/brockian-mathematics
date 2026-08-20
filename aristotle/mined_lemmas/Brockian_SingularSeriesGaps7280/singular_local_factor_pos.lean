/-
# Singular Series Gaps 7280
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps7280
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim, but as a plain block comment: Lean 4 forbids module
-- doc comments before `import`.)

import Mathlib

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

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`, the
reductions of the elements of `H` modulo `p` omit at least one residue class.
This is exactly the classical condition guaranteeing that the singular series
`𝔖(H)` attached to the tuple `H` does not vanish. -/

theorem singular_local_factor_pos {H : Finset ℕ} (hA : Admissible H)
    {p : ℕ} (hp : p.Prime) : 0 < 1 - (nu H p : ℝ) / p := by
  have hlt : nu H p < p := (admissible_iff_nu_lt H).mp hA p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have : (nu H p : ℝ) < p := by exact_mod_cast hlt
  have : (nu H p : ℝ) / p < 1 := (div_lt_one hp0).mpr this
  linarith

/-- Extension of the family: beyond any bound `N` (e.g. `N = 7280`) and for any
size `k` there exist admissible `k`-tuples consisting of primes larger than `N`. -/
