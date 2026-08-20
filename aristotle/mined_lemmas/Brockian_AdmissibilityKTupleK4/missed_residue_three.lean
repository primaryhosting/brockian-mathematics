/-
# Admissibility Ktuple K 4
Category: Brockian Corpus
Target: Brockian.AdmissibilityKTupleK4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

/-- A finite set of integers is **admissible** (in the sense of the Hardy–Littlewood
prime `k`-tuples conjecture) if, for every prime `p`, its reduction modulo `p` misses
at least one residue class. -/

theorem missed_residue_three :
    ∃ a : ZMod 3, ∀ h ∈ ({0, 2, 6, 8} : Finset ℤ), (h : ZMod 3) ≠ a := by
  decide

/-- **Admissibility for `4`-tuples.** The `4`-element set `{0, 2, 6, 8}` is an admissible
`k`-tuple with `k = 4`: it has exactly four elements, and for every prime `p` some residue
class mod `p` is missed by it. -/
