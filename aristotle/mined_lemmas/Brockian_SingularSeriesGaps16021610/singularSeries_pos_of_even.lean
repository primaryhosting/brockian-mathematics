import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/

lemma singularSeries_pos_of_even {d : ℕ} (hd : Even d) : 0 < singularSeries d := by
  rw [singularSeries, if_pos hd]
  have := singularFactor_pos d
  linarith

/-- The singular series of an odd gap vanishes. -/
