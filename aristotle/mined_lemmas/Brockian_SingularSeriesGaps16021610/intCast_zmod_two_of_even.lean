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

lemma intCast_zmod_two_of_even (d : ℕ) (hd : Even d) : (((d : ℤ)) : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := hd
  subst hk
  push_cast
  rw [← two_mul]
  simp [show ((2 : ZMod 2)) = 0 by decide]

/-- An odd natural number casts to `1` in `ZMod 2`. -/
