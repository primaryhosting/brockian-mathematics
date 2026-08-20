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

lemma intCast_zmod_two_of_odd (d : ℕ) (hd : ¬ Even d) : (((d : ℤ)) : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hd
  subst hk
  push_cast
  simp [show ((2 : ZMod 2)) = 0 by decide]

/-- The pair `{0, d}` is admissible exactly when the gap `d` is even. -/
