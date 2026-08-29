import Mathlib

/-!
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Filter Asymptotics
open Fintype (card)

namespace Math2

variable {n : ℕ}

/-- A *cap set* in `𝔽₃ⁿ`: a set containing no three (not necessarily distinct) points on a line,
i.e. whenever `x + y + z = 0` for `x, y, z` in the set, the three points coincide.

Since `3 • v = 0` in `𝔽₃ⁿ`, the condition `x + y + z = 0` says exactly that `x, y, z` form a
three-term arithmetic progression, so this is equivalent to `ThreeAPFree`. -/

private lemma three_nsmul_eq_zero (x : Fin n → ZMod 3) : x + x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  revert i
  intro i
  generalize x i = a
  revert a
  decide

/-- Being a cap set is the same as being free of three-term arithmetic progressions. -/
