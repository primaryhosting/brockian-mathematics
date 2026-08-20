import Mathlib

/-!
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4`: for every `n : ZMod 5`,
`n ^ 2` is `0`, `1` or `4` (rays `2` and `3` are square-free). -/

theorem square_mod5_mem (n : ZMod 5) : n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  revert n
  decide +kernel

/-- Integer form: for every `n : ℤ`, the class of `n ^ 2` in `ZMod 5` is `0`, `1` or `4`. -/
