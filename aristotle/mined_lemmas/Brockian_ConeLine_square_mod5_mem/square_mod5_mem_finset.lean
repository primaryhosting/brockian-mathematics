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

theorem square_mod5_mem_finset (n : ZMod 5) : n ^ 2 ∈ ({0, 1, 4} : Finset (ZMod 5)) := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using square_mod5_mem n

/-- Integer/`Int.emod` form: `n ^ 2 % 5 ∈ {0, 1, 4}` for every integer `n`. -/
