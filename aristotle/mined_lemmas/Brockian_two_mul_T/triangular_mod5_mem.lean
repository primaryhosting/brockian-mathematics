import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
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

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number. -/

theorem triangular_mod5_mem (n : ℕ) :
    (T n : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : (T n : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_mod]
  rcases T_mod_five_mem n with h5 | h5 | h5 <;> rw [h, h5] <;> simp

end ConeLine
end Brockian

