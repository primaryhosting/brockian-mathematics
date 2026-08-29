import Mathlib
/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, and a module docstring `/-! ... -/` is not allowed before them.  The required header
comment is therefore placed immediately after the single `import Mathlib` line.
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

namespace Frontier

/-! ## Partial derivatives in the space–time variables

Throughout, a space–time function is a map `u : ℝ → ℝ → ℝ`, written `u t x`, with `t` the
time variable and `x` the space variable. -/

/-- Time derivative `∂_t u` of a space–time function `u : ℝ → ℝ → ℝ`. -/

theorem hairer_KPZ_base_case :
    IsKPZSolution (fun _ _ => 0) kpzHopfCole (Set.Ioi 0) := by
  intro t ht x
  have ht0 : (0 : ℝ) < t := ht
  have htne : t ≠ 0 := ne_of_gt ht0
  rw [dt_kpzHopfCole ht0, dxx_kpzHopfCole htne, dx_kpzHopfCole htne]
  field_simp
  ring

end Frontier

