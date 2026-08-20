/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean requires `import` lines to precede every command, including a
module docstring `/-! ... -/`, so this header is a plain comment and the
module docstring below repeats it after the imports.)
-/

import Mathlib
import Archive.Sensitivity

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Two points of the discrete hypercube `Fin n → Bool` are neighbours when they
differ in exactly one coordinate. -/

theorem huang_sensitivity' {n : ℕ} (hn : 1 ≤ n) (H : Finset (Fin n → Bool))
    (hH : 2 ^ (n - 1) < H.card) :
    ∃ q ∈ H, Real.sqrt n ≤ (H.filter fun q' => IsNeighbour q q').card := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using huang_sensitivity (n := m) H (by simpa using hH)

end Frontier

