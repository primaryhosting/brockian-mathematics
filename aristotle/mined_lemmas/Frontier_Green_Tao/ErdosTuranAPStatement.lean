/- Lean requires `import` to precede any module docstring, so the required header comment
appears immediately after the import below. -/
import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
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

namespace Frontier

/-- `HasAPOfLength S k` says that the set `S ⊆ ℕ` contains an arithmetic progression
`a, a + d, …, a + (k-1) * d` of length `k` with nonzero common difference `d`. -/

def ErdosTuranAPStatement : Prop :=
  ∀ S : Set ℕ, ¬ Summable (Set.indicator S fun n : ℕ ↦ (1 : ℝ) / n) →
    ∀ k : ℕ, HasAPOfLength S k

/-- Containing an AP of length `k` is monotone (downwards) in `k`. -/
