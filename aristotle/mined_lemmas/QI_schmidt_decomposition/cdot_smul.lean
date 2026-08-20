/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem cdot_smul {d : ℕ} (x : Fin d → ℂ) (c : ℂ) (w : Fin d → ℂ) :
    cdot x (fun i => c * w i) = c * cdot x w := by
  simp only [cdot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `cdot` is conjugate-homogeneous in its first argument. -/
