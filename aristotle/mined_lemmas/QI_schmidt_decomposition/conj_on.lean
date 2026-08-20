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

theorem conj_on {d r : ℕ} {v : Fin r → Fin d → ℂ} (hv : IsON v) (k l : Fin r) :
    ∑ j, v k j * (starRingEnd ℂ) (v l j) = if k = l then 1 else 0 := by
  have h1 := hv l k
  simp only [cdot] at h1
  have h2 : (∑ j, v k j * (starRingEnd ℂ) (v l j)) = ∑ j, (starRingEnd ℂ) (v l j) * v k j :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h2, h1]
  by_cases hkl : k = l
  · simp [hkl]
  · simp [hkl, Ne.symm hkl]

/-- The reduced density matrix computed from a Schmidt decomposition. -/
