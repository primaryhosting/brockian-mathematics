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

theorem linearIndependent_of_isON {d r : ℕ} {u : Fin r → Fin d → ℂ} (h : IsON u) :
    LinearIndependent ℂ u := by
  rw [linearIndependent_iff']
  intro s g hg l hl
  have h0 : ∀ i : Fin d, (∑ k ∈ s, g k * u k i) = 0 := by
    intro i
    have := congrFun hg i
    simpa [Finset.sum_apply] using this
  have hz : (∑ i, (starRingEnd ℂ) (u l i) * ∑ k ∈ s, g k * u k i) = 0 := by
    simp [h0]
  have hexp : (∑ i, (starRingEnd ℂ) (u l i) * ∑ k ∈ s, g k * u k i)
      = ∑ k ∈ s, g k * cdot (u l) (u k) := by
    simp only [Finset.mul_sum, cdot]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring
  rw [hexp] at hz
  have hz2 : (∑ k ∈ s, g k * (if l = k then (1:ℂ) else 0)) = 0 := by
    rw [show (∑ k ∈ s, g k * (if l = k then (1:ℂ) else 0))
        = ∑ k ∈ s, g k * cdot (u l) (u k) from
      Finset.sum_congr rfl fun k _ => by rw [h l k]]
    exact hz
  simpa [mul_ite, hl] using hz2

/-- `cdot` is additive/homogeneous in its second argument. -/
