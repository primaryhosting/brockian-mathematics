/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

lemma exists_smul_of_orthogonal (v y : n → ℂ)
    (h : ∀ z : n → ℂ, star v ⬝ᵥ z = 0 → star y ⬝ᵥ z = 0) :
    ∃ μ : ℂ, y = μ • v := by
  by_cases hv : v = 0
  · subst hv
    refine ⟨0, ?_⟩
    have h0 := h y (by simp)
    simpa using dotProduct_star_self_eq_zero.mp h0
  · have hnv : star v ⬝ᵥ v ≠ 0 := fun hc => hv (dotProduct_star_self_eq_zero.mp hc)
    refine ⟨(star v ⬝ᵥ y) / (star v ⬝ᵥ v), ?_⟩
    have hz : star v ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := by
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ hnv, sub_self]
    have h1 : star y ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := h _ hz
    have h2 : star (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v)
        ⬝ᵥ (y - ((star v ⬝ᵥ y) / (star v ⬝ᵥ v)) • v) = 0 := by
      rw [star_sub, sub_dotProduct, h1, star_smul, smul_dotProduct, hz]
      simp
    exact sub_eq_zero.mp (dotProduct_star_self_eq_zero.mp h2)

/-- An operator acting as a scalar on every vector of the code acts as a scalar on the code. -/
