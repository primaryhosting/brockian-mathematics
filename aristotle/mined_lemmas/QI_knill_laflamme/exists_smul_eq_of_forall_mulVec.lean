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

lemma exists_smul_eq_of_forall_mulVec (P A : Matrix n n ℂ)
    (hA : ∀ v : n → ℂ, ∃ μ : ℂ, A *ᵥ (P *ᵥ v) = μ • (P *ᵥ v)) :
    ∃ l : ℂ, A * P = l • P := by
  by_cases hP0 : P = 0
  · exact ⟨0, by simp [hP0]⟩
  obtain ⟨j, hj⟩ : ∃ j : n, P *ᵥ (Pi.single j (1 : ℂ)) ≠ 0 := by
    by_contra hc
    push_neg at hc
    refine hP0 ?_
    ext i j
    have := congrFun (hc j) i
    simpa [Matrix.mulVec_single_one] using this
  obtain ⟨l, hl⟩ := hA (Pi.single j (1 : ℂ))
  refine ⟨l, ?_⟩
  have key : ∀ w : n → ℂ, A *ᵥ (P *ᵥ w) = l • (P *ᵥ w) := by
    intro w
    obtain ⟨μ, hμ⟩ := hA w
    by_cases hu0 : P *ᵥ w = 0
    · rw [hu0]; simp
    by_cases hdep : ∃ t : ℂ, P *ᵥ w = t • (P *ᵥ Pi.single j (1 : ℂ))
    · obtain ⟨t, ht⟩ := hdep
      rw [ht, Matrix.mulVec_smul, hl, smul_comm]
    · obtain ⟨ν, hν⟩ := hA (w + Pi.single j (1 : ℂ))
      rw [Matrix.mulVec_add, Matrix.mulVec_add, hμ, hl] at hν
      have hcomb : (μ - ν) • (P *ᵥ w) + (l - ν) • (P *ᵥ Pi.single j (1 : ℂ)) = 0 := by
        rw [sub_smul, sub_smul, sub_add_sub_comm, hν, smul_add, sub_self]
      have hμν : μ = ν := by
        by_contra hne
        have hsub : μ - ν ≠ 0 := sub_ne_zero.mpr hne
        refine hdep ⟨(ν - l) / (μ - ν), ?_⟩
        have h3 : (μ - ν) • (P *ᵥ w) = (ν - l) • (P *ᵥ Pi.single j (1 : ℂ)) := by
          have h4 := hcomb
          rw [add_eq_zero_iff_eq_neg, ← neg_smul] at h4
          rw [h4]
          congr 1
          ring
        calc P *ᵥ w = (μ - ν)⁻¹ • ((μ - ν) • (P *ᵥ w)) := by
              rw [smul_smul, inv_mul_cancel₀ hsub, one_smul]
          _ = ((ν - l) / (μ - ν)) • (P *ᵥ Pi.single j (1 : ℂ)) := by
              rw [h3, smul_smul, div_eq_inv_mul]
      have hlν : l = ν := by
        have h5 : (l - ν) • (P *ᵥ Pi.single j (1 : ℂ)) = 0 := by
          have h6 := hcomb
          rw [hμν, sub_self, zero_smul, zero_add] at h6
          exact h6
        rcases smul_eq_zero.mp h5 with h' | h'
        · exact sub_eq_zero.mp h'
        · exact absurd h' hj
      rw [hμ, hμν, hlν]
  ext i j'
  have h1 : (A * P) *ᵥ (Pi.single j' (1 : ℂ)) = (l • P) *ᵥ (Pi.single j' (1 : ℂ)) := by
    rw [← Matrix.mulVec_mulVec, key, smul_mulVec]
  have := congrFun h1 i
  simpa [Matrix.mulVec_single_one] using this

end Aux

omit [Fintype ι] [DecidableEq ι] in
/-- If a scalar recovery exists, the recovery channel restores all code states. -/
