import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional.
Positivity is expressed by requiring `f (Xᴴ * X)` to be a nonnegative real number. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  pos : ∀ X : Matrix n n ℂ, ∃ r : ℝ, 0 ≤ r ∧ f (Xᴴ * X) = (r : ℂ)

/-- `f` extends the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)`.
(The pure states of the commutative algebra `D_n ≃ ℂ^n` are exactly the evaluations.) -/

lemma state_pos_pair (hf : IsState f) {k l : n} (hkl : k ≠ l) (α β : ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧
      (starRingEnd ℂ) α * α * f (Matrix.single k k 1)
        + (starRingEnd ℂ) α * β * f (Matrix.single k l 1)
        + (starRingEnd ℂ) β * α * f (Matrix.single l k 1)
        + (starRingEnd ℂ) β * β * f (Matrix.single l l 1) = (r : ℂ) := by
  classical
  set w : n → ℂ := fun x => if x = k then α else if x = l then β else 0 with hw
  have hwk : w k = α := by simp [hw]
  have hwl : w l = β := by simp [hw, Ne.symm hkl]
  obtain ⟨r, hr, hval⟩ := hf.pos (Matrix.vecMulVec (Pi.single k (1 : ℂ)) w)
  rw [conjTranspose_mul_self_vecMulVec] at hval
  refine ⟨r, hr, ?_⟩
  have hstep : ∀ q : n, ∑ s : n, Matrix.vecMulVec (star w) w q s * f (Matrix.single q s 1)
      = (starRingEnd ℂ) (w q) * (w k * f (Matrix.single q k 1)
          + w l * f (Matrix.single q l 1)) := by
    intro q
    have hterm : ∀ s : n, Matrix.vecMulVec (star w) w q s * f (Matrix.single q s 1)
        = (starRingEnd ℂ) (w q) * (w s * f (Matrix.single q s 1)) := by
      intro s
      simp [Matrix.vecMulVec_apply, mul_assoc]
    rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.mul_sum]
    congr 1
    rw [← Finset.sum_subset (Finset.subset_univ ({k, l} : Finset n))]
    · rw [Finset.sum_pair hkl]
    · intro s _ hs
      have hsk : s ≠ k := by intro h; exact hs (by simp [h])
      have hsl : s ≠ l := by intro h; exact hs (by simp [h])
      simp [hw, hsk, hsl]
  have key : f (Matrix.vecMulVec (star w) w)
      = (starRingEnd ℂ) α * α * f (Matrix.single k k 1)
        + (starRingEnd ℂ) α * β * f (Matrix.single k l 1)
        + (starRingEnd ℂ) β * α * f (Matrix.single l k 1)
        + (starRingEnd ℂ) β * β * f (Matrix.single l l 1) := by
    rw [linearMap_apply_eq_sum f, Finset.sum_congr rfl fun q _ => hstep q,
      ← Finset.sum_subset (Finset.subset_univ ({k, l} : Finset n))]
    · rw [Finset.sum_pair hkl, hwk, hwl]
      ring
    · intro q _ hq
      have hqk : q ≠ k := by intro h; exact hq (by simp [h])
      have hql : q ≠ l := by intro h; exact hq (by simp [h])
      simp [hw, hqk, hql]
  rw [← key]
  exact hval

/-- If a matrix unit `E k k` is annihilated by the state, so are the off-diagonal units
`E k l` and `E l k`. -/
