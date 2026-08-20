import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem countable_fixed (M : O3) (hdet : (M : Matrix (Fin 3) (Fin 3) ℝ).det = 1) (hne : M ≠ 1) :
    {x : E | ‖x‖ = 1 ∧ M • x = x}.Countable := by
  rcases eq_empty_or_nonempty {x : E | ‖x‖ = 1 ∧ M • x = x} with h | ⟨x0, hx0⟩
  · rw [h]; exact countable_empty
  · have hMne : (M : Matrix (Fin 3) (Fin 3) ℝ) ≠ 1 := fun hc => hne (Subtype.ext hc)
    have hfix : ∀ x : E, M • x = x → (M : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (fun i => x i) =
        (fun i => x i) := by
      intro x hx
      funext i
      have := congrArg (fun y : E => y i) hx
      simpa [O3.smul_apply, Matrix.mulVec, dotProduct] using this
    have hx0' := hfix x0 hx0.2
    have hx00 : (fun i => x0 i) ≠ (0 : Fin 3 → ℝ) := by
      intro hc
      have : ‖x0‖ = 0 := by
        rw [EuclideanSpace.norm_eq]
        have : ∀ i, x0 i = 0 := fun i => congrFun hc i
        simp [this]
      rw [hx0.1] at this
      exact one_ne_zero this
    refine Set.Countable.mono (s₂ := {x0, -x0}) ?_ ((Set.toFinite _).countable)
    rintro y ⟨hy1, hy2⟩
    obtain ⟨c, hc⟩ := fixed_parallel _ (O3.mem_iff M) hdet hMne hx0' (hfix y hy2) hx00
    have hy : y = c • x0 := by
      ext i
      have := congrFun hc i
      simpa using this
    have hnorm : |c| = 1 := by
      have := congrArg (fun z : E => ‖z‖) hy
      simp only [norm_smul, Real.norm_eq_abs, hx0.1, mul_one] at this
      rw [hy1] at this
      exact this.symm
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp hnorm with h | h
    · left; rw [hy, h, one_smul]
    · right; rw [hy, h]; simp

end BT

import Mathlib
import RequestProject.Abstract
import RequestProject.Space
import RequestProject.Free
import RequestProject.Fixed
import RequestProject.Rotate
import RequestProject.Cone

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
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
set_option synthInstance.maxHeartbeats 400000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open Matrix Set Function Metric

namespace BT

/-- The set of *poles*: points of the unit sphere fixed by some nontrivial element of the
free group of rotations. -/
