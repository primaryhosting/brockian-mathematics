import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩


lemma ivm_invariant : ∀ (L : List (Bool × Bool)) (x : Bool × Bool),
    FreeGroup.IsReduced (x :: L) → ∃ c : ZMod 5, c ≠ 0 ∧ ivm (x :: L) = c • uu x := by
  intro L
  induction L with
  | nil => exact fun x _ => ⟨1, by decide, by rw [ivm_singleton, one_smul]⟩
  | cons y rest ih =>
      intro x hred
      rw [FreeGroup.isReduced_cons_cons] at hred
      obtain ⟨c, hc, hcy⟩ := ih y hred.2
      have hne : y ≠ (x.1, !x.2) := by
        intro hy
        have h1 : x.1 = y.1 := by rw [hy]
        have h2 := hred.1 h1
        rw [hy] at h2
        simp at h2
      obtain ⟨d, hd, hdy⟩ := Nm_mulVec_uu x y hne
      refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
      rw [ivm_cons, hcy, Matrix.mulVec_smul, hdy, smul_smul, mul_comm c d]

/-- The real matrix of a word, in terms of the letters. -/
