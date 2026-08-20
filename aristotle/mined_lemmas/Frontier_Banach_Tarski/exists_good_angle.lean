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


lemma exists_good_angle (rot : ℝ → SO3) (hpow : ∀ (t : ℝ) (n : ℕ), rot t ^ n = rot (n * t))
    (D : Set E) (hD : D.Countable) (C : Set E) (hC : C.Countable)
    (hcount : ∀ x ∈ D, ∀ y : E, {t : ℝ | toPerm (rot t) x = y}.Countable) :
    ∃ t : ℝ, ∀ x ∈ D, ∀ n : ℕ, 1 ≤ n → toPerm (rot t ^ n) x ∉ C := by
  classical
  have hbad : {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C}.Countable := by
    have hsub : {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C} ⊆
        ⋃ (x : D), ⋃ (n : {n : ℕ // 1 ≤ n}), ⋃ (y : C),
          {t : ℝ | toPerm (rot ((n : ℕ) * t)) (x : E) = (y : E)} := by
      rintro t ⟨x, hx, n, hn, hmem⟩
      refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_iUnion.2 ⟨⟨n, hn⟩, Set.mem_iUnion.2
        ⟨⟨toPerm (rot t ^ n) x, hmem⟩, ?_⟩⟩⟩
      show toPerm (rot ((n : ℕ) * t)) x = toPerm (rot t ^ n) x
      rw [hpow]
    refine Set.Countable.mono hsub ?_
    haveI := hD.to_subtype
    haveI := hC.to_subtype
    refine Set.countable_iUnion (fun x => Set.countable_iUnion (fun n =>
      Set.countable_iUnion (fun y => ?_)))
    have hinj : Function.Injective (fun t : ℝ => ((n : ℕ) : ℝ) * t) := by
      intro a b hab
      have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by
        have : 0 < (n : ℕ) := n.2
        positivity
      exact mul_left_cancel₀ hn0 hab
    exact Set.Countable.preimage (hcount x x.2 y) hinj
  by_contra hcon
  push_neg at hcon
  refine Cardinal.not_countable_real ?_
  have : (Set.univ : Set ℝ) = {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C} := by
    symm
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨x, hx, n, hn, hmem⟩ := hcon t
    exact ⟨x, hx, n, hn, hmem⟩
  rw [this]
  exact hbad

/-! ## Fixed points of rotations, and the Hausdorff paradox -/

/-- The cross product of two vectors of `ℝ³`. -/
