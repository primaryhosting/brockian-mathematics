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


lemma isEquidecomposable_union (y : Bool × Bool) :
    Frontier.IsEquidecomposable FG (W y ∪ W (flip y)) Set.univ := by
  classical
  refine ⟨⟨⟨fun w => if w.toWord.head? = some y then w else lt y * w,
      fun u => if u.toWord.head? = some y then u else lt (flip y) * u,
      W y ∪ W (flip y), Set.univ, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
  · intro w _; trivial
  · -- map_target
    intro u _
    by_cases hu : u.toWord.head? = some y
    · simp only [hu, if_true]
      exact Or.inl hu
    · simp only [hu, if_false]
      right
      have : u.toWord.head? ≠ some (flip (flip y)) := by rwa [flip_flip]
      show (lt (flip y) * u).toWord.head? = some (flip y)
      rw [toWord_lt_mul this]
      simp
  · -- left_inv
    intro w hw
    by_cases h : w.toWord.head? = some y
    · simp [h]
    · simp only [h, if_false]
      have hw' : w ∈ W (flip y) := hw.resolve_left h
      have hhead : w.toWord.head? = some (flip y) := hw'
      obtain ⟨rest, hrest⟩ : ∃ rest, w.toWord = flip y :: rest := by
        cases hcase : w.toWord with
        | nil => rw [hcase] at hhead; simp at hhead
        | cons hd tl =>
            rw [hcase] at hhead
            simp only [List.head?_cons, Option.some.injEq] at hhead
            exact ⟨tl, by simp [hhead]⟩
      have hcancel : lt y * w = FreeGroup.mk rest := by
        have := lt_flip_mul (x := flip y) hrest
        rwa [flip_flip] at this
      have hrestword : (FreeGroup.mk rest).toWord = rest := (eq_lt_mul hrest).2
      have hhead2 : rest.head? ≠ some y := by
        have := head_ne_of_reduced hrest
        rwa [flip_flip] at this
      rw [hcancel]
      have : (FreeGroup.mk rest).toWord.head? ≠ some y := by rw [hrestword]; exact hhead2
      simp only [this, if_false]
      rw [← hcancel, ← mul_assoc, lt_mul_lt, one_mul]
  · -- right_inv
    intro u _
    by_cases hu : u.toWord.head? = some y
    · simp [hu]
    · simp only [hu, if_false]
      have hne : u.toWord.head? ≠ some (flip (flip y)) := by rwa [flip_flip]
      have hword : (lt (flip y) * u).toWord = flip y :: u.toWord := toWord_lt_mul hne
      have : (lt (flip y) * u).toWord.head? ≠ some y := by
        rw [hword]
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact flip_ne y
      simp only [this, if_false]
      rw [← mul_assoc]
      have : lt y * lt (flip y) = 1 := by
        have := lt_mul_lt (flip y)
        rwa [flip_flip] at this
      rw [this, one_mul]
  · -- isDecompOn
    refine ⟨{1, lt y}, ?_⟩
    intro w _
    by_cases h : w.toWord.head? = some y
    · exact ⟨1, by simp, by simp [h]⟩
    · exact ⟨lt y, by simp, by simp [h]⟩

/-- **The free group of rank two is paradoxical**: it contains two disjoint subsets, each of
which is equidecomposable (using left translations) with the whole group. -/
