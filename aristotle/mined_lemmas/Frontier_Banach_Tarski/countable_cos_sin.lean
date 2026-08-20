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


lemma countable_cos_sin (c s : ℝ) : {t : ℝ | Real.cos t = c ∧ Real.sin t = s}.Countable := by
  rcases Set.eq_empty_or_nonempty {t : ℝ | Real.cos t = c ∧ Real.sin t = s} with h | ⟨t₀, ht₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono (s₂ := Set.range (fun k : ℤ => t₀ + k * (2 * Real.pi))) ?_
      (Set.countable_range _)
    rintro t ⟨hc, hs⟩
    have h1 : Real.cos (t - t₀) = 1 := by
      have hpy := Real.sin_sq_add_cos_sq t₀
      rw [ht₀.1, ht₀.2] at hpy
      rw [Real.cos_sub, hc, hs, ht₀.1, ht₀.2]
      nlinarith [hpy]
    rw [Real.cos_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, by linarith [hk]⟩

/-- For a point off the `z`-axis, only countably many rotations about the `z`-axis can send it
to a given point. -/
