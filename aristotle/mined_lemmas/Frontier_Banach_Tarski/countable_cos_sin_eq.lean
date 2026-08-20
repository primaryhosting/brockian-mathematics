import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem countable_cos_sin_eq (A B : ℝ) :
    {u : ℝ | Real.cos u = A ∧ Real.sin u = B}.Countable := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | Real.cos u = A ∧ Real.sin u = B} with h | ⟨u₀, hu₀⟩
  · rw [h]; exact Set.countable_empty
  · obtain ⟨hu1, hu2⟩ := hu₀
    have hAB : A ^ 2 + B ^ 2 = 1 := by
      subst hu1; subst hu2
      exact Real.cos_sq_add_sin_sq u₀
    refine Set.Countable.mono ?_ (Set.countable_range fun k : ℤ => u₀ + k * (2 * Real.pi))
    rintro u ⟨hc, hs⟩
    have hcos : Real.cos (u - u₀) = 1 := by
      rw [Real.cos_sub, hc, hs, hu1, hu2]
      nlinarith [hAB]
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (u - u₀)).1 hcos
    exact ⟨k, by simp only []; linarith [hk]⟩

/-- Preimages of a countable set under multiplication by a nonzero constant are countable. -/
