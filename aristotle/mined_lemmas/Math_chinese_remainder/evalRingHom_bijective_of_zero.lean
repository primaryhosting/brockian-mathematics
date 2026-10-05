import Mathlib

/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι]

/-- The natural reduction ring homomorphism `ℤ/(∏ i, n i) → ∏ i, ℤ/(n i)`. -/

lemma evalRingHom_bijective_of_zero (n : ι → ℕ) (hco : Pairwise (Nat.Coprime on n))
    {i₀ : ι} (h0 : n i₀ = 0) :
    Function.Bijective (Pi.evalRingHom (fun i => ZMod (n i)) i₀) := by
  classical
  have hone : ∀ j, j ≠ i₀ → n j = 1 := by
    intro j hj
    have := hco (Ne.symm hj)
    simp only [Function.onFun, Nat.Coprime, h0, Nat.gcd_zero_left] at this
    exact this
  have hsub : ∀ j, j ≠ i₀ → Subsingleton (ZMod (n j)) := by
    intro j hj
    rw [hone j hj]
    infer_instance
  constructor
  · intro y y' hyy'
    funext j
    by_cases hj : j = i₀
    · subst hj; exact hyy'
    · haveI := hsub j hj; exact Subsingleton.elim _ _
  · intro z
    refine ⟨Function.update 0 i₀ z, ?_⟩
    simp

/-- **Chinese remainder theorem.**  For pairwise coprime moduli `n i`, the ring
`ℤ/(∏ i, n i)` is isomorphic to the product ring `∏ i, ℤ/(n i)`; moreover the
isomorphism is the natural one, sending the class of an integer `x` to the tuple
of its classes modulo each `n i`. -/
