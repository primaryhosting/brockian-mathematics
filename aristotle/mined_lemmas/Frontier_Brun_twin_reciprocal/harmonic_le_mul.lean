import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

lemma harmonic_le_mul (n : ℕ) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / k ≤
      (∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a) *
        (∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2) := by
  classical
  have H : ∀ k : ℕ, ∃ p : ℕ × ℕ, p.2 ^ 2 * p.1 = k ∧ Squarefree p.1 := by
    intro k
    obtain ⟨a, b, h1, h2⟩ := Nat.sq_mul_squarefree k
    exact ⟨(a, b), h1, h2⟩
  choose f hf1 hf2 using H
  set A := (Icc 1 n).filter Squarefree with hA
  set B := Icc 1 n with hB
  have hmapsto : ∀ k ∈ Icc 1 n, f k ∈ A ×ˢ B := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 := hf1 k
    have hk1 : 1 ≤ k := hk.1
    have ha1 : 1 ≤ (f k).1 := by
      rcases Nat.eq_zero_or_pos (f k).1 with h | h
      · rw [h, Nat.mul_zero] at h1; omega
      · omega
    have hb1 : 1 ≤ (f k).2 := by
      rcases Nat.eq_zero_or_pos (f k).2 with h | h
      · rw [h] at h1; simp at h1; omega
      · omega
    have ha2 : (f k).1 ≤ n := by
      have : (f k).1 ≤ k := by
        calc (f k).1 ≤ (f k).2 ^ 2 * (f k).1 := Nat.le_mul_of_pos_left _ (by positivity)
          _ = k := h1
      omega
    have hb2 : (f k).2 ≤ n := by
      have : (f k).2 ≤ k := by
        calc (f k).2 ≤ (f k).2 ^ 2 := by nlinarith
          _ ≤ (f k).2 ^ 2 * (f k).1 := Nat.le_mul_of_pos_right _ (by omega)
          _ = k := h1
      omega
    simp only [Finset.mem_product, hA, hB, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨ha1, ha2⟩, hf2 k⟩, hb1, hb2⟩
  have hinj : Set.InjOn f ((Icc 1 n : Finset ℕ) : Set ℕ) := by
    intro x _ y _ h
    rw [← hf1 x, ← hf1 y, h]
  calc ∑ k ∈ Icc 1 n, (1:ℝ)/k
      = ∑ k ∈ Icc 1 n, ((1:ℝ)/((f k).1) * (1/((f k).2:ℝ)^2)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hcast : ((k:ℝ)) = ((f k).2:ℝ)^2 * ((f k).1:ℝ) := by exact_mod_cast (hf1 k).symm
        rw [hcast]; ring
    _ = ∑ p ∈ (Icc 1 n).image f, ((1:ℝ)/(p.1) * (1/(p.2:ℝ)^2)) :=
        (Finset.sum_image (f := fun p : ℕ × ℕ => (1:ℝ)/(p.1:ℝ) * (1/(p.2:ℝ)^2)) hinj).symm
    _ ≤ ∑ p ∈ A ×ˢ B, ((1:ℝ)/(p.1) * (1/(p.2:ℝ)^2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_image] at hp
          obtain ⟨k, hk, rfl⟩ := hp
          exact hmapsto k hk
        · intro p _ _; positivity
    _ = (∑ a ∈ A, (1:ℝ)/a) * (∑ b ∈ B, (1:ℝ)/(b:ℝ)^2) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]

/-- The sum of reciprocals of squarefree numbers up to `n` is at most `∏_{p ≤ n} (1 + 1/p)`. -/
