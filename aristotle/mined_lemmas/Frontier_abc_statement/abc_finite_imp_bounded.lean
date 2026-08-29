/-
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

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

set_option grind.warning false

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

theorem abc_finite_imp_bounded (h : ABCConjecture) : ABCBounded := by
  intro ε hε
  classical
  set F : Finset (ℕ × ℕ × ℕ) := (h ε hε).toFinset with hF
  refine ⟨1 + ∑ t ∈ F, (t.2.2 : ℝ), ?_⟩
  intro a b c ht
  have hsum : (0 : ℝ) ≤ ∑ t ∈ F, (t.2.2 : ℝ) :=
    Finset.sum_nonneg fun t _ => by positivity
  set K : ℝ := 1 + ∑ t ∈ F, (t.2.2 : ℝ) with hK
  have hK1 : (1 : ℝ) ≤ K := by simp [hK]; linarith
  have hr : (1 : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := one_le_rad_rpow _ ε hε
  by_cases hex : ((rad (a * b * c) : ℝ)) ^ (1 + ε) < (c : ℝ)
  · have hmem : (a, b, c) ∈ F := by
      rw [hF, Set.Finite.mem_toFinset]
      exact ⟨ht, hex⟩
    have hcle : (c : ℝ) ≤ ∑ t ∈ F, (t.2.2 : ℝ) := by
      have := Finset.single_le_sum (f := fun t : ℕ × ℕ × ℕ => (t.2.2 : ℝ))
        (fun t _ => by positivity) hmem
      simpa using this
    calc (c : ℝ) ≤ K := by rw [hK]; linarith
      _ = K * 1 := by ring
      _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_left hr (by linarith)
  · push_neg at hex
    calc (c : ℝ) ≤ (rad (a * b * c) : ℝ) ^ (1 + ε) := hex
      _ = 1 * (rad (a * b * c) : ℝ) ^ (1 + ε) := by ring
      _ ≤ K * (rad (a * b * c) : ℝ) ^ (1 + ε) := by
          apply mul_le_mul_of_nonneg_right hK1 (by linarith)

/-- The bounded form implies finiteness of the exceptional sets. -/
