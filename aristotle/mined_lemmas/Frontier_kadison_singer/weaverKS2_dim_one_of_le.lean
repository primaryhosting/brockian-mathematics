/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- Weaver's discrepancy-theoretic form `KS₂` of the Kadison–Singer problem, in dimension `d`,
with smallness parameter `ε` and discrepancy constant `C`.

Given finitely many vectors `v i` in `ℂ^d` which form a Parseval frame
(`∑ i, |⟪v i, x⟫|² = ‖x‖²` for all `x`, i.e. `∑ i, v i v i* = I`) and each of which is small
(`‖v i‖² ≤ ε`), the index set can be split into two halves each of which is a frame with
upper bound `C` (i.e. the operator norm of each of the two partial sums `∑ v i v i*` is at
most `C`).

The Marcus–Spielman–Srivastava theorem states that this holds for every `d` and every `ε > 0`
with `C = (1/√2 + √ε)²`. -/

theorem weaverKS2_dim_one_of_le (ε C : ℝ) (hε : 0 ≤ ε) (hC : 1 / 2 + ε / 2 ≤ C) :
    WeaverKS2 1 ε C := by
  intro m v hv hpar
  classical
  set a : Fin m → ℝ := fun i => ‖v i 0‖ ^ 2 with ha
  have hnorm : ∀ y : EuclideanSpace ℂ (Fin 1), ‖y‖ ^ 2 = ‖y 0‖ ^ 2 := by
    intro y; rw [EuclideanSpace.norm_eq]; simp
  have hinner : ∀ (i : Fin m) (x : EuclideanSpace ℂ (Fin 1)),
      ‖inner ℂ (v i) x‖ ^ 2 = a i * ‖x‖ ^ 2 := by
    intro i x
    rw [hnorm x, ha]
    simp [PiLp.inner_apply, mul_pow, mul_comm]
  have hai : ∀ i, a i ≤ ε := by
    intro i
    have h := hv i
    rw [hnorm (v i)] at h
    exact h
  have ha0 : ∀ i, 0 ≤ a i := fun i => by positivity
  have hsum : ∑ i, a i = 1 := by
    have h := hpar (EuclideanSpace.single (0 : Fin 1) (1:ℂ))
    simp only [hinner] at h
    rw [← Finset.sum_mul] at h
    have hx : ‖(EuclideanSpace.single (0 : Fin 1) (1:ℂ))‖ ^ 2 = 1 := by simp
    rw [hx] at h
    simpa using h
  obtain ⟨T, -, hT1, hT2⟩ := exists_split_le_half (Finset.univ : Finset (Fin m)) a ε hε
    (fun i _ => ha0 i) (fun i _ => hai i)
  have hc : (Finset.univ : Finset (Fin m)) \ T = Tᶜ := by ext i; simp
  rw [hc] at hT2
  rw [hsum] at hT1 hT2
  refine ⟨T, ?_, ?_⟩
  · intro x
    have hx0 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    calc ∑ i ∈ T, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ T, a i) * ‖x‖ ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => hinner i x
      _ ≤ C * ‖x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hx0
          linarith
  · intro x
    have hx0 : (0:ℝ) ≤ ‖x‖ ^ 2 := by positivity
    calc ∑ i ∈ Tᶜ, ‖inner ℂ (v i) x‖ ^ 2 = (∑ i ∈ Tᶜ, a i) * ‖x‖ ^ 2 := by
          rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => hinner i x
      _ ≤ C * ‖x‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hx0
          linarith

/-- The one-dimensional case of Weaver's `KS₂`, with the Marcus–Spielman–Srivastava constant.
This is the base case of the Kadison–Singer theorem. -/
