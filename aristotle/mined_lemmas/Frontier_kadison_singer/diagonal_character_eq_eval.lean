import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `M_n(ℂ)`: a unital positive linear functional.
Positivity is expressed by requiring `f (Xᴴ * X)` to be a nonnegative real number. -/
structure IsState (f : Matrix n n ℂ →ₗ[ℂ] ℂ) : Prop where
  unital : f 1 = 1
  pos : ∀ X : Matrix n n ℂ, ∃ r : ℝ, 0 ≤ r ∧ f (Xᴴ * X) = (r : ℂ)

/-- `f` extends the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)`.
(The pure states of the commutative algebra `D_n ≃ ℂ^n` are exactly the evaluations.) -/

theorem diagonal_character_eq_eval (chi : (n → ℂ) →ₗ[ℂ] ℂ)
    (hmul : ∀ a b : n → ℂ, chi (a * b) = chi a * chi b) (hone : chi 1 = 1) :
    ∃ i : n, ∀ d : n → ℂ, chi d = d i := by
  classical
  have hidem : ∀ k : n, chi (Pi.single k (1 : ℂ)) * chi (Pi.single k (1 : ℂ))
      = chi (Pi.single k (1 : ℂ)) := by
    intro k
    rw [← hmul]
    congr 1
    funext x
    by_cases h : k = x <;> simp [Pi.single_apply, h]
  have hsum : ∑ k : n, chi (Pi.single k (1 : ℂ)) = 1 := by
    have hone' : ∑ k : n, (Pi.single k (1 : ℂ) : n → ℂ) = (1 : n → ℂ) := by
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← map_sum, hone', hone]
  have hex : ∃ i : n, chi (Pi.single i (1 : ℂ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    rw [Finset.sum_congr rfl fun k _ => hcon k] at hsum
    simp at hsum
  obtain ⟨i, hi⟩ := hex
  have hi1 : chi (Pi.single i (1 : ℂ)) = 1 :=
    mul_right_cancel₀ hi (by rw [hidem i, one_mul])
  have hzero : ∀ k : n, k ≠ i → chi (Pi.single k (1 : ℂ)) = 0 := by
    intro k hk
    have hprod : chi (Pi.single k (1 : ℂ)) * chi (Pi.single i (1 : ℂ)) = 0 := by
      rw [← hmul]
      have hmul0 : (Pi.single k (1 : ℂ) : n → ℂ) * (Pi.single i (1 : ℂ) : n → ℂ) = 0 := by
        funext x
        by_cases h : k = x
        · subst h
          simp [Ne.symm hk]
        · simp [Pi.single_apply, h]
      rw [hmul0, map_zero]
    rw [hi1, mul_one] at hprod
    exact hprod
  refine ⟨i, fun d => ?_⟩
  have hexp : chi d = ∑ k : n, d k * chi (Pi.single k (1 : ℂ)) := by
    conv_lhs => rw [← Finset.univ_sum_single d]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsm : (Pi.single k (d k) : n → ℂ) = d k • (Pi.single k (1 : ℂ) : n → ℂ) := by
      funext x
      by_cases h : k = x <;> simp [Pi.single_apply, h]
    rw [hsm, map_smul, smul_eq_mul]
  rw [hexp, Finset.sum_eq_single i]
  · rw [hi1, mul_one]
  · intro k _ hk
    rw [hzero k hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### The finite-dimensional Kadison–Singer theorem -/

/-- **Kadison–Singer, finite-dimensional case (base case).**
For each index `i`, the pure state `d ↦ d i` of the diagonal MASA `D_n ⊆ M_n(ℂ)` has a
*unique* extension to a state on the full matrix algebra `M_n(ℂ)`, namely `A ↦ A i i`.

This is the finite-dimensional instance of the Kadison–Singer problem (whose full,
infinite-dimensional form, for the atomic MASA `ℓ^∞(ℕ) ⊆ B(ℓ²(ℕ))`, was resolved by
Marcus–Spielman–Srivastava). -/
