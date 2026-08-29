/-
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Mirzakhani WP Volume
Category: Frontier — Fields Medal Work
Target: Frontier.mirzakhani_WP_volume
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

open MeasureTheory Set Real Asymptotics

namespace Frontier

/-! ## Mirzakhani's integration kernel -/

/-- The basic "logistic" profile appearing in Mirzakhani's kernels:
`logistic u = 1 / (1 + exp (u / 2))`. -/

lemma hasSum_alternating_inv_sq :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2) (π ^ 2 / 12) := by
  have hz := hasSum_inv_sq_succ
  set u : ℕ → ℝ := fun n => if Even n then 0 else 1 / ((n : ℝ) + 1) ^ 2 with hu_def
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; simp only at h; omega
  have hsupp : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), u n = 0 := by
    intro n hn
    rcases Nat.even_or_odd n with h | h
    · simp [hu_def, h]
    · exfalso
      apply hn
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by simp only; omega⟩
  have hcomp : HasSum (fun k : ℕ => u (2 * k + 1)) (π ^ 2 / 24) := by
    have heq : (fun k : ℕ => u (2 * k + 1)) = fun k : ℕ => (1/4 : ℝ) * (1 / ((k : ℝ) + 1) ^ 2) := by
      funext k
      have h1 : ¬ Even (2 * k + 1) := by simp [parity_simps]
      simp only [hu_def, h1, if_false]
      push_cast
      have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [heq]
    have h2 := hz.mul_left (1/4 : ℝ)
    convert h2 using 1
    ring
  have hu : HasSum u (π ^ 2 / 24) := (hinj.hasSum_iff hsupp).1 hcomp
  have hfun : (fun n : ℕ => (-1 : ℝ) ^ n / ((n : ℝ) + 1) ^ 2)
      = fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 - 2 * u n := by
    funext n
    rcases Nat.even_or_odd n with h | h
    · simp [hu_def, h, h.neg_one_pow]
    · have h1 : ¬ Even n := Nat.not_even_iff_odd.2 h
      simp only [hu_def, h1, if_false, h.neg_one_pow]
      ring
  rw [hfun]
  convert hz.sub (hu.mul_left 2) using 1
  ring

