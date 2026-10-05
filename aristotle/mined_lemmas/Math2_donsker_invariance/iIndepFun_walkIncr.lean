/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma iIndepFun_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) {u : ℕ → ℝ} (hu : Monotone u) (n k : ℕ) :
    iIndepFun (fun j : Fin k ↦ walkIncr X u n (j : ℕ)) P := by
  classical
  set s : Fin k → Finset ℕ := fun j ↦
    Finset.Ico ⌊(n : ℝ) * u (j : ℕ)⌋₊ ⌊(n : ℝ) * u ((j : ℕ) + 1)⌋₊ with hs
  have hmono : ∀ a b : ℕ, a ≤ b → ⌊(n : ℝ) * u a⌋₊ ≤ ⌊(n : ℝ) * u b⌋₊ := fun a b hab ↦
    Nat.floor_le_floor (by nlinarith [hu hab, Nat.cast_nonneg (α := ℝ) n])
  have hsub : ∀ j : Fin k, s j ⊆ Finset.range ⌊(n : ℝ) * u k⌋₊ := by
    intro j x hx
    simp only [hs, Finset.mem_Ico] at hx
    exact Finset.mem_range.2 (lt_of_lt_of_le hx.2 (hmono _ _ (by omega)))
  have hdisj : Pairwise (Function.onFun Disjoint s) := by
    intro a b hab
    have key : ∀ c d : Fin k, (c : ℕ) < (d : ℕ) → Disjoint (s c) (s d) := by
      intro c d hcd
      refine Finset.disjoint_left.2 fun x hx hx' ↦ ?_
      simp only [hs, Finset.mem_Ico] at hx hx'
      have := hmono ((c : ℕ) + 1) (d : ℕ) hcd
      omega
    rcases lt_or_gt_of_ne (fun h ↦ hab (Fin.ext h) : (a : ℕ) ≠ (b : ℕ)) with h | h
    · exact key a b h
    · exact (key b a h).symm
  exact (iIndepFun_blockSums hmeas hindep hlaw s hsub hdisj).comp
    (g := fun _ : Fin k ↦ fun x : ℝ ↦ x / Real.sqrt n) fun _ ↦ by fun_prop

/-- The joint law of the increments of the rescaled walk is a product of centred Gaussians. -/
