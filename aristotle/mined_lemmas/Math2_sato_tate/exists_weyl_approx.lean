import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
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

namespace Math2

open Filter Topology Set Polynomial

/-- The Sato–Tate density `(2/π) sin²θ` on the interval `[0, π]`. -/

lemma exists_weyl_approx {f : ℝ → ℝ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : ℕ → ℝ), ∀ t ∈ Icc (0:ℝ) π,
      |f t - ∑ m ∈ Finset.range n, c m * weyl m t| ≤ ε := by
  have hF : Continuous (fun x : ℝ => f (Real.arccos x)) := hf.comp Real.continuous_arccos
  obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-1) 1 (fun x => f (Real.arccos x))
    hF.continuousOn ε hε
  obtain ⟨n, c, hc⟩ := exists_chebyshev_repr q
  refine ⟨n, c, fun t ht => ?_⟩
  have hcos : Real.cos t ∈ Icc (-1:ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have h1 := hq (Real.cos t) hcos
  rw [Real.arccos_cos ht.1 ht.2] at h1
  have h2 : ∑ m ∈ Finset.range n, c m * weyl m t = q.eval (Real.cos t) := (hc (Real.cos t)).symm
  rw [h2, abs_sub_comm]
  exact h1.le

/-! ### The Weyl criterion for the Sato–Tate measure -/

/-- **Weyl criterion for the Sato–Tate measure.**  A sequence of angles in `[0, π]` is
Sato–Tate distributed if and only if all the Weyl sums attached to the nontrivial
symmetric powers tend to `0`. -/
