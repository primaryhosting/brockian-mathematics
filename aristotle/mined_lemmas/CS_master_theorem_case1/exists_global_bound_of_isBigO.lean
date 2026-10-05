import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- For `b > 0`, taking the `k`-th (natural) power commutes with the real power `c`. -/

lemma exists_global_bound_of_isBigO {f g : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) (hg : ∀ k, 0 < g k)
    (h : f =O[atTop] g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ k, f k ≤ C * g k := by
  obtain ⟨C, hC⟩ := h.bound
  rw [Filter.eventually_atTop] at hC
  obtain ⟨N, hN⟩ := hC
  obtain ⟨M, hM⟩ := ((Finset.range N).image (fun k => f k / g k)).exists_le
  refine ⟨max (max C M) 0, le_max_right _ _, fun k => ?_⟩
  have hgk : 0 < g k := hg k
  have hmax1 : C ≤ max (max C M) 0 := le_trans (le_max_left C M) (le_max_left _ _)
  have hmax2 : M ≤ max (max C M) 0 := le_trans (le_max_right C M) (le_max_left _ _)
  by_cases hk : N ≤ k
  · have hb := hN k hk
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hf k), abs_of_nonneg hgk.le] at hb
    nlinarith
  · have hmem : f k / g k ≤ M :=
      hM _ (Finset.mem_image_of_mem _ (Finset.mem_range.2 (by omega)))
    rw [div_le_iff₀ hgk] at hmem
    nlinarith

open Asymptotics Filter in
/-- **Master theorem, Case 1**, stated with Mathlib's asymptotic notation.

If `T` satisfies `T(b^(k+1)) = a * T(b^k) + f(b^(k+1))` with `a > 0`, `b > 1`, `f ≥ 0` and
`f(n) = O(n^(log_b a - ε))` for some `ε > 0`, then `T(n) = Θ(n^(log_b a))`
(along `n = b^k`, `k → ∞`). -/
