/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology Set MeasureTheory intervalIntegral
open scoped Real

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

lemma stepFun_eq (f : ℝ → ℝ) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    ∃ k ≤ n, |x - grid n k| ≤ Real.pi / n ∧ stepFun f n x = f (grid n k) := by
  have hpi := Real.pi_pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set k := ⌈x * n / Real.pi⌉₊ with hk
  have hy0 : 0 ≤ x * n / Real.pi := by have := hx.1; positivity
  have hkn : k ≤ n := by
    rw [hk, Nat.ceil_le, div_le_iff₀ hpi]
    have := hx.2
    nlinarith
  have hxk : x ≤ grid n k := by
    have h1 : x * n / Real.pi ≤ (k : ℝ) := Nat.le_ceil _
    unfold grid
    rw [le_div_iff₀ hnR]
    rw [div_le_iff₀ hpi] at h1
    nlinarith
  have hkx : grid n k - x ≤ Real.pi / n := by
    have h2 : (k : ℝ) < x * n / Real.pi + 1 := Nat.ceil_lt_add_one hy0
    unfold grid
    rw [sub_le_iff_le_add, div_le_iff₀ hnR]
    have hcancel : Real.pi / n * n = Real.pi := div_mul_cancel₀ _ hnR.ne'
    have hxn : x * n / Real.pi * Real.pi = x * n := div_mul_cancel₀ _ hpi.ne'
    nlinarith [mul_lt_mul_of_pos_right h2 hpi]
  have hlt : ∀ j : ℕ, j < k → grid n j < x := by
    intro j hj
    have h3 : (j : ℝ) < x * n / Real.pi := Nat.lt_ceil.1 hj
    unfold grid
    rw [div_lt_iff₀ hnR]
    rw [lt_div_iff₀ hpi] at h3
    nlinarith
  refine ⟨k, hkn, by rw [abs_le]; constructor <;> linarith, ?_⟩
  unfold stepFun
  have hfilter : (Finset.range n).filter (fun j => x ≤ grid n j) = Finset.Ico k n := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hjn, hxj⟩
      refine ⟨?_, hjn⟩
      by_contra hc
      push_neg at hc
      exact absurd hxj (not_le.2 (hlt j hc))
    · rintro ⟨hkj, hjn⟩
      exact ⟨hjn, hxk.trans (grid_mono hkj)⟩
  have hsum : (∑ j ∈ Finset.range n,
        (f (grid n j) - f (grid n (j + 1))) * (if x ≤ grid n j then 1 else 0))
      = ∑ j ∈ Finset.Ico k n, (f (grid n j) - f (grid n (j + 1))) := by
    rw [← hfilter, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split <;> simp
  rw [hsum]
  have htel : (∑ j ∈ Finset.Ico k n, (f (grid n j) - f (grid n (j + 1))))
      = f (grid n k) - f (grid n n) := by
    rw [Finset.sum_Ico_eq_sub _ hkn, Finset.sum_range_sub' (fun i => f (grid n i)),
      Finset.sum_range_sub' (fun i => f (grid n i))]
    ring
  rw [htel, grid_self hn]
  ring

