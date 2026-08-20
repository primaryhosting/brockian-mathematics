import Mathlib
import RequestProject.Kernel
import RequestProject.TwoDim

/-!
# Weil–Petersson volume polynomials in low complexity

We record the Weil–Petersson volume polynomials `V_{0,3}`, `V_{0,4}` and `V_{0,5}`, the
right-hand sides of Mirzakhani's recursion in the cases `(g,n) = (0,4)` and `(0,5)`, and
verify the recursion in both cases, together with the fact that the recursion determines
the volume polynomial.
-/

open scoped BigOperators Real
open MeasureTheory Set Real

namespace Frontier

set_option maxHeartbeats 1000000

/-! ## The volume polynomials -/

/-- `V_{0,3} ≡ 1`: the moduli space of pairs of pants is a point. -/

lemma hasSum_alt_of_hasSum (p : ℕ) {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1/((n:ℝ)+1)^p) Z) :
    HasSum (fun n : ℕ => (-1:ℝ)^n/((n:ℝ)+1)^p) ((1 - 2/2^p) * Z) := by
  set c : ℕ → ℝ := fun n => 1 / ((n:ℝ)+1)^p - (-1:ℝ)^n / ((n:ℝ)+1)^p with hc
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; simp only [] at h; omega
  have hzero : ∀ n ∉ Set.range (fun k : ℕ => 2 * k + 1), c n = 0 := by
    intro n hn
    have hne : ¬ Odd n := by
      intro ho
      obtain ⟨k, hk⟩ := ho
      exact hn ⟨k, by simp only []; omega⟩
    have : Even n := Nat.not_odd_iff_even.mp hne
    simp [hc, this.neg_one_pow]
  have hcomp : HasSum (c ∘ (fun k : ℕ => 2 * k + 1)) ((2/2^p) * Z) := by
    have h := hZ.mul_left (2/2^p)
    refine h.congr_fun ?_
    intro k
    have h1 : ((2 * k + 1 : ℕ) : ℝ) + 1 = 2 * ((k:ℝ) + 1) := by push_cast; ring
    have h2 : (-1:ℝ)^(2*k+1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    show c (2*k+1) = 2/2^p * (1/((k:ℝ)+1)^p)
    rw [hc]
    simp only [h1, h2]
    have hk : ((k:ℝ)+1) ≠ 0 := by positivity
    rw [mul_pow]
    field_simp
    ring
  have hcsum : HasSum c ((2/2^p) * Z) := (hinj.hasSum_iff hzero).mp hcomp
  have h := hZ.sub hcsum
  have heq : (fun n : ℕ => 1/((n:ℝ)+1)^p - c n) = fun n : ℕ => (-1:ℝ)^n/((n:ℝ)+1)^p := by
    funext n; simp [hc]
  rw [heq] at h
  convert h using 1
  ring

/-- `∫₀^∞ xᵐ/(1+eˣ) dx = m! · η(m+1)`. -/
