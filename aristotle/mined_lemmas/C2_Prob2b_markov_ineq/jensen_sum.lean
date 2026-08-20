import Mathlib
open Finset
namespace C2.Prob2b

/-- Markov's inequality (counting form): for nonnegative reals `x i`,
`a` times the number of indices with `a ≤ x i` is at most `∑ i, x i`.
The hypothesis `0 < a` turns out to be unnecessary for the proof. -/

theorem jensen_sum {n : ℕ} (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (x : Fin n → ℝ) (hn : 0 < n) :
    f ((∑ i, x i)/n) ≤ (∑ i, f (x i))/n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have := hf.map_sum_le (t := (univ : Finset (Fin n))) (w := fun _ => (n : ℝ)⁻¹) (p := x)
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => Set.mem_univ _)
  simpa [smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul] using this

/-- The variance of a finite family of reals is nonnegative (Cauchy–Schwarz / Chebyshev). -/
