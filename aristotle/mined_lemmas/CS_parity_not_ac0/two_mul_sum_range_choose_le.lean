import RequestProject.OrApprox

/-!
# Approximating a whole `AC⁰` circuit by a low degree polynomial

Gate by gate (in topological order) we replace each gate by a low degree
function over `ZMod 3`, accumulating an exceptional set of inputs.  A circuit of
depth `d` with `s` gates is approximated by a function of degree `(2ℓ)^d`
outside a set of at most `s · 2^{n-ℓ}` inputs.
-/

namespace CS

open Finset

variable {n : ℕ}

/-- The vector of gate values of a circuit on a given input. -/

lemma two_mul_sum_range_choose_le (N : ℕ) :
    2 * (∑ k ∈ Finset.range N, (2 * N).choose k) ≤ 4 ^ N := by
  classical
  have hsymm : (∑ k ∈ Finset.range N, (2 * N).choose k)
      = ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), (2 * N).choose k := by
    refine Finset.sum_nbij' (fun k => 2 * N - k) (fun k => 2 * N - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      simp only [Finset.mem_range]
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      show 2 * N - (2 * N - k) = k
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      show 2 * N - (2 * N - k) = k
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      rw [Nat.choose_symm (by omega)]
  have htot : ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k = 2 ^ (2 * N) :=
    Nat.sum_range_choose (2 * N)
  have hsplit : ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k
      = (∑ k ∈ Finset.range N, (2 * N).choose k) + (2 * N).choose N
        + ∑ k ∈ Finset.Ico (N + 1) (2 * N + 1), (2 * N).choose k := by
    have h1 : Finset.range (2 * N + 1) = Finset.range (N + 1) ∪ Finset.Ico (N + 1) (2 * N + 1) := by
      ext k; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range (N + 1)) (Finset.Ico (N + 1) (2 * N + 1)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [Finset.mem_range] at hk
      simp only [Finset.mem_Ico] at hk'
      omega
    rw [h1, Finset.sum_union hdisj, Finset.sum_range_succ]
  have h4 : (4 : ℕ) ^ N = 2 ^ (2 * N) := by
    rw [pow_mul]; norm_num
  omega

/-- The number of subsets of a `2N`-element set of size at most `N + D`,
bounded via the central binomial coefficient. -/
