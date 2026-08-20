import Mathlib
namespace Brockian.SylvesterSchur

/-!
# The Sylvester–Schur theorem

If `n > k ≥ 1` then one of `n+1, …, n+k` has a prime factor `> k`.

The proof follows Erdős' argument: assuming the contrary, every prime factor of the
binomial coefficient `(n+k).choose k` is at most `k`.  This yields two upper bounds for
that binomial coefficient (one via the number of primes `≤ k`, one via the primorial),
both of which are contradicted by an elementary lower bound, except in a range of small
parameters which is covered by an explicit chain of primes.
-/

open Finset Real

/-! ### An elementary upper bound for the prime counting function -/

/-- The number of primes `≤ k`. -/

theorem caseB {N k : ℕ} (hk : 20000 ≤ k) (h1 : 2 * k + 1 ≤ N) (h2 : N ^ 2 < k ^ 3) :
    k * ((2 * k) ^ k * (N ^ Nat.sqrt N * 4 ^ min k (N / 3))) ≤ 4 ^ k * N ^ k := by
  have hk0 : 0 < k := by omega
  have hN0 : 0 < N := by omega
  set s := Nat.sqrt N with hsdef
  set m := min k (N / 3) with hmdef
  have hkR : (20000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0R : (0 : ℝ) < (k : ℝ) := by positivity
  have hN0R : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
  have hyR : 2 * (k : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h1
  have hy2R : (N : ℝ) ^ 2 ≤ (k : ℝ) ^ 3 := by exact_mod_cast h2.le
  have hsR : ((s : ℝ)) ^ 2 ≤ (N : ℝ) := by
    have hle : s ^ 2 ≤ N := Nat.sqrt_le' N
    exact_mod_cast (Nat.cast_le (α := ℝ)).2 hle
  have hm1R : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast min_le_left k (N / 3)
  have hm3R : 3 * (m : ℝ) ≤ (N : ℝ) := by
    have hmm : 3 * m ≤ N := by
      have hmr : m ≤ N / 3 := min_le_right _ _
      omega
    exact_mod_cast hmm
  have key := caseB_real hkR hyR hy2R hsR (by positivity) hm1R hm3R
  have hL : (0 : ℝ) < (k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)) := by positivity
  have hR : (0 : ℝ) < 4 ^ k * (N : ℝ) ^ k := by positivity
  have hlogL : Real.log ((k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)))
      = Real.log k + k * Real.log (2 * k) + s * Real.log N + m * Real.log 4 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
    ring
  have hlogR : Real.log ((4 : ℝ) ^ k * (N : ℝ) ^ k) = k * Real.log 4 + k * Real.log N := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
  have hfin :
      (k : ℝ) * ((2 * (k : ℝ)) ^ k * ((N : ℝ) ^ s * 4 ^ m)) ≤ 4 ^ k * (N : ℝ) ^ k := by
    rw [← Real.log_le_log_iff hL hR, hlogL, hlogR]
    exact key
  have hcast :
      ((k * ((2 * k) ^ k * (N ^ s * 4 ^ m)) : ℕ) : ℝ) ≤ ((4 ^ k * N ^ k : ℕ) : ℝ) := by
    push_cast
    exact hfin
  exact_mod_cast hcast

/-! ### The third case: a chain of primes -/

/-- One step of the descent along a chain of primes. -/
