import Mathlib

/-!
# Dirichlet density of primes in an invertible residue class

This file proves a quantitative form of Dirichlet's theorem on primes in arithmetic
progressions, in the logarithmic (Dirichlet) sense: if `a` is a unit of `ZMod q`, then

`(x - 1) * ∑' p prime, p ≡ a [q], log p / p ^ x → 1 / φ(q)`   as `x → 1⁺`.

This is the analytic input for the density form of the Chebotarev theorem for cyclotomic
extensions proved in `RequestProject.Main`.

The proof combines the results of `Mathlib.NumberTheory.LSeries.PrimesInAP`: the L-series of
the von Mangoldt function restricted to the residue class `a` has a simple pole at `s = 1`
with residue `1/φ(q)`, and the contribution of the proper prime powers is bounded.
-/

open scoped Classical

open ArithmeticFunction ArithmeticFunction.vonMangoldt Filter Topology Complex

namespace Math2

/-- The Dirichlet-density statement for primes in the residue class `a` mod `q`, in the form
of the logarithmically weighted prime sum: as `x → 1⁺`,
`(x - 1) * ∑_{p ≡ a (q)} (log p) p ^ (-x) → 1 / φ(q)`. -/

theorem tendsto_mul_tsum_indicator_of_finite_symmDiff {S T : Set ℕ} {F : Finset ℕ} {c : ℝ}
    (hF : ∀ k ∉ F, (k ∈ S ↔ k ∈ T))
    (hTsumm : ∀ x : ℝ, 1 < x →
      Summable (Set.indicator T (fun k : ℕ => Real.log k / (k : ℝ) ^ x)))
    (hT : Tendsto (fun x : ℝ => (x - 1) *
        ∑' k : ℕ, Set.indicator T (fun k : ℕ => Real.log k / (k : ℝ) ^ x) k)
      (𝓝[>] (1 : ℝ)) (𝓝 c)) :
    Tendsto (fun x : ℝ => (x - 1) *
        ∑' k : ℕ, Set.indicator S (fun k : ℕ => Real.log k / (k : ℝ) ^ x) k)
      (𝓝[>] (1 : ℝ)) (𝓝 c) := by
  classical
  set g : ℝ → ℕ → ℝ := fun x k => Real.log k / (k : ℝ) ^ x with hgdef
  set u : ℝ → ℕ → ℝ := fun x k => Set.indicator S (g x) k - Set.indicator T (g x) k with hudef
  have husupp : ∀ (x : ℝ) (k : ℕ), k ∉ F → u x k = 0 := by
    intro x k hk
    by_cases hS : k ∈ S
    · have hTk : k ∈ T := (hF k hk).mp hS
      simp [hudef, Set.indicator_of_mem hS, Set.indicator_of_mem hTk]
    · have hTk : k ∉ T := fun h => hS ((hF k hk).mpr h)
      simp [hudef, Set.indicator_of_notMem hS, Set.indicator_of_notMem hTk]
  have husumm : ∀ x : ℝ, Summable (u x) := fun x => summable_of_ne_finset_zero (husupp x)
  have hutsum : ∀ x : ℝ, ∑' k : ℕ, u x k = ∑ k ∈ F, u x k := fun x => tsum_eq_sum (husupp x)
  -- the sum over `S` differs from the sum over `T` by the finite correction
  have hsplit : ∀ x : ℝ, 1 < x → ∑' k : ℕ, Set.indicator S (g x) k =
      (∑' k : ℕ, Set.indicator T (g x) k) + ∑ k ∈ F, u x k := by
    intro x hx
    rw [← hutsum x, ← (hTsumm x hx).tsum_add (husumm x)]
    exact tsum_congr fun k => by simp [hudef]
  -- the finite correction is negligible in the limit
  have hbound : ∀ (x : ℝ) (k : ℕ), 1 ≤ x → |u x k| ≤ Real.log k := by
    intro x k hx
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hudef, hgdef]
    · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
      have hpow : (1 : ℝ) ≤ (k : ℝ) ^ x := Real.one_le_rpow hk1 (by linarith)
      have hgle : |g x k| ≤ Real.log k := by
        rw [hgdef]
        simp only [abs_div, abs_of_nonneg hlog,
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) x)]
        exact div_le_self hlog hpow
      have hgnn : 0 ≤ g x k := div_nonneg hlog (Real.rpow_nonneg (Nat.cast_nonneg k) x)
      by_cases hS : k ∈ S <;> by_cases hTk : k ∈ T <;>
        simp only [hudef, Set.indicator_of_mem, Set.indicator_of_notMem, hS, hTk, sub_zero,
          zero_sub, sub_self, abs_zero, abs_neg, not_false_eq_true] <;>
        simp_all [abs_of_nonneg hgnn]
  have hT2 : Tendsto (fun x : ℝ => (x - 1) * ∑ k ∈ F, u x k) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    set M : ℝ := ∑ k ∈ F, Real.log k with hMdef
    have hlim : Tendsto (fun x : ℝ => |x - 1| * M) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have hc : Continuous fun x : ℝ => |x - 1| * M := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : (1 : ℝ) ≤ x := le_of_lt hx
    have hsum : |∑ k ∈ F, u x k| ≤ M :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hbound x k hx1)
    calc ‖(x - 1) * ∑ k ∈ F, u x k‖ = |x - 1| * |∑ k ∈ F, u x k| := by
          simp [abs_mul]
      _ ≤ |x - 1| * M := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
  have hcomb := hT.add hT2
  rw [add_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [hsplit x hx, mul_add]

end Math2

/-
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chebotarev
Category: Frontier Math
Target: Math2.chebotarev
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

open NumberField

namespace Math2

/-!
## Generalities on primes of a number field lying over a rational prime
-/

/-- A prime of `𝓞 L` lying over a rational prime has finite residue ring. -/
