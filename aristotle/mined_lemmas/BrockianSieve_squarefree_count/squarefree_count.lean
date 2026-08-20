import Mathlib
/-!
# Squarefree count via the Möbius sieve.
Uses Mathlib's `ArithmeticFunction.moebius` (μ). Bare `import Mathlib`; no non-core/Archive
namespaces or invented lemmas.
-/
namespace BrockianSieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- `∑_{d ∣ n} μ d = 1` if `n = 1` and `0` otherwise. -/

theorem squarefree_count (x : ℕ) :
    (((Finset.Icc 1 x).filter Squarefree).card : ℤ)
      = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ≤ x),
          ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ) := by
  have hIcc : Finset.Icc 1 x = Finset.Ioc 0 x := by ext n; simp; omega
  -- `⌊x / d ^ 2⌋` counts the multiples of `d ^ 2` in `[1, x]`
  have hdiv : ∀ d : ℕ, ((x / d ^ 2 : ℕ) : ℤ)
      = (((Finset.Icc 1 x).filter (fun n => d ^ 2 ∣ n)).card : ℤ) := by
    intro d
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  calc (((Finset.Icc 1 x).filter Squarefree).card : ℤ)
      = ∑ n ∈ Finset.Icc 1 x, (if Squarefree n then (1 : ℤ) else 0) := by simp
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ∣ n), (μ d : ℤ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        simp only [Finset.mem_Icc] at hn
        rw [sum_moebius_sq_dvd hn.1 hn.2]
    _ = ∑ n ∈ Finset.Icc 1 x, ∑ d ∈ Finset.Icc 1 x, (if d ^ 2 ∣ n then (μ d : ℤ) else 0) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_filter _ _
    _ = ∑ d ∈ Finset.Icc 1 x, ∑ n ∈ Finset.Icc 1 x, (if d ^ 2 ∣ n then (μ d : ℤ) else 0) :=
        Finset.sum_comm
    _ = ∑ d ∈ (Finset.Icc 1 x).filter (fun d => d ^ 2 ≤ x),
          ArithmeticFunction.moebius d * ((x / d ^ 2 : ℕ) : ℤ) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hdiv d, ← Finset.sum_filter]
        by_cases h : d ^ 2 ≤ x
        · simp only [h, if_true]
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        · simp only [h, if_false]
          have hemp : (Finset.Icc 1 x).filter (fun n => d ^ 2 ∣ n) = ∅ := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false, not_and]
            rintro ⟨hn1, hnx⟩ hdvd
            exact h (le_trans (Nat.le_of_dvd (by omega) hdvd) hnx)
          simp [hemp]

end BrockianSieve

