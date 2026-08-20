import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/

theorem simon_success_bound {n : ℕ} {f : V n → V n} {s : V n} (h : IsSimon f s) (m : ℕ) :
    1 - 2 ^ n / 2 ^ m ≤ simonSuccess f m s := by
  classical
  have hs := h.1
  have hprob : ∀ v : Fin m → V n, ∏ i, simonProb f (v i)
      = if (∀ i, dot (v i) s = 0) then ((2:ℝ)/2^n)^m else 0 := by
    intro v
    by_cases hv : ∀ i, dot (v i) s = 0
    · rw [if_pos hv]
      rw [Finset.prod_congr rfl (fun i _ => by rw [simonProb_eq h, if_pos (hv i)])]
      simp [div_pow]
    · rw [if_neg hv]
      push_neg at hv
      obtain ⟨i, hi⟩ := hv
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [simonProb_eq h, if_neg hi]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin m → V n))
      (fun v => Determines v s) (fun v => ∏ i, simonProb f (v i))
  rw [sum_prod_simonProb h m] at hsplit
  have hbadsum : ∑ v ∈ Finset.univ.filter (fun v : Fin m → V n => ¬ Determines v s),
      ∏ i, simonProb f (v i) = (badSet n m s).card * ((2:ℝ)/2^n)^m := by
    rw [← Finset.sum_subset (s₁ := badSet n m s)]
    · rw [Finset.sum_congr rfl (fun v hv => ?_), Finset.sum_const, nsmul_eq_mul]
      simp only [badSet, Finset.mem_filter] at hv
      rw [hprob v, if_pos hv.2.1]
    · intro v hv
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and] at hv
      simp [hv.2]
    · intro v hvF hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvF
      simp only [badSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hv
      rw [hprob v, if_neg (fun hall => (hv hall) hvF)]
  have hcard := badSet_card_le (m := m) s hs
  have hcast : ((badSet n m s).card : ℝ) * 4 ^ m ≤ 2 ^ n * (2 ^ n) ^ m := by
    have h1 : (((badSet n m s).card * 4 ^ m : ℕ) : ℝ) ≤ (((2 ^ n - 2) * (2 ^ n) ^ m : ℕ) : ℝ) := by
      exact_mod_cast hcard
    have h2 : (((2 ^ n - 2) * (2 ^ n) ^ m : ℕ) : ℝ) ≤ ((2 ^ n * (2 ^ n) ^ m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    push_cast at h1 h2
    linarith
  have hfinal : ((badSet n m s).card : ℝ) * ((2:ℝ)/2^n)^m ≤ 2 ^ n / 2 ^ m := by
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    calc ((badSet n m s).card : ℝ) * 2 ^ m * 2 ^ m
        = ((badSet n m s).card : ℝ) * 4 ^ m := by rw [mul_assoc, ← mul_pow]; norm_num
      _ ≤ 2 ^ n * (2 ^ n) ^ m := hcast
  rw [hbadsum] at hsplit
  unfold simonSuccess
  linarith

/-- With `2 n` queries, Simon's algorithm determines the secret except with probability
`2 ^ (-n)`. -/
