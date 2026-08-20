import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

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

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

theorem twin_count_le (j : ℕ) (hj : 16 ≤ j) (N : ℕ) :
    (#((range N).filter (fun n => n.Prime ∧ (n+2).Prime)) : ℝ)
      ≤ 2*N*Real.exp (-(j:ℝ)) + 2^(E j + 1) := by
  classical
  set W : ℕ := 2^(2^j) with hW
  -- Mertens gives a large enough sum over odd primes below `W`
  have hjR : (16:ℝ) ≤ j := by exact_mod_cast hj
  have h2j : (2:ℝ)^j ≥ 2 := by
    have : (2:ℝ)^1 ≤ (2:ℝ)^j := by
      apply pow_le_pow_right₀ (by norm_num)
      omega
    simpa using this
  have hW3 : 3 ≤ W := by
    rw [hW]
    have h1 : 2 ≤ 2^j := Nat.one_lt_two_pow (by omega)
    calc 3 ≤ 2^2 := by norm_num
      _ ≤ 2^(2^j) := Nat.pow_le_pow_right (by norm_num) h1
  have hlogW : Real.log W = 2^j * Real.log 2 := by
    rw [hW]
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have hlog2gt : (0.6931471803:ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hloglogW : Real.log (Real.log W) ≥ ((j:ℝ)-1) * Real.log 2 := by
    have hge : (2:ℝ)^j * Real.log 2 ≥ 2^((j:ℕ)-1) := by
      have h1 : (2:ℝ)^j * Real.log 2 ≥ 2^j * 0.69 := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]
      have h2 : (2:ℝ)^j = 2 * 2^((j:ℕ)-1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h2] at h1 ⊢
      have : (0:ℝ) < 2^((j:ℕ)-1) := by positivity
      nlinarith
    rw [hlogW]
    have hcast : (((j:ℕ)-1 : ℕ) : ℝ) = (j:ℝ) - 1 := by
      have h1 : 1 ≤ j := by omega
      push_cast [Nat.cast_sub h1]
      ring
    calc ((j:ℝ)-1) * Real.log 2 = (((j:ℕ)-1 : ℕ) : ℝ) * Real.log 2 := by rw [hcast]
      _ = Real.log ((2:ℝ)^((j:ℕ)-1)) := (Real.log_pow _ _).symm
      _ ≤ Real.log ((2:ℝ)^j * Real.log 2) := Real.log_le_log (by positivity) hge
  have hSall : (j:ℝ) ≤ ∑ p ∈ oddPrimesBelow W, 2/(p:ℝ) := by
    have h := sum_oddPrimesBelow_ge W hW3
    have h2 : 2 * (((j:ℝ)-1) * Real.log 2 - Real.log 2) - 1 ≤
        2 * (Real.log (Real.log W) - Real.log 2) - 1 := by linarith
    refine le_trans ?_ (le_trans h2 h)
    nlinarith
  -- choose the sieving set
  obtain ⟨Q, hQsub, hQ1, hQ2⟩ := exists_good_subset (oddPrimesBelow W)
    (fun p hp => three_le_of_mem_oddPrimesBelow hp) (j:ℝ) (by positivity) hSall
  set S := ∑ p ∈ Q, 2/(p:ℝ) with hS
  have hQprime : ∀ p ∈ Q, p.Prime ∧ p ≠ 2 := by
    intro p hp
    obtain ⟨h1, h2, _⟩ := mem_oddPrimesBelow.1 (hQsub hp)
    exact ⟨h1, h2⟩
  set K := 4*j + 10 with hK
  have hKeven : Even K := by
    rw [hK]
    exact ⟨2*j+5, by ring⟩
  have hKS : Real.exp 1 * S + S ≤ K + 1 := by
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have hSle : S ≤ (j:ℝ) + 1 := hQ2
    have hS0 : 0 ≤ S := by
      rw [hS]
      apply Finset.sum_nonneg
      intro p hp
      have := three_le_of_mem_oddPrimesBelow (hQsub hp)
      positivity
    have hKR : ((K:ℕ):ℝ) = 4*(j:ℝ) + 10 := by rw [hK]; push_cast; ring
    rw [hKR]
    nlinarith
  -- the sieve bound
  have hsieve := sifted_bound Q hQprime N K hKeven hKS
  -- twin primes below N are either < W or survive the sieve
  have hsubset : (range N).filter (fun n => n.Prime ∧ (n+2).Prime) ⊆
      (range W) ∪ ((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, hnp, hnp2⟩ := hn
    by_cases hnW : n < W
    · exact Finset.mem_union_left _ (Finset.mem_range.2 hnW)
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 hnN, ?_⟩)
      intro p hpQ hdvd
      obtain ⟨hp1, _, hpW⟩ := mem_oddPrimesBelow.1 (hQsub hpQ)
      have hpn : p < n := lt_of_lt_of_le hpW (by omega)
      rcases (Nat.Prime.dvd_mul hp1).1 hdvd with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp1 hnp).1 h
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hp1 hnp2).1 h
        omega
  have hcard : (#((range N).filter (fun n => n.Prime ∧ (n+2).Prime)) : ℝ)
      ≤ W + (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ) := by
    have h1 := Finset.card_le_card hsubset
    have h2 := Finset.card_union_le (range W) ((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2)))
    have : #((range N).filter (fun n => n.Prime ∧ (n+2).Prime)) ≤
        W + #((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) := by
      simpa using h1.trans h2
    exact_mod_cast this
  -- estimate the error term
  have hQcard : (Q.card : ℝ) ≤ W := by
    have h1 : Q.card ≤ (oddPrimesBelow W).card := Finset.card_le_card hQsub
    have h2 := oddPrimesBelow_card_le W
    exact_mod_cast h1.trans h2
  have herr : ((K:ℕ)+1 : ℝ) * (2*Q.card + 2)^K ≤ 2^(E j) := by
    have hWR : (W:ℝ) = 2^(2^j) := by rw [hW]; push_cast; ring
    have h1 : (2:ℝ)*Q.card + 2 ≤ 2^(2^j + 2) := by
      have : (2:ℝ)*W + 2 ≤ 2^(2^j+2) := by
        rw [hWR, pow_add]
        have h1 : (1:ℝ) ≤ 2^(2^j) := one_le_pow₀ (by norm_num)
        norm_num
        linarith
      nlinarith
    have h2 : ((K:ℕ)+1 : ℝ) ≤ 2^(4*j+11) := by
      have hKR : ((K:ℕ):ℝ) = 4*(j:ℝ) + 10 := by rw [hK]; push_cast; ring
      rw [hKR]
      have : (4*(j:ℝ)+11) ≤ 2^(4*j+11) := by
        have hb : ((4*j+11 : ℕ):ℝ) ≤ 2^(4*j+11) := by
          exact_mod_cast Nat.le_of_lt (Nat.lt_two_pow_self)
        push_cast at hb
        linarith
      linarith
    calc ((K:ℕ)+1 : ℝ) * (2*Q.card + 2)^K
        ≤ 2^(4*j+11) * ((2:ℝ)^(2^j+2))^K := by
          apply mul_le_mul h2 (pow_le_pow_left₀ (by positivity) h1 K) (by positivity) (by positivity)
      _ = 2^(4*j+11) * (2:ℝ)^((2^j+2)*K) := by rw [← pow_mul]
      _ = 2^(E j) := by
          rw [← pow_add, E, hK]
          congr 1
          ring
  have hWle : (W:ℝ) ≤ 2^(E j) := by
    have : (W:ℝ) = 2^(2^j) := by rw [hW]; push_cast; ring
    rw [this]
    apply pow_le_pow_right₀ (by norm_num) (le_E j)
  have hexp : Real.exp (-S) ≤ Real.exp (-(j:ℝ)) := by
    apply Real.exp_le_exp.2
    linarith
  have hN0 : (0:ℝ) ≤ N := by positivity
  calc (#((range N).filter (fun n => n.Prime ∧ (n+2).Prime)) : ℝ)
      ≤ W + (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ) := hcard
    _ ≤ W + (2 * N * Real.exp (-S) + ((K:ℕ)+1 : ℝ) * (2*Q.card + 2)^K) := by
        have := hsieve
        push_cast at this ⊢
        linarith
    _ ≤ 2^(E j) + (2 * N * Real.exp (-(j:ℝ)) + 2^(E j)) := by
        have h1 : 2 * (N:ℝ) * Real.exp (-S) ≤ 2 * N * Real.exp (-(j:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hexp (by positivity)
        linarith
    _ = 2*N*Real.exp (-(j:ℝ)) + 2^(E j + 1) := by
        rw [pow_succ]
        ring

end Brun

import RequestProject.Brun.Twin

/-!
# Convergence of the sum of reciprocals of twin primes (Brun's theorem)

Using the twin prime counting bound `Brun.twin_count_le`, we sum over dyadic blocks and
deduce that `∑ 1/p` over twin primes converges.
-/

open Finset

namespace Brun

/-- The function whose sum is Brun's constant: `1/n` if `n` and `n+2` are both prime. -/
