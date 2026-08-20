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
theorem Brun_twin_reciprocal :
    Summable (fun n : ℕ => if n.Prime ∧ (n + 2).Prime then (1 : ℝ) / n else 0) :=
  Brun.summable_twinRecip

end Frontier

import RequestProject.Brun.Bound
import RequestProject.Brun.Mertens

/-!
# An upper bound for the number of twin primes below `N`

Combining the sieve bound with the Mertens-type lower bound, we obtain
`Brun.twin_count_le`: for `j ≥ 16` and any `N`,
`#{n < N : n and n+2 are prime} ≤ 2 N exp (-j) + 2 ^ (E j + 1)`,
where `E j` is an explicit (huge) exponent depending only on `j`.
-/

open Finset

namespace Brun

/-- The odd primes below `W`. -/
def oddPrimesBelow (W : ℕ) : Finset ℕ := (Nat.primesBelow W).filter (fun p => p ≠ 2)

lemma mem_oddPrimesBelow {p W : ℕ} : p ∈ oddPrimesBelow W ↔ (p.Prime ∧ p ≠ 2 ∧ p < W) := by
  simp only [oddPrimesBelow, Finset.mem_filter, Nat.mem_primesBelow]
  tauto

lemma oddPrimesBelow_card_le (W : ℕ) : (oddPrimesBelow W).card ≤ W := by
  have hsub : oddPrimesBelow W ⊆ range W := by
    intro p hp
    exact Finset.mem_range.2 (mem_oddPrimesBelow.1 hp).2.2
  simpa using Finset.card_le_card hsub

lemma three_le_of_mem_oddPrimesBelow {p W : ℕ} (hp : p ∈ oddPrimesBelow W) : 3 ≤ p := by
  obtain ⟨h1, h2, _⟩ := mem_oddPrimesBelow.1 hp
  have := h1.two_le
  omega

/-- Mertens-type lower bound for the sum of `2/p` over odd primes below `W`. -/
lemma sum_oddPrimesBelow_ge (W : ℕ) (hW : 3 ≤ W) :
    2 * (Real.log (Real.log W) - Real.log 2) - 1 ≤ ∑ p ∈ oddPrimesBelow W, 2/(p:ℝ) := by
  classical
  have hmert := sum_one_div_primesBelow_ge W hW
  have hsplit : ∑ p ∈ Nat.primesBelow W, (1:ℝ)/p
      = (if 2 ∈ Nat.primesBelow W then (1:ℝ)/2 else 0) + ∑ p ∈ oddPrimesBelow W, (1:ℝ)/p := by
    by_cases h2 : 2 ∈ Nat.primesBelow W
    · rw [if_pos h2]
      have : oddPrimesBelow W = (Nat.primesBelow W).erase 2 := by
        unfold oddPrimesBelow
        ext p
        simp [Finset.mem_erase, Finset.mem_filter]
        tauto
      rw [this]
      have := Finset.add_sum_erase (Nat.primesBelow W) (fun p => (1:ℝ)/p) h2
      simpa using this.symm
    · rw [if_neg h2]
      have : oddPrimesBelow W = Nat.primesBelow W := by
        unfold oddPrimesBelow
        apply Finset.filter_true_of_mem
        intro p hp
        rintro rfl
        exact h2 hp
      rw [this, zero_add]
  have hhalf : (if 2 ∈ Nat.primesBelow W then (1:ℝ)/2 else 0) ≤ 1/2 := by
    split <;> norm_num
  have hdouble : ∑ p ∈ oddPrimesBelow W, 2/(p:ℝ) = 2 * ∑ p ∈ oddPrimesBelow W, (1:ℝ)/p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hdouble]
  linarith

/-- Greedy choice of a subset with prescribed sum. -/
lemma exists_good_subset (R : Finset ℕ) (hR : ∀ p ∈ R, 3 ≤ p) (T : ℝ) (hT : 0 ≤ T)
    (hbig : T ≤ ∑ p ∈ R, 2/(p:ℝ)) :
    ∃ Q ⊆ R, T ≤ ∑ p ∈ Q, 2/(p:ℝ) ∧ ∑ p ∈ Q, 2/(p:ℝ) ≤ T + 1 := by
  classical
  set F := R.powerset.filter (fun Q : Finset ℕ => T ≤ ∑ p ∈ Q, 2/(p:ℝ)) with hF
  have hRF : R ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl R, hbig⟩
  obtain ⟨Q, hQF, hQmin⟩ := Finset.exists_min_image F Finset.card ⟨R, hRF⟩
  rw [hF, Finset.mem_filter, Finset.mem_powerset] at hQF
  refine ⟨Q, hQF.1, hQF.2, ?_⟩
  by_contra hc
  push_neg at hc
  have hQne : Q.Nonempty := by
    rcases Finset.eq_empty_or_nonempty Q with h | h
    · rw [h] at hc
      simp at hc
      linarith
    · exact h
  obtain ⟨p, hp⟩ := hQne
  have hp3 : (3:ℝ) ≤ p := by exact_mod_cast hR p (hQF.1 hp)
  have herase : ∑ q ∈ Q.erase p, 2/(q:ℝ) = (∑ q ∈ Q, 2/(q:ℝ)) - 2/(p:ℝ) := by
    have := Finset.add_sum_erase Q (fun q => 2/(q:ℝ)) hp
    linarith [this]
  have hple : 2/(p:ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hmem : Q.erase p ∈ F := by
    rw [hF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨(Finset.erase_subset _ _).trans hQF.1, ?_⟩
    rw [herase]
    linarith
  have := hQmin _ hmem
  have hcard := Finset.card_erase_of_mem hp
  have : 0 < Q.card := Finset.card_pos.2 ⟨p, hp⟩
  omega

/-- The exponent appearing in the error term of the sieve, for parameter `j`. -/
def E (j : ℕ) : ℕ := (2^j + 2) * (4*j + 10) + 4*j + 11

lemma le_E (j : ℕ) : 2^j ≤ E j := by
  have h : 2^j * 1 ≤ (2^j + 2) * (4*j + 10) := Nat.mul_le_mul (by omega) (by omega)
  rw [mul_one] at h
  simp only [E]
  omega

lemma j_le_E (j : ℕ) : j ≤ E j := le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (le_E j)

/-- **Upper bound on the number of twin primes below `N`.** -/
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
noncomputable def twinRecip (n : ℕ) : ℝ := if n.Prime ∧ (n+2).Prime then 1/(n:ℝ) else 0

lemma twinRecip_nonneg (n : ℕ) : 0 ≤ twinRecip n := by
  unfold twinRecip
  split
  · positivity
  · exact le_rfl

/-- The dyadic block sums. -/
noncomputable def block (i : ℕ) : ℝ := ∑ n ∈ Ico (2^i) (2^(i+1)), twinRecip n

lemma block_nonneg (i : ℕ) : 0 ≤ block i :=
  Finset.sum_nonneg fun n _ => twinRecip_nonneg n

lemma block_le_count (i : ℕ) :
    block i ≤ (1/(2:ℝ)^i) * #((range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
  classical
  have h1 : ∀ n ∈ Ico (2^i) (2^(i+1)),
      twinRecip n ≤ (if n.Prime ∧ (n+2).Prime then (1:ℝ)/2^i else 0) := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    unfold twinRecip
    split
    · apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast hn.1
    · exact le_rfl
  calc block i
      ≤ ∑ n ∈ Ico (2^i) (2^(i+1)), (if n.Prime ∧ (n+2).Prime then (1:ℝ)/2^i else 0) :=
        Finset.sum_le_sum h1
    _ = (1/(2:ℝ)^i) * #((Ico (2^i) (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
        rw [← Finset.sum_filter, Finset.sum_const]
        simp [nsmul_eq_mul, mul_comm]
    _ ≤ (1/(2:ℝ)^i) * #((range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hsub : (Ico (2^i) (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime) ⊆
            (range (2^(i+1))).filter (fun n => n.Prime ∧ (n+2).Prime) := by
          apply Finset.filter_subset_filter
          intro x hx
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
        exact_mod_cast Finset.card_le_card hsub

/-- The geometric ratio used in the error estimate. -/
noncomputable def rt : ℝ := Real.sqrt 2 / 2

lemma rt_nonneg : 0 ≤ rt := by
  unfold rt
  positivity

lemma rt_lt_one : rt < 1 := by
  unfold rt
  have h : Real.sqrt 2 < 2 := by
    have : Real.sqrt 2 < Real.sqrt 4 := by
      apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    calc Real.sqrt 2 < Real.sqrt 4 := this
      _ = 2 := by
          rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  linarith

/-- Block bound with sieve parameter `j`. -/
lemma block_le (i j : ℕ) (hj : 16 ≤ j) (hij : 2 * E j ≤ i) :
    block i ≤ 4 * Real.exp (-(j:ℝ)) + 2 * rt^i := by
  have hcount := twin_count_le j hj (2^(i+1))
  have h2i : (0:ℝ) < 2^i := by positivity
  have hstep : block i ≤ (1/(2:ℝ)^i) * (2*(2^(i+1) : ℕ)*Real.exp (-(j:ℝ)) + 2^(E j + 1)) := by
    refine (block_le_count i).trans ?_
    apply mul_le_mul_of_nonneg_left hcount (by positivity)
  have hpow : ((2^(i+1) : ℕ) : ℝ) = 2 * 2^i := by push_cast; ring
  have hfirst : (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ))) = 4 * Real.exp (-(j:ℝ)) := by
    rw [hpow]
    field_simp
    ring
  have hsecond : (1/(2:ℝ)^i) * (2:ℝ)^(E j + 1) ≤ 2 * rt^i := by
    have hsq : ((2:ℝ)^(E j))^2 ≤ ((Real.sqrt 2)^i)^2 := by
      have h1 : ((2:ℝ)^(E j))^2 = 2^(2 * E j) := by
        rw [← pow_mul, mul_comm]
      have h2 : ((Real.sqrt 2)^i)^2 = (2:ℝ)^i := by
        rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (by norm_num)]
      rw [h1, h2]
      exact pow_le_pow_right₀ (by norm_num) hij
    have hle : (2:ℝ)^(E j) ≤ (Real.sqrt 2)^i :=
      (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
    have hrw : (1/(2:ℝ)^i) * (2:ℝ)^(E j + 1) = 2 * ((2:ℝ)^(E j) / 2^i) := by
      rw [pow_succ]
      field_simp
    rw [hrw]
    have hrt : rt^i = (Real.sqrt 2)^i / 2^i := by
      unfold rt
      rw [div_pow]
    rw [hrt]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact (div_le_div_iff_of_pos_right (by positivity)).mpr hle
  calc block i ≤ (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ)) + 2^(E j + 1)) := hstep
    _ = (1/(2:ℝ)^i) * (2*((2^(i+1) : ℕ) : ℝ)*Real.exp (-(j:ℝ))) + (1/(2:ℝ)^i) * 2^(E j + 1) := by
        ring
    _ ≤ 4 * Real.exp (-(j:ℝ)) + 2 * rt^i := by rw [hfirst]; linarith [hsecond]

lemma block_le_one (i : ℕ) : block i ≤ 1 := by
  classical
  have h1 : ∀ n ∈ Ico (2^i) (2^(i+1)), twinRecip n ≤ (1:ℝ)/2^i := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    unfold twinRecip
    split
    · apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast hn.1
    · positivity
  calc block i ≤ ∑ _n ∈ Ico (2^i) (2^(i+1)), (1:ℝ)/2^i := Finset.sum_le_sum h1
    _ = 1 := by
        rw [Finset.sum_const, Nat.card_Ico]
        have : (2:ℕ)^(i+1) - 2^i = 2^i := by
          have : (2:ℕ)^(i+1) = 2 * 2^i := by ring
          omega
        rw [this, nsmul_eq_mul]
        field_simp
        push_cast
        ring

/-- The block index threshold for sieve parameter `j`. -/
def aa (j : ℕ) : ℕ := 2 * E j

lemma E_mono : Monotone E := by
  intro j k hjk
  unfold E
  have h1 : 2^j + 2 ≤ 2^k + 2 := by
    have : (2:ℕ)^j ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hjk
    omega
  have h2 : 4*j + 10 ≤ 4*k + 10 := by omega
  have := Nat.mul_le_mul h1 h2
  omega

lemma aa_mono : Monotone aa := fun _ _ hjk => Nat.mul_le_mul_left 2 (E_mono hjk)

lemma le_aa (j : ℕ) : j ≤ aa j := by
  unfold aa
  have := j_le_E j
  omega

/-- The largest admissible sieve parameter for block index `i`. -/
noncomputable def jj (i : ℕ) : ℕ := Nat.findGreatest (fun j => 16 ≤ j ∧ 2 * E j ≤ i) i

lemma jj_spec {i : ℕ} (hi : aa 16 ≤ i) : 16 ≤ jj i ∧ 2 * E (jj i) ≤ i := by
  unfold jj
  refine Nat.findGreatest_spec (P := fun j => 16 ≤ j ∧ 2 * E j ≤ i) (m := 16)
    (le_trans (le_aa 16) hi) ⟨le_rfl, ?_⟩
  simpa [aa] using hi

lemma le_jj {i j : ℕ} (hj : 16 ≤ j) (hij : aa j ≤ i) : j ≤ jj i := by
  unfold jj
  refine Nat.le_findGreatest (le_trans (le_aa j) hij) ⟨hj, ?_⟩
  simpa [aa] using hij

/-- Partition of a sum over a long interval into blocks. -/
lemma sum_Ico_partition (h : ℕ → ℝ) {m J : ℕ} (hmJ : m ≤ J) :
    ∑ i ∈ Ico (aa m) (aa J), h i = ∑ j ∈ Ico m J, ∑ i ∈ Ico (aa j) (aa (j+1)), h i := by
  induction J, hmJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ, ← ih,
      Finset.sum_Ico_consecutive _ (aa_mono hJ) (aa_mono (Nat.le_succ J))]

/-- The comparison series. -/
noncomputable def vv (j : ℕ) : ℝ := 928 * ((j:ℝ)+1) * (2/Real.exp 1)^j

lemma vv_nonneg (j : ℕ) : 0 ≤ vv j := by
  unfold vv
  positivity

lemma summable_vv : Summable vv := by
  have hlt : (2/Real.exp 1 : ℝ) < 1 := by
    rw [div_lt_one (Real.exp_pos 1)]
    have := Real.exp_one_gt_d9
    linarith
  have h : ‖(2/Real.exp 1 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hlt
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 h
  have h2 := summable_geometric_of_lt_one (r := (2/Real.exp 1 : ℝ)) (by positivity) hlt
  have h3 : Summable (fun j : ℕ => ((j:ℝ)+1) * (2/Real.exp 1)^j) := by
    simpa [add_mul] using h1.add h2
  have h4 := h3.mul_left 928
  have heq : vv = fun j : ℕ => 928 * (((j:ℝ)+1) * (2/Real.exp 1)^j) := by
    funext j; unfold vv; ring
  rw [heq]
  exact h4

lemma aa_succ_le (j : ℕ) : 4 * (aa (j+1) : ℝ) * Real.exp (-(j:ℝ)) ≤ vv j := by
  have hnat : E (j+1) ≤ 116 * (j+1) * 2^j := by
    have hx : 1 ≤ (2:ℕ)^j := Nat.one_le_two_pow
    have hE : E (j+1) = (2*2^j + 2) * (4*j + 14) + 4*j + 15 := by
      unfold E
      rw [pow_succ]
      ring
    rw [hE]
    nlinarith
  have hR : (aa (j+1) : ℝ) ≤ 232 * ((j:ℝ)+1) * 2^j := by
    have haa : (aa (j+1) : ℝ) = 2 * (E (j+1) : ℝ) := by unfold aa; push_cast; ring
    rw [haa]
    have h2 : ((E (j+1) : ℕ) : ℝ) ≤ 116 * ((j:ℝ)+1) * 2^j := by
      exact_mod_cast hnat
    linarith
  have hexp : (0:ℝ) < Real.exp (-(j:ℝ)) := Real.exp_pos _
  have hgeom : (2/Real.exp 1 : ℝ)^j = 2^j * Real.exp (-(j:ℝ)) := by
    rw [div_pow, ← Real.exp_nat_mul]
    rw [Real.exp_neg]
    field_simp
  unfold vv
  rw [hgeom]
  nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j]

/-- The tail sum bound. -/
lemma tail_sum_le (I : ℕ) :
    ∑ i ∈ range I, (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) ≤ ∑' j, vv j := by
  classical
  set g : ℕ → ℝ := fun i => if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0 with hg
  have hgnn : ∀ i, 0 ≤ g i := by
    intro i
    rw [hg]
    dsimp only
    split
    · positivity
    · exact le_rfl
  have hgle : ∀ i, g i ≤ 4 * Real.exp (-(jj i : ℝ)) := by
    intro i
    rw [hg]
    dsimp only
    split
    · exact le_rfl
    · positivity
  set J := I + 16 with hJ
  have hIJ : I ≤ aa J := le_trans (by omega) (le_aa J)
  have h16J : 16 ≤ J := by omega
  have hzero : ∑ i ∈ range (aa 16), g i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hg]
    dsimp only
    rw [if_neg]
    exact Nat.not_le.2 (Finset.mem_range.1 hi)
  have hinner : ∀ j ∈ Ico 16 J, ∑ i ∈ Ico (aa j) (aa (j+1)), g i ≤ vv j := by
    intro j hj
    have hj16 : 16 ≤ j := (Finset.mem_Ico.1 hj).1
    have hpt : ∀ i ∈ Ico (aa j) (aa (j+1)), g i ≤ 4 * Real.exp (-(j:ℝ)) := by
      intro i hi
      have hij : aa j ≤ i := (Finset.mem_Ico.1 hi).1
      have hjji : j ≤ jj i := le_jj hj16 hij
      have : Real.exp (-(jj i : ℝ)) ≤ Real.exp (-(j:ℝ)) := by
        apply Real.exp_le_exp.2
        have : (j:ℝ) ≤ (jj i : ℝ) := by exact_mod_cast hjji
        linarith
      have := hgle i
      linarith
    calc ∑ i ∈ Ico (aa j) (aa (j+1)), g i
        ≤ ∑ _i ∈ Ico (aa j) (aa (j+1)), 4 * Real.exp (-(j:ℝ)) := Finset.sum_le_sum hpt
      _ = ((aa (j+1) - aa j : ℕ) : ℝ) * (4 * Real.exp (-(j:ℝ))) := by
          rw [Finset.sum_const, Nat.card_Ico]
          simp [nsmul_eq_mul]
      _ ≤ (aa (j+1) : ℝ) * (4 * Real.exp (-(j:ℝ))) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Nat.sub_le _ _
      _ = 4 * (aa (j+1) : ℝ) * Real.exp (-(j:ℝ)) := by ring
      _ ≤ vv j := aa_succ_le j
  calc ∑ i ∈ range I, g i
      ≤ ∑ i ∈ range (aa J), g i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hIJ)
        · intro i _ _
          exact hgnn i
    _ = ∑ i ∈ range (aa 16), g i + ∑ i ∈ Ico (aa 16) (aa J), g i :=
        (Finset.sum_range_add_sum_Ico g (aa_mono h16J)).symm
    _ = ∑ i ∈ Ico (aa 16) (aa J), g i := by rw [hzero, zero_add]
    _ = ∑ j ∈ Ico 16 J, ∑ i ∈ Ico (aa j) (aa (j+1)), g i := sum_Ico_partition g h16J
    _ ≤ ∑ j ∈ Ico 16 J, vv j := Finset.sum_le_sum hinner
    _ ≤ ∑ j ∈ range J, vv j := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          exact Finset.mem_range.2 (Finset.mem_Ico.1 hx).2
        · intro i _ _
          exact vv_nonneg i
    _ ≤ ∑' j, vv j := Summable.sum_le_tsum _ (fun i _ => vv_nonneg i) summable_vv

/-- Every partial sum of the block sums is bounded. -/
lemma sum_block_le (I : ℕ) :
    ∑ i ∈ range I, block i ≤ (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹ := by
  classical
  have hpt : ∀ i, block i ≤ (if i < aa 16 then (1:ℝ) else 0)
      + (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) + 2 * rt^i := by
    intro i
    by_cases h : i < aa 16
    · rw [if_pos h, if_neg (by omega)]
      have := block_le_one i
      have h2 : (0:ℝ) ≤ 2 * rt^i :=
        mul_nonneg (by norm_num) (pow_nonneg rt_nonneg i)
      linarith
    · rw [if_neg h, if_pos (by omega)]
      have hi : aa 16 ≤ i := by omega
      obtain ⟨h1, h2⟩ := jj_spec hi
      have := block_le i (jj i) h1 h2
      linarith
  have hgeo : ∑ i ∈ range I, (2 : ℝ) * rt^i ≤ 2 * (1 - rt)⁻¹ := by
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    have hsum : Summable (fun i : ℕ => rt^i) := summable_geometric_of_lt_one rt_nonneg rt_lt_one
    calc ∑ i ∈ range I, rt^i ≤ ∑' i : ℕ, rt^i :=
          Summable.sum_le_tsum _ (fun i _ => pow_nonneg rt_nonneg i) hsum
      _ = (1 - rt)⁻¹ := tsum_geometric_of_lt_one rt_nonneg rt_lt_one
  have hcount : ∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0) ≤ (aa 16 : ℝ) := by
    calc ∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0)
        = (#((range I).filter (fun i => i < aa 16)) : ℝ) := by
          rw [← Finset.sum_filter, Finset.sum_const]
          simp
      _ ≤ (aa 16 : ℝ) := by
          have hsub : (range I).filter (fun i => i < aa 16) ⊆ range (aa 16) := by
            intro x hx
            exact Finset.mem_range.2 (Finset.mem_filter.1 hx).2
          have := Finset.card_le_card hsub
          rw [Finset.card_range] at this
          exact_mod_cast this
  calc ∑ i ∈ range I, block i
      ≤ ∑ i ∈ range I, ((if i < aa 16 then (1:ℝ) else 0)
          + (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0) + 2 * rt^i) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = (∑ i ∈ range I, (if i < aa 16 then (1:ℝ) else 0))
        + (∑ i ∈ range I, (if aa 16 ≤ i then 4 * Real.exp (-(jj i : ℝ)) else 0))
        + ∑ i ∈ range I, (2:ℝ) * rt^i := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹ := by
        have := tail_sum_le I
        linarith

/-- Dyadic decomposition of a partial sum. -/
lemma sum_Ico_dyadic (I : ℕ) :
    ∑ n ∈ Ico 1 (2^I), twinRecip n = ∑ i ∈ range I, block i := by
  induction I with
  | zero => simp
  | succ I ih =>
    rw [Finset.sum_range_succ, ← ih, block]
    rw [Finset.sum_Ico_consecutive]
    · exact Nat.one_le_two_pow
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges. -/
theorem summable_twinRecip : Summable twinRecip := by
  apply summable_of_sum_range_le (c := (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹)
    twinRecip_nonneg
  intro M
  have hM : M ≤ 2^M := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h1 : ∑ n ∈ range M, twinRecip n ≤ ∑ n ∈ range (2^M), twinRecip n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hM)
    · intro i _ _
      exact twinRecip_nonneg i
  have h2 : ∑ n ∈ range (2^M), twinRecip n
      = twinRecip 0 + ∑ n ∈ Ico 1 (2^M), twinRecip n := by
    have := Finset.sum_range_add_sum_Ico twinRecip (m := 1) (n := 2^M) Nat.one_le_two_pow
    rw [← this]
    simp
  have h3 : twinRecip 0 = 0 := by
    unfold twinRecip
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd h (by norm_num)
  rw [h2, h3, zero_add, sum_Ico_dyadic] at h1
  exact h1.trans (sum_block_le M)

end Brun

import Mathlib

/-!
# Counting `n < N` with `n (n+2)` divisible by a set of odd primes

The main result is `Brun.card_divisible_approx`: for a finite set `T` of odd primes,
the number of `n < N` such that every `p ∈ T` divides `n (n+2)` differs from
`N * 2 ^ |T| / ∏ p ∈ T, p` by at most `2 ^ |T|`.
-/

open Finset

namespace Brun

section Periodic

variable (P : ℕ → Prop) [DecidablePred P]

lemma count_add_period (M : ℕ) (hper : ∀ n, P (n + M) ↔ P n) (n : ℕ) :
    #((range (n + M)).filter P) = #((range n).filter P) + #((range M).filter P) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : k + 1 + M = (k + M) + 1 := by ring
    rw [h1, Finset.range_add_one, Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases h : P k
    · have h2 : P (k + M) := (hper k).mpr h
      rw [if_pos h2, if_pos h, Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp), ih]
      omega
    · have h2 : ¬ P (k + M) := fun hc => h ((hper k).mp hc)
      rw [if_neg h2, if_neg h, ih]

lemma count_mul_period (M : ℕ) (hper : ∀ n, P (n + M) ↔ P n) (q s : ℕ) :
    #((range (q * M + s)).filter P) = q * #((range M).filter P) + #((range s).filter P) := by
  induction q with
  | zero => simp
  | succ k ih =>
    have h1 : (k+1) * M + s = (k * M + s) + M := by ring
    rw [h1, count_add_period P M hper, ih]
    ring

lemma count_mono (a b : ℕ) (h : a ≤ b) : #((range a).filter P) ≤ #((range b).filter P) := by
  have hsub : range a ⊆ range b := fun x hx =>
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) h)
  exact Finset.card_le_card (Finset.filter_subset_filter _ hsub)

/-- Counting a periodic predicate in `[0,N)`: the count differs from `N ρ / M` by at most `ρ`. -/
lemma count_periodic_approx (M : ℕ) (hM : 0 < M) (hper : ∀ n, P (n + M) ↔ P n) (N : ℕ) :
    |(#((range N).filter P) : ℝ) - N * (#((range M).filter P) : ℝ) / M| ≤
      #((range M).filter P) := by
  set ρ := #((range M).filter P) with hρ
  obtain ⟨q, s, hs, rfl⟩ : ∃ q s, s < M ∧ N = q * M + s :=
    ⟨N / M, N % M, Nat.mod_lt _ hM, by rw [Nat.mul_comm]; exact (Nat.div_add_mod N M).symm⟩
  rw [count_mul_period P M hper]
  have hle : #((range s).filter P) ≤ ρ := count_mono P s M hs.le
  have hM' : (0:ℝ) < M := by exact_mod_cast hM
  have hsM : (s:ℝ) ≤ M := by exact_mod_cast hs.le
  have hle' : ((#((range s).filter P) : ℕ) : ℝ) ≤ (ρ:ℝ) := by exact_mod_cast hle
  have hnn : (0:ℝ) ≤ ((#((range s).filter P) : ℕ) : ℝ) := by positivity
  have hρ0 : (0:ℝ) ≤ (ρ:ℝ) := by positivity
  have key : (((q:ℝ) * M + s)) * (ρ:ℝ) / M = q * ρ + s * ρ / M := by field_simp
  push_cast
  rw [key]
  have hb1 : (0:ℝ) ≤ (s:ℝ) * ρ / M := by positivity
  have hb2 : (s:ℝ) * ρ / M ≤ ρ := by
    rw [div_le_iff₀ hM']
    nlinarith
  rw [abs_le]
  constructor <;> linarith

end Periodic

/-- There is exactly one `n < a b` with `a ∣ n` and `b ∣ n + 2`, when `a` and `b` are coprime. -/
lemma crt_count_one (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    #((range (a*b)).filter (fun n => a ∣ n ∧ b ∣ n + 2)) = 1 := by
  classical
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hab 0 (2*b - 2)
  have hka : a ∣ k := (Nat.modEq_zero_iff_dvd).1 hk1
  have hkb : b ∣ k + 2 := by
    have h2 : k + 2 ≡ (2*b - 2) + 2 [MOD b] := Nat.ModEq.add_right 2 hk2
    have h3 : (2*b - 2) + 2 = 2*b := by omega
    rw [h3] at h2
    exact (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 ⟨2, by ring⟩))
  set x := k % (a*b) with hx
  have hxlt : x < a*b := Nat.mod_lt _ (by positivity)
  have hxa : a ∣ x := by
    have h : x ≡ k [MOD a] := (Nat.mod_modEq k (a*b)).of_dvd ⟨b, rfl⟩
    exact (Nat.modEq_zero_iff_dvd).1 (h.trans ((Nat.modEq_zero_iff_dvd).2 hka))
  have hxb : b ∣ x + 2 := by
    have h : x + 2 ≡ k + 2 [MOD b] :=
      Nat.ModEq.add_right 2 ((Nat.mod_modEq k (a*b)).of_dvd ⟨a, by ring⟩)
    exact (Nat.modEq_zero_iff_dvd).1 (h.trans ((Nat.modEq_zero_iff_dvd).2 hkb))
  rw [Finset.card_eq_one]
  refine ⟨x, ?_⟩
  rw [Finset.eq_singleton_iff_unique_mem]
  refine ⟨by simp [Finset.mem_filter, Finset.mem_range, hxlt, hxa, hxb], ?_⟩
  intro y hy
  simp only [Finset.mem_filter, Finset.mem_range] at hy
  obtain ⟨hylt, hya, hyb⟩ := hy
  have key : ∀ u v : ℕ, v < a*b → a ∣ u → b ∣ u + 2 → a ∣ v → b ∣ v + 2 → u ≤ v → u = v := by
    intro u v hv hua hub hva hvb huv
    have h1 : a ∣ v - u := Nat.dvd_sub hva hua
    have h2 : b ∣ v - u := by
      have := Nat.dvd_sub hvb hub
      simpa [Nat.add_sub_add_right] using this
    have h3 : a*b ∣ v - u := Nat.Coprime.mul_dvd_of_dvd_of_dvd hab h1 h2
    have h5 : v - u = 0 := by
      rcases Nat.eq_zero_or_pos (v - u) with h | h
      · exact h
      · exact absurd (Nat.le_of_dvd h h3) (by omega)
    omega
  rcases le_total y x with h | h
  · exact (key y x hxlt hya hyb hxa hxb h)
  · exact (key x y hylt hxa hxb hya hyb h).symm

/-- Counting `n < N` in a fixed pair of coprime congruence classes. -/
lemma count_pair_approx (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b) :
    |(#((range N).filter (fun n => a ∣ n ∧ b ∣ n + 2)) : ℝ) - N / (a*b)| ≤ 1 := by
  classical
  have hper : ∀ n : ℕ, (a ∣ n + a*b ∧ b ∣ (n + a*b) + 2) ↔ (a ∣ n ∧ b ∣ n + 2) := by
    intro n
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨(Nat.dvd_add_iff_left (⟨b, rfl⟩ : a ∣ a*b)).2 h1, ?_⟩
      have h3 : n + a*b + 2 = (n + 2) + a*b := by ring
      rw [h3] at h2
      exact (Nat.dvd_add_iff_left (⟨a, by ring⟩ : b ∣ a*b)).2 h2
    · rintro ⟨h1, h2⟩
      refine ⟨Dvd.dvd.add h1 ⟨b, rfl⟩, ?_⟩
      have h3 : n + a*b + 2 = (n + 2) + a*b := by ring
      rw [h3]
      exact Dvd.dvd.add h2 ⟨a, by ring⟩
  have := count_periodic_approx (fun n => a ∣ n ∧ b ∣ n + 2) (a*b) (by positivity) hper N
  rw [crt_count_one a b ha hb hab] at this
  simpa using this


/-- The decomposition of the counted set according to which primes divide `n` (rather
than `n + 2`). -/
lemma filter_dvd_eq_biUnion (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    (range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2)) =
      T.powerset.biUnion (fun U => (range N).filter
        (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion, Finset.mem_powerset]
  constructor
  · rintro ⟨hn, hdvd⟩
    refine ⟨T.filter (· ∣ n), Finset.filter_subset _ _, hn, ?_, ?_⟩
    · exact Finset.prod_primes_dvd n
        (fun p hp => Nat.Prime.prime (hT p (Finset.mem_filter.1 hp).1).1)
        (fun p hp => (Finset.mem_filter.1 hp).2)
    · rw [← Finset.filter_not]
      refine Finset.prod_primes_dvd _
        (fun p hp => Nat.Prime.prime (hT p (Finset.mem_filter.1 hp).1).1) ?_
      intro p hp
      obtain ⟨hpT, hpn⟩ := Finset.mem_filter.1 hp
      rcases (Nat.Prime.dvd_mul (hT p hpT).1).1 (hdvd p hpT) with h | h
      · exact absurd h hpn
      · exact h
  · rintro ⟨U, hUT, hn, h1, h2⟩
    refine ⟨hn, ?_⟩
    intro p hp
    by_cases hpU : p ∈ U
    · exact Dvd.dvd.mul_right (dvd_trans (Finset.dvd_prod_of_mem _ hpU) h1) _
    · have hmem : p ∈ T \ U := Finset.mem_sdiff.2 ⟨hp, hpU⟩
      exact Dvd.dvd.mul_left (dvd_trans (Finset.dvd_prod_of_mem _ hmem) h2) _

/-- The pieces of the above decomposition are pairwise disjoint. -/
lemma pairwiseDisjoint_pieces (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    ((T.powerset : Finset (Finset ℕ)) : Set (Finset ℕ)).PairwiseDisjoint
      (fun U => (range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) := by
  classical
  have key : ∀ U V : Finset ℕ, U ⊆ T → V ⊆ T → (∃ p, p ∈ U ∧ p ∉ V) →
      Disjoint ((range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2))
        ((range N).filter (fun n => (∏ p ∈ V, p) ∣ n ∧ (∏ p ∈ T \ V, p) ∣ n+2)) := by
    intro U V hU hV ⟨p, hpU, hpV⟩
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter] at hn1 hn2
    have hpT : p ∈ T := hU hpU
    have hpn : p ∣ n := dvd_trans (Finset.dvd_prod_of_mem _ hpU) hn1.2.1
    have hpn2 : p ∣ n + 2 :=
      dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_sdiff.2 ⟨hpT, hpV⟩)) hn2.2.2
    have hd2 : p ∣ 2 := (Nat.dvd_add_right hpn).1 hpn2
    exact (hT p hpT).2 ((Nat.prime_dvd_prime_iff_eq (hT p hpT).1 Nat.prime_two).1 hd2)
  intro U hU V hV hUV
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset] at hU hV
  by_cases h : ∃ p, p ∈ U ∧ p ∉ V
  · exact key U V hU hV h
  · push_neg at h
    have h2 : ∃ p, p ∈ V ∧ p ∉ U := by
      by_contra hc
      push_neg at hc
      exact hUV (Finset.Subset.antisymm h hc)
    exact (key V U hV hU h2).symm

/-- Each piece of the decomposition has cardinality within `1` of `N / ∏ p ∈ T, p`. -/
lemma piece_approx (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) (U : Finset ℕ)
    (hU : U ⊆ T) :
    |(#((range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ)
      - N / (∏ p ∈ T, p)| ≤ 1 := by
  classical
  set a := ∏ p ∈ U, p with hha
  set b := ∏ p ∈ T \ U, p with hhb
  have hab : a * b = ∏ p ∈ T, p := by
    rw [hha, hhb, mul_comm]
    exact Finset.prod_sdiff hU
  have ha : 0 < a := Finset.prod_pos (fun p hp => (hT p (hU hp)).1.pos)
  have hb : 0 < b := Finset.prod_pos (fun p hp => (hT p (Finset.mem_sdiff.1 hp).1).1.pos)
  have hcop : Nat.Coprime a b := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    have hne : p ≠ q := by
      rintro rfl
      exact (Finset.mem_sdiff.1 hq).2 hp
    exact (Nat.coprime_primes (hT p (hU hp)).1 (hT q (Finset.mem_sdiff.1 hq).1).1).2 hne
  rw [← hab]
  push_cast
  exact count_pair_approx a b N ha hb hcop

/-- **Main counting estimate.** For a finite set `T` of odd primes, the number of `n < N`
with `n (n+2)` divisible by every `p ∈ T` is `N * 2 ^ |T| / ∏ p ∈ T, p` up to an error of
at most `2 ^ |T|`. -/
theorem card_divisible_approx (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    |(#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℝ)
      - N * 2 ^ T.card / (∏ p ∈ T, p)| ≤ 2 ^ T.card := by
  classical
  rw [filter_dvd_eq_biUnion T hT N, Finset.card_biUnion (pairwiseDisjoint_pieces T hT N)]
  have hsplit : (N : ℝ) * 2 ^ T.card / (∏ p ∈ T, p)
      = ∑ U ∈ T.powerset, (N : ℝ) / (∏ p ∈ T, p) := by
    rw [Finset.sum_const, Finset.card_powerset]
    simp [nsmul_eq_mul]
    ring
  rw [hsplit, Nat.cast_sum, ← Finset.sum_sub_distrib]
  calc |∑ U ∈ T.powerset, ((#((range N).filter
          (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ) - N / (∏ p ∈ T, p))|
      ≤ ∑ U ∈ T.powerset, |(#((range N).filter
          (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ) - N / (∏ p ∈ T, p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ U ∈ T.powerset, (1:ℝ) := by
        refine Finset.sum_le_sum fun U hU => piece_approx T hT N U (Finset.mem_powerset.1 hU)
    _ = 2 ^ T.card := by rw [Finset.sum_const, Finset.card_powerset]; simp

end Brun

import RequestProject.Brun.Sieve

/-!
# Analytic estimates for Brun's pure sieve

We bound the main term and the error term of `Brun.sieve_main`, obtaining
`Brun.sifted_bound`: with `S = ∑ p ∈ Q, 2/p` and `K` even with `(e+1) S ≤ K + 1`,
the number of `n < N` with `n (n+2)` coprime to all `p ∈ Q` is at most
`2 N exp (-S) + (K+1) (2 |Q| + 2) ^ K`.
-/

open Finset

namespace Brun

variable (Q : Finset ℕ)

/-- `∏ (1 - 2/p) ≤ exp (-S)`. -/
lemma prod_one_sub_le_exp (hQ : ∀ p ∈ Q, 3 ≤ p) :
    ∏ p ∈ Q, (1 - 2/(p:ℝ)) ≤ Real.exp (-(∑ p ∈ Q, 2/(p:ℝ))) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    have : 2/(p:ℝ) ≤ 2/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h3
    linarith
  · intro p _
    have := Real.add_one_le_exp (-(2/(p:ℝ)))
    linarith

/-- Full inclusion–exclusion sum over all subsets. -/
lemma sum_powerset_alt (Q : Finset ℕ) :
    ∑ T ∈ Q.powerset, (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)) = ∏ p ∈ Q, (1 - 2/(p:ℝ)) := by
  have h := Finset.prod_add (fun p : ℕ => -(2/(p:ℝ))) (fun _ => (1:ℝ)) Q
  simp only [Finset.prod_const_one, mul_one] at h
  rw [show (fun p : ℕ => -(2/(p:ℝ)) + 1) = (fun p : ℕ => 1 - 2/(p:ℝ)) by funext p; ring] at h
  rw [h]
  exact Finset.sum_congr rfl fun T _ => (Finset.prod_neg (fun p : ℕ => (2/(p:ℝ)))).symm

/-- The tail of the inclusion–exclusion sum is small. -/
lemma tail_le (hQ : ∀ p ∈ Q, 3 ≤ p) (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ))
      ≤ Real.exp (Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
  classical
  set e := Real.exp 1 with he
  have he0 : (0:ℝ) < e := Real.exp_pos 1
  have hpos : ∀ p ∈ Q, (0:ℝ) < p := by
    intro p hp
    have : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    linarith
  have step1 : ∀ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
      ∏ p ∈ T, (2/(p:ℝ)) ≤ Real.exp (-(K+1)) * ∏ p ∈ T, (2*e/(p:ℝ)) := by
    intro T hT
    have hcard : K + 1 ≤ T.card := by
      have := (Finset.mem_filter.1 hT).2
      omega
    have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
    have hfac : ∏ p ∈ T, (2*e/(p:ℝ)) = e^T.card * ∏ p ∈ T, (2/(p:ℝ)) := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun p _ => by ring
    rw [hfac, ← mul_assoc]
    have hprodnn : (0:ℝ) ≤ ∏ p ∈ T, (2/(p:ℝ)) :=
      Finset.prod_nonneg fun p hp => by
        have := hpos p (hTQ hp); positivity
    have hcoef : (1:ℝ) ≤ Real.exp (-(K+1)) * e^T.card := by
      rw [he, ← Real.exp_nat_mul, ← Real.exp_add,
        show -((K:ℝ)+1) + T.card * 1 = (T.card : ℝ) - (K+1) by ring, Real.one_le_exp_iff]
      have : ((K:ℝ)+1) ≤ T.card := by exact_mod_cast hcard
      linarith
    nlinarith
  calc ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ))
      ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
          Real.exp (-(K+1)) * ∏ p ∈ T, (2*e/(p:ℝ)) := Finset.sum_le_sum step1
    _ = Real.exp (-(K+1)) *
          ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2*e/(p:ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(K+1)) * ∑ T ∈ Q.powerset, ∏ p ∈ T, (2*e/(p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro T hT _
        exact Finset.prod_nonneg fun p hp => by
          have := hpos p (Finset.mem_powerset.1 hT hp); positivity
    _ = Real.exp (-(K+1)) * ∏ p ∈ Q, (1 + 2*e/(p:ℝ)) := by
        congr 1
        have h := Finset.prod_add (fun p : ℕ => (2*e/(p:ℝ))) (fun _ => (1:ℝ)) Q
        simp only [Finset.prod_const_one, mul_one] at h
        rw [show (fun p : ℕ => (2*e/(p:ℝ)) + 1) = (fun p : ℕ => 1 + 2*e/(p:ℝ)) by
          funext p; ring] at h
        rw [h]
    _ ≤ Real.exp (-(K+1)) * Real.exp (e * ∑ p ∈ Q, 2/(p:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        rw [Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_le_prod
        · intro p hp
          have := hpos p hp; positivity
        · intro p _
          have h1 := Real.add_one_le_exp (e * (2/(p:ℝ)))
          have h2 : e * (2/(p:ℝ)) = 2*e/(p:ℝ) := by ring
          rw [h2] at h1 ⊢
          linarith
    _ = Real.exp (e * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
        rw [← Real.exp_add]; ring_nf

/-- The truncated main term of the sieve. -/
lemma main_term_le (hQ : ∀ p ∈ Q, 3 ≤ p) (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
      ≤ Real.exp (-(∑ p ∈ Q, 2/(p:ℝ)))
        + Real.exp (Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) - (K+1)) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not Q.powerset (fun T => T.card ≤ K)
    (fun T => (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
  rw [sum_powerset_alt Q] at hsplit
  have hpos : ∀ p ∈ Q, (0:ℝ) < p := by
    intro p hp
    have : (3:ℝ) ≤ p := by exact_mod_cast hQ p hp
    linarith
  have habs : -∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
      ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ)) := by
    calc -∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))
        ≤ |∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))| := neg_le_abs _
      _ ≤ ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K),
            |(-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ))| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ T ∈ Q.powerset.filter (fun T => ¬ T.card ≤ K), ∏ p ∈ T, (2/(p:ℝ)) := by
          refine Finset.sum_congr rfl fun T hT => ?_
          have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
          rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg]
          exact Finset.prod_nonneg fun p hp => by
            have := hpos p (hTQ hp); positivity
  have h1 := prod_one_sub_le_exp Q hQ
  have h2 := tail_le Q hQ K
  linarith

/-- Sum over small subsets, by cardinality (real-valued version). -/
lemma sum_powerset_filter_card_real (R : Finset ℕ) (K : ℕ) (f : ℕ → ℝ) :
    ∑ T ∈ R.powerset.filter (fun T => T.card ≤ K), f T.card
      = ∑ j ∈ range (K+1), (R.card.choose j : ℝ) * f j := by
  classical
  have hset : R.powerset.filter (fun T => T.card ≤ K)
      = (range (K+1)).biUnion (fun j => R.powersetCard j) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨T.card, h2, h1, rfl⟩
    · rintro ⟨a, ha, h1, rfl⟩
      exact ⟨h1, ha⟩
  rw [hset, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2] :
      ∀ T ∈ R.powersetCard j, f T.card = f j)]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp [mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left]
    intro T hT hT'
    exact hij ((Finset.mem_powersetCard.1 hT).2 ▸ (Finset.mem_powersetCard.1 hT').2 ▸ rfl)

/-- The error term of the sieve. -/
lemma error_le (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card
      ≤ (K+1) * (2*Q.card + 2)^K := by
  classical
  rw [sum_powerset_filter_card_real Q K (fun j => (2:ℝ)^j)]
  have hterm : ∀ j ∈ range (K+1), (Q.card.choose j : ℝ) * 2^j ≤ (2*Q.card + 2)^K := by
    intro j hj
    have hjK : j ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : (Q.card.choose j : ℝ) ≤ (Q.card : ℝ)^j := by
      exact_mod_cast Nat.choose_le_pow Q.card j
    have h2 : (Q.card : ℝ)^j * 2^j = (2*Q.card)^j := by
      rw [← mul_pow]; ring_nf
    have h3 : ((2:ℝ)*Q.card)^j ≤ (2*Q.card + 2)^K := by
      calc ((2:ℝ)*Q.card)^j ≤ (2*Q.card + 2)^j :=
            pow_le_pow_left₀ (by positivity) (by linarith) j
        _ ≤ (2*Q.card + 2)^K := by
            apply pow_le_pow_right₀ _ hjK
            have : (0:ℝ) ≤ Q.card := by positivity
            linarith
    calc (Q.card.choose j : ℝ) * 2^j ≤ (Q.card : ℝ)^j * 2^j := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2*Q.card)^j := h2
      _ ≤ (2*Q.card + 2)^K := h3
  calc ∑ j ∈ range (K+1), (Q.card.choose j : ℝ) * 2^j
      ≤ ∑ _j ∈ range (K+1), ((2*Q.card + 2)^K : ℝ) := Finset.sum_le_sum hterm
    _ = (K+1) * (2*Q.card + 2)^K := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul]

/-- **The sieve bound.** -/
theorem sifted_bound (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2) (N K : ℕ) (hK : Even K)
    (hKS : Real.exp 1 * (∑ p ∈ Q, 2/(p:ℝ)) + (∑ p ∈ Q, 2/(p:ℝ)) ≤ K + 1) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ 2 * N * Real.exp (-(∑ p ∈ Q, 2/(p:ℝ))) + (K+1) * (2*Q.card + 2)^K := by
  classical
  have hQ3 : ∀ p ∈ Q, 3 ≤ p := by
    intro p hp
    have := (hQ p hp).1.two_le
    have := (hQ p hp).2
    omega
  set S := ∑ p ∈ Q, 2/(p:ℝ) with hS
  have h1 := sieve_main Q hQ N K hK
  have h2 := main_term_le Q hQ3 K
  have h3 := error_le Q K
  have htail : Real.exp (Real.exp 1 * S - (K+1)) ≤ Real.exp (-S) := by
    apply Real.exp_le_exp.2
    linarith
  have hNnn : (0:ℝ) ≤ N := by positivity
  calc (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ N * (∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
              (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
        + ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card := h1
    _ ≤ N * (Real.exp (-S) + Real.exp (Real.exp 1 * S - (K+1))) + (K+1) * (2*Q.card + 2)^K := by
        gcongr
    _ ≤ N * (Real.exp (-S) + Real.exp (-S)) + (K+1) * (2*Q.card + 2)^K := by
        gcongr
    _ = 2 * N * Real.exp (-S) + (K+1) * (2*Q.card + 2)^K := by ring

end Brun

import Mathlib

/-!
# A Mertens-type lower bound for the sum of reciprocals of primes

We prove `∑_{p < N} 1/p ≥ log log N - log 2` for `N ≥ 3`, by the classical argument
`log N ≤ H_N ≤ (∑_{a ≤ N squarefree} 1/a) * (∑_b 1/b²) ≤ 2 ∏_{p < N} (1 + 1/p) ≤ 2 exp(∑ 1/p)`.
-/

open Finset

namespace Brun

/-- The sum of `1/b²` for `1 ≤ b ≤ n` is at most `2 - 1/n`. -/
lemma sum_one_div_sq_le' (n : ℕ) (hn : 1 ≤ n) :
    ∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 - 1 / n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hn with h | h
    · simp [← h]; norm_num
    · have hm : 1 ≤ m := by omega
      rw [Finset.sum_Icc_succ_top (by omega)]
      have := ih hm
      have hm0 : (0:ℝ) < m := by exact_mod_cast hm
      have h1 : (1:ℝ)/((m:ℝ)+1)^2 ≤ 1/m - 1/(m+1) := by
        have he : 1/(m:ℝ) - 1/((m:ℝ)+1) = 1/((m:ℝ)*((m:ℝ)+1)) := by field_simp; ring
        rw [he]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
      push_cast
      linarith

/-- The sum of `1/b²` for `b ≤ n` is at most `2`. -/
lemma sum_one_div_sq_le (n : ℕ) : ∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have := sum_one_div_sq_le' n h
    have : (0:ℝ) < n := by exact_mod_cast h
    have h2 := sum_one_div_sq_le' n (by omega)
    have : (0:ℝ) ≤ 1 / (n:ℝ) := by positivity
    linarith

/-- Bounding the harmonic sum by (squarefree sum) * (sum of inverse squares). -/
lemma harmonic_le_mul (n : ℕ) :
    ∑ k ∈ Icc 1 n, (1 : ℝ) / k ≤
      (∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a) *
        (∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2) := by
  classical
  have H : ∀ k : ℕ, ∃ p : ℕ × ℕ, p.2 ^ 2 * p.1 = k ∧ Squarefree p.1 := by
    intro k
    obtain ⟨a, b, h1, h2⟩ := Nat.sq_mul_squarefree k
    exact ⟨(a, b), h1, h2⟩
  choose f hf1 hf2 using H
  set A := (Icc 1 n).filter Squarefree with hA
  set B := Icc 1 n with hB
  have hmapsto : ∀ k ∈ Icc 1 n, f k ∈ A ×ˢ B := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 := hf1 k
    have hk1 : 1 ≤ k := hk.1
    have ha1 : 1 ≤ (f k).1 := by
      rcases Nat.eq_zero_or_pos (f k).1 with h | h
      · rw [h, Nat.mul_zero] at h1; omega
      · omega
    have hb1 : 1 ≤ (f k).2 := by
      rcases Nat.eq_zero_or_pos (f k).2 with h | h
      · rw [h] at h1; simp at h1; omega
      · omega
    have ha2 : (f k).1 ≤ n := by
      have : (f k).1 ≤ k := by
        calc (f k).1 ≤ (f k).2 ^ 2 * (f k).1 := Nat.le_mul_of_pos_left _ (by positivity)
          _ = k := h1
      omega
    have hb2 : (f k).2 ≤ n := by
      have : (f k).2 ≤ k := by
        calc (f k).2 ≤ (f k).2 ^ 2 := by nlinarith
          _ ≤ (f k).2 ^ 2 * (f k).1 := Nat.le_mul_of_pos_right _ (by omega)
          _ = k := h1
      omega
    simp only [Finset.mem_product, hA, hB, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨ha1, ha2⟩, hf2 k⟩, hb1, hb2⟩
  have hinj : Set.InjOn f ((Icc 1 n : Finset ℕ) : Set ℕ) := by
    intro x _ y _ h
    rw [← hf1 x, ← hf1 y, h]
  calc ∑ k ∈ Icc 1 n, (1:ℝ)/k
      = ∑ k ∈ Icc 1 n, ((1:ℝ)/((f k).1) * (1/((f k).2:ℝ)^2)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have hcast : ((k:ℝ)) = ((f k).2:ℝ)^2 * ((f k).1:ℝ) := by exact_mod_cast (hf1 k).symm
        rw [hcast]; ring
    _ = ∑ p ∈ (Icc 1 n).image f, ((1:ℝ)/(p.1) * (1/(p.2:ℝ)^2)) :=
        (Finset.sum_image (f := fun p : ℕ × ℕ => (1:ℝ)/(p.1:ℝ) * (1/(p.2:ℝ)^2)) hinj).symm
    _ ≤ ∑ p ∈ A ×ˢ B, ((1:ℝ)/(p.1) * (1/(p.2:ℝ)^2)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          simp only [Finset.mem_image] at hp
          obtain ⟨k, hk, rfl⟩ := hp
          exact hmapsto k hk
        · intro p _ _; positivity
    _ = (∑ a ∈ A, (1:ℝ)/a) * (∑ b ∈ B, (1:ℝ)/(b:ℝ)^2) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]

/-- The sum of reciprocals of squarefree numbers up to `n` is at most `∏_{p ≤ n} (1 + 1/p)`. -/
lemma sum_squarefree_le_prod (n : ℕ) :
    ∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a ≤
      ∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p) := by
  classical
  set S := (Icc 1 n).filter Squarefree with hS
  set P := Nat.primesBelow (n+1) with hP
  have hmem : ∀ a ∈ S, 1 ≤ a ∧ a ≤ n ∧ Squarefree a := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  have hprod : ∀ a ∈ S, ∏ p ∈ a.primeFactors, (1:ℝ)/p = 1/a := by
    intro a ha
    obtain ⟨h1, h2, h3⟩ := hmem a ha
    have h4 : ∏ p ∈ a.primeFactors, p = a := Nat.prod_primeFactors_of_squarefree h3
    rw [Finset.prod_div_distrib, ← Nat.cast_prod, h4]
    simp
  have hinj : Set.InjOn Nat.primeFactors (S : Set ℕ) := by
    intro x hx y hy h
    obtain ⟨_, _, h3⟩ := hmem x hx
    obtain ⟨_, _, h3'⟩ := hmem y hy
    rw [← Nat.prod_primeFactors_of_squarefree h3, ← Nat.prod_primeFactors_of_squarefree h3', h]
  have hsub : S.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    simp only [Finset.mem_image] at hT
    obtain ⟨a, ha, rfl⟩ := hT
    obtain ⟨h1, h2, h3⟩ := hmem a ha
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [hP, Nat.mem_primesBelow]
    exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (by omega) hp.2.1) (by omega), hp.1⟩
  calc ∑ a ∈ S, (1:ℝ)/a = ∑ a ∈ S, ∏ p ∈ a.primeFactors, (1:ℝ)/p :=
        (Finset.sum_congr rfl hprod).symm
    _ = ∑ T ∈ S.image Nat.primeFactors, ∏ p ∈ T, (1:ℝ)/p :=
        (Finset.sum_image (f := fun T : Finset ℕ => ∏ p ∈ T, (1:ℝ)/(p:ℝ)) hinj).symm
    _ ≤ ∑ T ∈ P.powerset, ∏ p ∈ T, (1:ℝ)/p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro T _ _
        positivity
    _ = ∏ p ∈ P, ((1:ℝ)/p + 1) := by rw [Finset.prod_add]; simp
    _ = ∏ p ∈ P, (1 + (1:ℝ)/p) := by simp [add_comm]

/-- `∏ (1 + 1/p) ≤ exp (∑ 1/p)`. -/
lemma prod_one_add_le_exp (P : Finset ℕ) :
    ∏ p ∈ P, (1 + (1 : ℝ) / p) ≤ Real.exp (∑ p ∈ P, (1 : ℝ) / p) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p _; positivity
  · intro p _
    have := Real.add_one_le_exp ((1:ℝ)/p)
    linarith

/-- Mertens-type lower bound: `∑_{p < N} 1/p ≥ log log N - log 2`. -/
theorem sum_one_div_primesBelow_ge (N : ℕ) (hN : 3 ≤ N) :
    Real.log (Real.log N) - Real.log 2 ≤ ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  have hharm : Real.log ((n:ℝ) + 1) ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) / k := by
    have h := log_add_one_le_harmonic n
    have h2 : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Icc 1 n, (1 : ℝ) / k := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [h2] at h
    simpa using h
  have hchain : Real.log ((n:ℝ) + 1) ≤ 2 * Real.exp (∑ p ∈ Nat.primesBelow (n+1), (1 : ℝ) / p) := by
    calc Real.log ((n:ℝ)+1) ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) / k := hharm
      _ ≤ (∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a) *
            (∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2) := harmonic_le_mul n
      _ ≤ (∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p)) * 2 := by
          apply mul_le_mul (sum_squarefree_le_prod n) (sum_one_div_sq_le n)
          · positivity
          · exact le_trans (by positivity) (sum_squarefree_le_prod n)
      _ = 2 * (∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p)) := by ring
      _ ≤ 2 * Real.exp (∑ p ∈ Nat.primesBelow (n+1), (1 : ℝ) / p) := by
          have := prod_one_add_le_exp (Nat.primesBelow (n+1))
          linarith
  have hlogpos : 0 < Real.log ((n:ℝ)+1) := by
    apply Real.log_pos
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have := Real.log_le_log (by positivity) hchain
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at this
  push_cast
  linarith

end Brun

import RequestProject.Brun.Counting

/-!
# Brun's pure sieve

Truncated inclusion–exclusion (Bonferroni) applied to the twin prime sieve.
The main result of this file, `Brun.sieve_main`, bounds the number of `n < N` such that
`n (n+2)` is coprime to all primes in a finite set `Q` of odd primes.
-/

open Finset

namespace Brun

/-- Alternating sum of binomial coefficients. -/
lemma alt_sum_choose (s K : ℕ) :
    ∑ j ∈ range (K+1), (-1:ℤ)^j * ((s+1).choose j) = (-1)^K * (s.choose K) := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hpascal : ((s+1).choose (m+1) : ℤ) = s.choose m + s.choose (m+1) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) (Nat.choose_succ_succ s m)
    rw [hpascal]
    ring

/-- Rewriting a sum over small subsets as a sum over cardinalities. -/
lemma sum_powerset_filter_card (R : Finset ℕ) (K : ℕ) :
    ∑ T ∈ R.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card
      = ∑ j ∈ range (K+1), (-1:ℤ)^j * (R.card.choose j) := by
  classical
  have hset : R.powerset.filter (fun T => T.card ≤ K)
      = (range (K+1)).biUnion (fun j => R.powersetCard j) := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard, Nat.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨T.card, h2, h1, rfl⟩
    · rintro ⟨a, ha, h1, rfl⟩
      exact ⟨h1, ha⟩
  rw [hset, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_congr rfl (fun T hT => by rw [(Finset.mem_powersetCard.1 hT).2] :
      ∀ T ∈ R.powersetCard j, (-1:ℤ)^T.card = (-1:ℤ)^j)]
    rw [Finset.sum_const, Finset.card_powersetCard]
    simp [mul_comm]
  · intro i _ j _ hij
    simp only [Finset.disjoint_left]
    intro T hT hT'
    exact hij ((Finset.mem_powersetCard.1 hT).2 ▸ (Finset.mem_powersetCard.1 hT').2 ▸ rfl)

/-- The Bonferroni inequality: truncating inclusion–exclusion after an even number of terms
gives an upper bound. -/
lemma bonferroni_pointwise (R : Finset ℕ) (K : ℕ) (hK : Even K) :
    (if R = ∅ then (1:ℤ) else 0)
      ≤ ∑ T ∈ R.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card := by
  classical
  by_cases h : R = ∅
  · subst h
    rw [if_pos rfl, Finset.powerset_empty, Finset.filter_singleton]
    simp
  · rw [if_neg h, sum_powerset_filter_card]
    obtain ⟨s, hs⟩ : ∃ s, R.card = s + 1 := by
      refine ⟨R.card - 1, ?_⟩
      have : 0 < R.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h)
      omega
    rw [hs, alt_sum_choose, hK.neg_one_pow]
    positivity

/-- Brun's pure sieve inequality, in integer form. -/
lemma sifted_le (Q : Finset ℕ) (N K : ℕ) (hK : Even K) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℤ)
      ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
  set R : ℕ → Finset ℕ := fun n => Q.filter (fun p => p ∣ n*(n+2)) with hR
  have hcount : ∀ T : Finset ℕ, T ⊆ Q →
      ((#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℤ))
        = ∑ n ∈ range N, (if T ⊆ R n then (1:ℤ) else 0) := by
    intro T hT
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    apply propext
    constructor
    · intro h p hp
      exact Finset.mem_filter.2 ⟨hT hp, h p hp⟩
    · intro h p hp
      exact (Finset.mem_filter.1 (h hp)).2
  have step1 : (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℤ)
      = ∑ n ∈ range N, (if R n = ∅ then (1:ℤ) else 0) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    apply propext
    rw [Finset.filter_eq_empty_iff]
  have step2 : ∑ n ∈ range N, (if R n = ∅ then (1:ℤ) else 0)
      ≤ ∑ n ∈ range N, ∑ T ∈ (R n).powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card :=
    Finset.sum_le_sum fun n _ => bonferroni_pointwise (R n) K hK
  have step3 : ∑ n ∈ range N, ∑ T ∈ (R n).powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card
      = ∑ n ∈ range N, ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
          (if T ⊆ R n then (-1:ℤ)^T.card else 0) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext T
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1.trans (Finset.filter_subset _ _), h2⟩, h1⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h2⟩
  have step4 : ∑ n ∈ range N, ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
          (if T ⊆ R n then (-1:ℤ)^T.card else 0)
      = ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [hcount T (Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split <;> simp
  rw [step1]
  exact (step2.trans_eq step3).trans_eq step4

/-- **Brun's pure sieve**, real form: the number of `n < N` with `n (n+2)` coprime to all
primes of `Q` is at most the truncated main term plus the truncated error term. -/
theorem sieve_main (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ p ≠ 2) (N K : ℕ) (hK : Even K) :
    (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ N * (∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K),
              (-1:ℝ)^T.card * ∏ p ∈ T, (2/(p:ℝ)))
        + ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card := by
  have hint := sifted_le Q N K hK
  have hcast : (#((range N).filter (fun n => ∀ p ∈ Q, ¬ p ∣ n*(n+2))) : ℝ)
      ≤ ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (-1:ℝ)^T.card *
          #((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) := by
    exact_mod_cast hint
  refine hcast.trans ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun T hT => ?_
  have hTQ : T ⊆ Q := Finset.mem_powerset.1 (Finset.mem_filter.1 hT).1
  have hTodd : ∀ p ∈ T, p.Prime ∧ p ≠ 2 := fun p hp => hQ p (hTQ hp)
  have happrox := card_divisible_approx T hTodd N
  have hprod : (N : ℝ) * 2 ^ T.card / (∏ p ∈ T, (p:ℕ) : ℕ) = N * ∏ p ∈ T, (2/(p:ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_const]
    push_cast
    ring
  rw [hprod] at happrox
  rw [abs_le] at happrox
  set A := (#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℝ) with hA
  set M := (N : ℝ) * ∏ p ∈ T, (2/(p:ℝ)) with hM
  have key : (-1:ℝ)^T.card * A ≤ (-1:ℝ)^T.card * M + 2^T.card := by
    rcases Nat.even_or_odd T.card with h | h
    · rw [h.neg_one_pow]; linarith [happrox.2]
    · rw [h.neg_one_pow]; linarith [happrox.1]
  refine key.trans ?_
  rw [hM]
  ring_nf
  exact le_rfl

end Brun

