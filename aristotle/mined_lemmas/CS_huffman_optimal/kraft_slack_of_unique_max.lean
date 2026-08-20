import RequestProject.Forest

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

/-- The value computed by Huffman's algorithm on a multiset of weights. -/

lemma kraft_slack_of_unique_max (M : ℕ) (a : ℝ) (r : Multiset (ℝ × ℕ))
    (hM : 1 ≤ M) (hlt : ∀ q ∈ r, q.2 < M) (hk : mkraft ((a, M) ::ₘ r) ≤ 1) :
    mkraft ((a, M) ::ₘ r) + (2 : ℝ)⁻¹ ^ M ≤ 1 := by
  have hle : ∀ q ∈ (a, M) ::ₘ r, q.2 ≤ M := by
    intro q hq
    rcases Multiset.mem_cons.mp hq with rfl | hq
    · exact le_rfl
    · exact (hlt q hq).le
  have hscale : mkraft ((a, M) ::ₘ r) * 2 ^ M
      = (((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) : ℝ) := by
    have h1 : mkraft ((a, M) ::ₘ r)
        = (((a, M) ::ₘ r).map (fun q => (2 : ℝ)⁻¹ ^ q.2)).sum := by
      simp [mkraft, Multiset.map_map, Function.comp]
    have h2 : (((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) : ℝ)
        = (((a, M) ::ₘ r).map (fun q => ((2:ℝ)) ^ (M - q.2))).sum := by
      push_cast
      rw [Multiset.map_map]
      refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
      intro q _
      simp
    rw [h1, ← Multiset.sum_map_mul_right, h2]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro q hq
    have hq2 : q.2 ≤ M := hle q hq
    have hpow : (2 : ℝ) ^ M = 2 ^ (M - q.2) * 2 ^ q.2 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow, inv_pow, ← mul_assoc, inv_mul_eq_div]
    field_simp
  set N : ℕ := ((((a, M) ::ₘ r).map (fun q => 2 ^ (M - q.2))).sum : ℕ) with hN
  have hodd : N % 2 = 1 := by
    have hsum : N = 1 + (r.map (fun q => 2 ^ (M - q.2))).sum := by
      rw [hN]
      simp
    have heven : 2 ∣ (r.map (fun q => 2 ^ (M - q.2))).sum := by
      refine Multiset.dvd_sum ?_
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
      have hq1 : 1 ≤ M - q.2 := by have := hlt q hq; omega
      exact dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := heven
    omega
  have hpow : (0:ℝ) < 2 ^ M := by positivity
  have hNle : (N : ℝ) ≤ 2 ^ M := by
    rw [← hscale]
    nlinarith [hk, hpow]
  have hNleN : N ≤ 2 ^ M := by exact_mod_cast hNle
  have hpowEven : 2 ∣ 2 ^ M := dvd_pow_self 2 (by omega)
  have hNne : N ≠ 2 ^ M := by
    intro hEq
    obtain ⟨c, hc⟩ := hpowEven
    omega
  have hNlt : N + 1 ≤ 2 ^ M := by omega
  have hNlt' : (N : ℝ) + 1 ≤ 2 ^ M := by exact_mod_cast hNlt
  have hmain : mkraft ((a, M) ::ₘ r) * 2 ^ M + 1 ≤ 2 ^ M := by rw [hscale]; exact hNlt'
  rw [inv_pow, ← sub_nonneg]
  have hrw : 1 - (mkraft ((a, M) ::ₘ r) + ((2:ℝ) ^ M)⁻¹)
      = (2 ^ M - mkraft ((a, M) ::ₘ r) * 2 ^ M - 1) / 2 ^ M := by
    field_simp
    ring
  rw [hrw]
  exact div_nonneg (by linarith) hpow.le


