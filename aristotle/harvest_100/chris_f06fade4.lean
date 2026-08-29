import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_fiedler_value
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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Finset SimpleGraph Matrix

/-- The Laplacian of the cycle graph `C n` (`n ≥ 3`) acts on a vector by
`(L v) i = 2 * v i - (v (i-1) + v (i+1))`. -/
lemma cycle_lap_mulVec {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n → ℝ) (i : Fin n) :
    ((SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ v) i = 2 * v i - (v (i - 1) + v (i + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset]
  have hne : i - 1 ≠ i + 1 := by
    intro h
    rw [sub_eq_iff_eq_add, add_assoc] at h
    have h0 : (1 + 1 : Fin (m + 3)) = 0 := by
      have : i + (1 + 1) = i + 0 := by rw [← h, add_zero]
      exact add_left_cancel this
    have h2 : ((1 + 1 : Fin (m + 3)) : ℕ) = 2 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt]
    rw [h0] at h2
    simp at h2
  rw [Finset.sum_pair hne]
  norm_num

/-- If `1 ≤ k < n` then `cos (2πk/n) ≤ cos (2π/n)`. -/
lemma cos_two_pi_mul_le {n k : ℕ} (hn : 3 ≤ n) (hk : k ≠ 0) (hkn : k < n) :
    Real.cos (2 * Real.pi * k / n) ≤ Real.cos (2 * Real.pi / n) := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hpi := Real.pi_pos
  set a : ℕ := min k (n - k) with ha
  have ha1 : 1 ≤ a := by simp [ha]; omega
  have ha2 : 2 * a ≤ n := by simp [ha]; omega
  have hcos_eq : Real.cos (2 * Real.pi * k / n) = Real.cos (2 * Real.pi * a / n) := by
    rcases le_or_gt k (n - k) with h | h
    · have hak : a = k := by simp [ha]; omega
      rw [hak]
    · have hak : a = n - k := by simp [ha]; omega
      rw [hak]
      have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by
        push_cast [Nat.cast_sub hkn.le]; ring
      rw [hcast]
      have h2 : 2 * Real.pi * ((n : ℝ) - k) / n = 2 * Real.pi - 2 * Real.pi * k / n := by
        field_simp
      rw [h2, Real.cos_two_pi_sub]
  rw [hcos_eq]
  refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
  · rw [div_le_iff₀ hn0]
    have : (2 : ℝ) * a ≤ n := by exact_mod_cast ha2
    nlinarith
  · rw [div_le_div_iff_of_pos_right hn0]
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha1
    nlinarith

/-- The real part of an `n`-th root of unity other than `1` is at most `cos (2π/n)`. -/
lemma root_of_unity_re_le {n : ℕ} (hn : 3 ≤ n) {z : ℂ} (hz : z ^ n = 1) (hz1 : z ≠ 1) :
    z.re ≤ Real.cos (2 * Real.pi / n) := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨k, hkn, hk⟩ := (Complex.isPrimitiveRoot_exp n (by omega)).eq_pow_of_pow_eq_one hz
  have hzform : z = Complex.exp (((2 * Real.pi * k / n : ℝ)) * Complex.I) := by
    rw [← hk, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hz1 (by simpa using hk.symm)
  rw [hzform, Complex.exp_ofReal_mul_I_re]
  exact cos_two_pi_mul_le hn hk0 hkn

/-- Lower bound: any eigenvalue of the cycle Laplacian whose eigenvector has zero sum is at
least `2 - 2 cos (2π/n)`. -/
theorem cycle_rec_eigenvalue_lower {n : ℕ} [NeZero n] (hn : 3 ≤ n) (μ : ℝ) (v : ZMod n → ℝ)
    (hv : v ≠ 0) (hsum : ∑ i, v i = 0)
    (hrec : ∀ i : ZMod n, 2 * v i - (v (i - 1) + v (i + 1)) = μ * v i) :
    2 - 2 * Real.cos (2 * Real.pi / n) ≤ μ := by
  classical
  set w : ZMod n → ℂ := fun i => ((v i : ℝ) : ℂ) with hw
  have hrecC : ∀ i : ZMod n, 2 * w i - (w (i - 1) + w (i + 1)) = (μ : ℂ) * w i := by
    intro i
    have h := hrec i
    simp only [hw]
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h
  have hwsum : ∑ i, w i = 0 := by
    simp only [hw]
    rw [← Complex.ofReal_sum, hsum, Complex.ofReal_zero]
  set B := AddChar.complexBasis (ZMod n) with hB
  set c := B.equivFun w with hc
  have hrepr : ∀ i : ZMod n, ∑ ψ : AddChar (ZMod n) ℂ, c ψ * ψ i = w i := by
    intro i
    have h := congrFun (B.sum_equivFun w) i
    simpa [hB, AddChar.coe_complexBasis] using h
  -- every character is an eigenvector of the recurrence
  have hpsi_rec : ∀ (ψ : AddChar (ZMod n) ℂ) (i : ZMod n),
      2 * ψ i - (ψ (i - 1) + ψ (i + 1)) = (2 - ψ 1 - (ψ 1)⁻¹) * ψ i := by
    intro ψ i
    have h1 : ψ (i + 1) = ψ i * ψ 1 := by rw [AddChar.map_add_eq_mul]
    have h2 : ψ (i - 1) = ψ i * (ψ 1)⁻¹ := by
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
    rw [h1, h2]; ring
  -- comparing coefficients in the character basis
  have hcoef : ∀ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) = (μ : ℂ) * c ψ := by
    have hzero : ∑ ψ : AddChar (ZMod n) ℂ,
        (c ψ * (2 - ψ 1 - (ψ 1)⁻¹) - (μ : ℂ) * c ψ) • (ψ : ZMod n → ℂ) = 0 := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul]
      rw [Finset.sum_sub_distrib]
      have hA : ∑ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) * ψ i
          = 2 * w i - (w (i - 1) + w (i + 1)) := by
        have step : ∀ ψ : AddChar (ZMod n) ℂ, c ψ * (2 - ψ 1 - (ψ 1)⁻¹) * ψ i
            = 2 * (c ψ * ψ i) - ((c ψ * ψ (i - 1)) + (c ψ * ψ (i + 1))) := by
          intro ψ
          have h := hpsi_rec ψ i
          rw [mul_assoc, ← h]; ring
        rw [Finset.sum_congr rfl (fun ψ _ => step ψ), Finset.sum_sub_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum, hrepr i, hrepr (i - 1), hrepr (i + 1)]
      have hBb : ∑ ψ : AddChar (ZMod n) ℂ, (μ : ℂ) * c ψ * ψ i = (μ : ℂ) * w i := by
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum, hrepr i]
      rw [hA, hBb, hrecC i, sub_self]
    intro ψ
    have h := Fintype.linearIndependent_iff.mp (AddChar.linearIndependent (ZMod n) ℂ) _ hzero ψ
    linear_combination h
  -- the trivial character does not occur, since `v` has zero sum
  have hc0 : c 0 = 0 := by
    have h1 : ∑ i : ZMod n, w i
        = ∑ ψ : AddChar (ZMod n) ℂ, c ψ * (∑ i : ZMod n, ψ i) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact (Finset.sum_congr rfl (fun i _ => hrepr i)).symm
    have h2 : ∀ ψ : AddChar (ZMod n) ℂ, (∑ i : ZMod n, ψ i)
        = if ψ = 0 then (Fintype.card (ZMod n) : ℂ) else 0 := fun ψ => AddChar.sum_eq_ite ψ
    rw [h1] at hwsum
    simp_rw [h2, mul_ite, mul_zero,
      Finset.sum_ite_eq' Finset.univ (0 : AddChar (ZMod n) ℂ)] at hwsum
    simp only [Finset.mem_univ, if_true, mul_eq_zero, Nat.cast_eq_zero] at hwsum
    rcases hwsum with h | h
    · exact h
    · exact absurd h (by simp [ZMod.card, NeZero.ne n])
  -- some character occurs with a nonzero coefficient
  have hwne : w ≠ 0 := by
    intro h
    exact hv (funext fun i => by
      have := congrFun h i
      simp only [hw, Pi.zero_apply, Complex.ofReal_eq_zero] at this
      simpa using this)
  obtain ⟨ψ, hcpsi⟩ : ∃ ψ : AddChar (ZMod n) ℂ, c ψ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hwne (funext fun i => by
      rw [← hrepr i]
      simp [hcon])
  have hpsine : ψ ≠ 0 := by
    intro h
    exact hcpsi (h ▸ hc0)
  set z : ℂ := ψ 1 with hzdef
  have hzpow : z ^ n = 1 := by
    rw [hzdef, ← AddChar.map_nsmul_eq_pow]
    simp [nsmul_eq_mul]
  have hz1 : z ≠ 1 := by
    intro h
    refine hpsine ?_
    ext i
    have hi : (i.val) • (1 : ZMod n) = i := by simp [nsmul_eq_mul]
    calc ψ i = ψ ((i.val) • (1 : ZMod n)) := by rw [hi]
      _ = (ψ 1) ^ i.val := AddChar.map_nsmul_eq_pow ψ _ _
      _ = 1 := by rw [← hzdef, h, one_pow]
  have hznorm : ‖z‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hzpow (by omega)
  have hmu : (μ : ℂ) = 2 - ((2 * z.re : ℝ) : ℂ) := by
    have h2 : (2 - z - z⁻¹) = (μ : ℂ) :=
      mul_left_cancel₀ hcpsi (by linear_combination hcoef ψ)
    rw [← h2, Complex.inv_eq_conj hznorm, ← Complex.add_conj z]
    ring
  have hmure : μ = 2 - 2 * z.re := by
    have := congrArg Complex.re hmu
    simpa using this
  have hle : z.re ≤ Real.cos (2 * Real.pi / n) := root_of_unity_re_le hn hzpow hz1
  rw [hmure]
  linarith

/-- `2 - 2 cos (2π/n)` really is an eigenvalue, with a zero-sum eigenvector. -/
theorem cycle_rec_eigenvector {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    ∃ v : ZMod n → ℝ, v ≠ 0 ∧ (∑ i, v i = 0) ∧
      ∀ i : ZMod n, 2 * v i - (v (i - 1) + v (i + 1))
        = (2 - 2 * Real.cos (2 * Real.pi / n)) * v i := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  set psi : AddChar (ZMod n) ℂ := AddChar.circleEquivComplex (AddChar.zmod n 1) with hpsi
  have hpsi1 : psi 1 = Complex.exp (((2 * Real.pi / n : ℝ)) * Complex.I) := by
    have h := AddChar.zmod_intCast n 1 1
    simp only [Int.cast_one, one_mul] at h
    rw [hpsi, show ((AddChar.circleEquivComplex (AddChar.zmod n 1) : ZMod n → ℂ) 1)
      = ((AddChar.zmod n 1 1 : Circle) : ℂ) from rfl, h, Circle.coe_exp]
    ring_nf
  have hre : (psi 1).re = Real.cos (2 * Real.pi / n) := by
    rw [hpsi1, Complex.exp_ofReal_mul_I_re]
  have hnorm : ‖psi 1‖ = 1 := by
    rw [hpsi1]
    simp [Complex.norm_exp]
  have hz : ¬ (AddChar.zmod n (1 : ZMod n) = 0) := by
    intro h
    have h0 : AddChar.zmod n (1 : ZMod n) = AddChar.zmod n 0 := by
      rw [h, AddChar.zmod_zero]; rfl
    exact one_ne_zero (AddChar.zmod_injective h0)
  have hne0 : psi ≠ 0 := by
    rw [show psi = AddChar.zmodAddEquiv (1 : ZMod n) from rfl]
    simpa using hz
  refine ⟨fun i => (psi i).re, ?_, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · have hsum : ∑ i, (psi i).re = (∑ i, psi i).re := by
      simp [Complex.re_sum]
    rw [hsum, AddChar.sum_eq_zero_iff_ne_zero.2 hne0]
    simp
  · intro i
    have e1 : psi (i + 1) = psi i * psi 1 := by rw [AddChar.map_add_eq_mul]
    have e2 : psi (i - 1) = psi i * (starRingEnd ℂ) (psi 1) := by
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv,
        Complex.inv_eq_conj hnorm]
    have key : (psi (i - 1)).re + (psi (i + 1)).re = 2 * (psi 1).re * (psi i).re := by
      rw [e1, e2]
      simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    simp only
    rw [key, ← hre]
    ring

/-- **Fiedler value of the cycle graph.** For `n ≥ 3`, the algebraic connectivity of `C n`,
i.e. the smallest eigenvalue of its Laplacian admitting an eigenvector orthogonal to the
constant vector (equivalently, the second-smallest Laplacian eigenvalue), equals
`2 - 2 * cos (2 * π / n)`. -/
theorem cycle_fiedler_value {n : ℕ} (hn : 3 ≤ n) :
    IsLeast {μ : ℝ | ∃ v : Fin n → ℝ, v ≠ 0 ∧ (∑ i, v i = 0) ∧
        (SimpleGraph.cycleGraph n).lapMatrix ℝ *ᵥ v = μ • v}
      (2 - 2 * Real.cos (2 * Real.pi / n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  constructor
  · obtain ⟨v, hv0, hvs, hvr⟩ := cycle_rec_eigenvector (n := m + 1) hn
    refine ⟨v, hv0, hvs, ?_⟩
    funext i
    rw [cycle_lap_mulVec hn]
    simpa using hvr i
  · rintro μ ⟨v, hv0, hvs, hvr⟩
    refine cycle_rec_eigenvalue_lower (n := m + 1) hn μ v hv0 hvs (fun i => ?_)
    have := congrFun hvr i
    rw [cycle_lap_mulVec hn] at this
    simpa using this

end Frontier.Spectral

