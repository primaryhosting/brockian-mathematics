/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
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

namespace Chem

open Finset SimpleGraph

/-- A primitive 15-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

/-- The associated character on the integers: `W m = ζ ^ m`. -/
noncomputable def W (m : ℤ) : ℂ := zeta ^ m

/-- The character of `Fin 15` with frequency `m`. -/
noncomputable def chi (m : ℤ) (i : Fin 15) : ℂ := W (m * (i : ℕ))

lemma zeta_primitive : IsPrimitiveRoot zeta 15 := by
  have h := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [zeta] using h

lemma zeta_ne_zero : zeta ≠ 0 := by
  simp [zeta, Complex.exp_ne_zero]

lemma W_add (m n : ℤ) : W (m + n) = W m * W n := by
  simp [W, zpow_add₀ zeta_ne_zero]

lemma W_zero : W 0 = 1 := by simp [W]

lemma W_neg (m : ℤ) : W (-m) = (W m)⁻¹ := by simp [W, zpow_neg]

lemma W_ne_zero (m : ℤ) : W m ≠ 0 := zpow_ne_zero _ zeta_ne_zero

lemma W_eq_one_iff (m : ℤ) : W m = 1 ↔ (15 : ℤ) ∣ m := by
  rw [W, zeta_primitive.zpow_eq_one_iff_dvd]
  norm_num

lemma W_congr {a b : ℤ} (h : (15 : ℤ) ∣ a - b) : W a = W b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + 15 * t := by omega
  rw [hab, W_add, (W_eq_one_iff (15 * t)).mpr ⟨t, rfl⟩, mul_one]

lemma W_mul_neg (m : ℤ) : W m * W (-m) = 1 := by
  rw [← W_add, add_neg_cancel, W_zero]

/-- The successor relation in `Fin 15`, at the level of integer exponents. -/
lemma fin_succ_dvd (i : Fin 15) : (15 : ℤ) ∣ (((i + 1 : Fin 15) : ℕ) : ℤ) - (i : ℕ) - 1 := by
  have h : ((i + 1 : Fin 15) : ℕ) = ((i : ℕ) + 1) % 15 := by
    rw [Fin.val_add]
    norm_num
  have h2 : (i : ℕ) < 15 := i.isLt
  omega

/-- Key step relation for the characters. -/
lemma chi_step (m : ℤ) (i : Fin 15) : chi m (i + 1) = chi m i * W m := by
  rw [chi, chi, ← W_add]
  refine W_congr ?_
  obtain ⟨t, ht⟩ := fin_succ_dvd i
  refine ⟨m * t, ?_⟩
  have : (((i + 1 : Fin 15) : ℕ) : ℤ) = (i : ℕ) + 1 + 15 * t := by omega
  rw [this]; ring

lemma chi_zero (m : ℤ) : chi m 0 = 1 := by
  simp [chi, W_zero]

/-- Orthogonality / geometric sum of characters. -/
lemma char_sum (d : ℤ) :
    ∑ k : Fin 15, chi d k = if (15 : ℤ) ∣ d then 15 else 0 := by
  have hk : ∀ k : Fin 15, chi d k = (W d) ^ (k : ℕ) := by
    intro k
    simp [chi, W, zpow_mul, zpow_natCast]
  rw [Finset.sum_congr rfl (fun k _ => hk k), Fin.sum_univ_eq_sum_range (fun t => (W d) ^ t) 15]
  by_cases h : (15 : ℤ) ∣ d
  · have h1 : W d = 1 := (W_eq_one_iff d).mpr h
    simp [h1, h]
  · have hne : W d ≠ 1 := fun hc => h ((W_eq_one_iff d).mp hc)
    have h15 : (W d) ^ (15 : ℕ) = 1 := by
      have hEq : (W d) ^ (15 : ℕ) = W (d * 15) := by
        rw [W, W, ← zpow_natCast (zeta ^ d) 15, ← zpow_mul]
        norm_num
      rw [hEq, W_eq_one_iff]
      exact ⟨d, by ring⟩
    rw [geom_sum_eq hne, h15]
    simp [h]

lemma sum_shift (f : Fin 15 → ℂ) : ∑ i : Fin 15, f (i + 1) = ∑ i : Fin 15, f i :=
  Fintype.sum_equiv (Equiv.addRight (1 : Fin 15)) _ _ (fun _ => rfl)

/-- Fourier inversion on `Fin 15`. -/
lemma dft_inversion (v : Fin 15 → ℂ) (j : Fin 15) :
    ∑ k : Fin 15, chi ((k : ℕ) : ℤ) j * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = 15 * v j := by
  have step : ∀ k i : Fin 15,
      chi ((k : ℕ) : ℤ) j * (chi (-((k : ℕ) : ℤ)) i * v i)
        = chi (((j : ℕ) : ℤ) - (i : ℕ)) k * v i := by
    intro k i
    rw [chi, chi, chi, ← mul_assoc, ← W_add]
    congr 2
    ring
  calc ∑ k : Fin 15, chi ((k : ℕ) : ℤ) j * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = ∑ k : Fin 15, ∑ i : Fin 15, chi (((j : ℕ) : ℤ) - (i : ℕ)) k * v i := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => step k i)
    _ = ∑ i : Fin 15, (∑ k : Fin 15, chi (((j : ℕ) : ℤ) - (i : ℕ)) k) * v i := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => by rw [Finset.sum_mul])
    _ = 15 * v j := by
        rw [Finset.sum_eq_single j]
        · rw [char_sum]
          simp
        · intro i _ hij
          rw [char_sum]
          have h1 : (i : ℕ) < 15 := i.isLt
          have h2 : (j : ℕ) < 15 := j.isLt
          have h3 : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          have : ¬ (15 : ℤ) ∣ (((j : ℕ) : ℤ) - (i : ℕ)) := by omega
          simp [this]
        · intro h
          exact absurd (Finset.mem_univ j) h

/-- The Fourier coefficients diagonalise the eigenvalue equation. -/
lemma dft_eigen (v : Fin 15 → ℂ) (μ : ℂ) (h : ∀ i : Fin 15, v (i - 1) + v (i + 1) = μ * v i)
    (k : Fin 15) :
    μ * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i)
      = (W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ))) * (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i) := by
  set m : ℤ := -((k : ℕ) : ℤ) with hm
  set c : ℂ := ∑ i : Fin 15, chi m i * v i with hcdef
  have hS2 : ∑ i : Fin 15, chi m i * v (i - 1) = W m * c := by
    have := (sum_shift (fun i => chi m i * v (i - 1))).symm
    rw [this]
    rw [hcdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [chi_step]
    simp only [add_sub_cancel_right]
    ring
  have hS1 : ∑ i : Fin 15, chi m i * v (i + 1) = W (-m) * c := by
    have hg := sum_shift (fun i => (W (-m) * chi m i) * v i)
    have hlhs : ∀ i : Fin 15, (W (-m) * chi m (i + 1)) * v (i + 1) = chi m i * v (i + 1) := by
      intro i
      rw [chi_step]
      have : W (-m) * (chi m i * W m) = chi m i * (W m * W (-m)) := by ring
      rw [this, W_mul_neg, mul_one]
    calc ∑ i : Fin 15, chi m i * v (i + 1)
        = ∑ i : Fin 15, (W (-m) * chi m (i + 1)) * v (i + 1) :=
          Finset.sum_congr rfl (fun i _ => (hlhs i).symm)
      _ = ∑ i : Fin 15, (W (-m) * chi m i) * v i := hg
      _ = W (-m) * c := by
            rw [hcdef, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun i _ => by ring)
  have : μ * c = ∑ i : Fin 15, chi m i * (v (i - 1) + v (i + 1)) := by
    rw [hcdef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h i]; ring
  rw [this]
  have hsplit : ∑ i : Fin 15, chi m i * (v (i - 1) + v (i + 1))
      = (∑ i : Fin 15, chi m i * v (i - 1)) + ∑ i : Fin 15, chi m i * v (i + 1) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hsplit, hS1, hS2, hm]
  simp only [neg_neg]
  ring

lemma W_val_add_neg (k : Fin 15) :
    W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ)) = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  set t : ℝ := 2 * Real.pi * (k : ℕ) / 15 with ht
  have hW : W ((k : ℕ) : ℤ) = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [W, zpow_natCast, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have hWneg : W (-((k : ℕ) : ℤ)) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [W_neg, hW, ← Complex.exp_neg]
  rw [hW, hWneg, Complex.exp_mul_I]
  have hneg : Complex.exp (-((t : ℂ) * Complex.I)) = Complex.cos t - Complex.sin t * Complex.I := by
    rw [show -((t : ℂ) * Complex.I) = (-(t : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]
    ring
  rw [hneg, Complex.ofReal_cos]
  ring

/-- The action of the adjacency matrix of `C₁₅`. -/
lemma adj_mulVec (v : Fin 15 → ℂ) (j : Fin 15) :
    ((cycleGraph 15).adjMatrix ℂ).mulVec v j = v (j - 1) + v (j + 1) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  have h : (cycleGraph 15).neighborFinset j = {j - 1, j + 1} := cycleGraph_neighborFinset
  have hne : j - 1 ≠ j + 1 := by revert j; decide
  rw [h, Finset.sum_pair hne]

/-- **Hückel theory for the cyclic polyene C₁₅.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₅`
if and only if `μ = 2 cos (2πk/15)` for some `k ∈ {0, …, 14}`. -/
theorem huckel_C15 (μ : ℂ) :
    (∃ v : Fin 15 → ℂ, v ≠ 0 ∧
        ((cycleGraph 15).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 15, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    have heig : ∀ i : Fin 15, v (i - 1) + v (i + 1) = μ * v i := by
      intro i
      have h := congrFun hA i
      rw [adj_mulVec] at h
      simpa using h
    have hex : ∃ k : Fin 15, (∑ i : Fin 15, chi (-((k : ℕ) : ℤ)) i * v i) ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv
      funext j
      have hinv := dft_inversion v j
      rw [Finset.sum_congr rfl (fun k _ => by rw [hcon k, mul_zero])] at hinv
      simp only [Finset.sum_const, smul_zero] at hinv
      have : (15 : ℂ) * v j = 0 := hinv.symm
      simpa using this
    obtain ⟨k, hk⟩ := hex
    refine ⟨k, ?_⟩
    have key := dft_eigen v μ heig k
    have hμ : μ = W ((k : ℕ) : ℤ) + W (-((k : ℕ) : ℤ)) := mul_right_cancel₀ hk key
    rw [hμ, W_val_add_neg]
  · rintro ⟨k, rfl⟩
    refine ⟨fun j => chi ((k : ℕ) : ℤ) j, ?_, ?_⟩
    · intro hzero
      have h0 : chi ((k : ℕ) : ℤ) 0 = 0 := congrFun hzero 0
      rw [chi_zero] at h0
      exact one_ne_zero h0
    · funext j
      rw [adj_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← W_val_add_neg k]
      have hj : j = (j - 1) + 1 := by simp
      set i : Fin 15 := j - 1 with hi
      rw [hj]
      simp only [chi_step]
      have h1 : W ((k : ℕ) : ℤ) * W (-((k : ℕ) : ℤ)) = 1 := W_mul_neg _
      linear_combination (-(chi ((k : ℕ) : ℤ) i)) * h1

end Chem

