import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

namespace Chem

open Matrix Complex

/-- Adjacency matrix of the cycle graph `C₅` (the Hückel matrix of the cyclopentadienyl
π-system in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/
noncomputable def C5adj : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- For every `k`, the number `2 cos(2πk/5)` is an eigenvalue of `C5adj`, with
eigenvector `(ω^j)_{j<5}` where `ω = exp(2πik/5)`. -/
theorem C5adj_hasEigenvector (k : ℕ) :
    ∃ v : Fin 5 → ℂ, v ≠ 0 ∧
      C5adj *ᵥ v = (2 * (Real.cos (2 * Real.pi * k / 5) : ℂ)) • v := by
  set θ : ℝ := 2 * Real.pi * k / 5 with hθ
  set z : ℂ := Complex.exp (θ * I) with hzdef
  have hzne : z ≠ 0 := Complex.exp_ne_zero _
  have hz5 : z ^ 5 = 1 := by
    rw [hzdef, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * ((θ : ℂ) * I) = ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by
        push_cast [hθ]; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  have hz4 : z ^ 4 = Complex.exp (-((θ : ℂ) * I)) := by
    have h1 : z ^ 4 * z = 1 := by rw [← pow_succ]; exact hz5
    have h2 : Complex.exp (-((θ : ℂ) * I)) * z = 1 := by
      rw [hzdef, ← Complex.exp_add]; simp
    exact mul_right_cancel₀ hzne (h1.trans h2.symm)
  have hc : (2 * (Real.cos θ : ℂ)) = z + z ^ 4 := by
    rw [hz4, hzdef, Complex.ofReal_cos, Complex.two_cos, neg_mul]
  rw [hc]
  refine ⟨![1, z, z ^ 2, z ^ 3, z ^ 4], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · ext i
    fin_cases i
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -z * hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination -z ^ 2 * hz5
    · simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
      linear_combination (-1 - z ^ 3) * hz5

/-- The characteristic polynomial of `C₅`:
`det (A - μ) = -(μ⁵ - 5μ³ + 5μ - 2)`. -/
theorem C5adj_det_sub (μ : ℂ) :
    (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)).det = -(μ ^ 5 - 5 * μ ^ 3 + 5 * μ - 2) := by
  have h : (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)) =
      !![-μ, 1, 0, 0, 1;
         1, -μ, 1, 0, 0;
         0, 1, -μ, 1, 0;
         0, 0, 1, -μ, 1;
         1, 0, 0, 1, -μ] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [C5adj]
  rw [h]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem cos_two_pi_div_five : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
  have h : (2 * Real.pi / 5) = 2 * (Real.pi / 5) := by ring
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

theorem cos_four_pi_div_five : Real.cos (4 * Real.pi / 5) = -(1 + Real.sqrt 5) / 4 := by
  have h : (4 * Real.pi / 5) = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

/-- **Hückel theory for the cyclopentadienyl π-system.**  A complex number `μ` is an
eigenvalue of the adjacency (Hückel) matrix of the cycle graph `C₅` if and only if
`μ = 2 cos (2πk/5)` for some `k ∈ {0,1,2,3,4}`. -/
theorem huckel_C5 (μ : ℂ) :
    (∃ v : Fin 5 → ℂ, v ≠ 0 ∧ C5adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 5 ∧ μ = 2 * (Real.cos (2 * Real.pi * k / 5) : ℂ) := by
  constructor
  · rintro h
    -- the eigenvalue equation forces `det (A - μ) = 0`
    have hdet : (C5adj - μ • (1 : Matrix (Fin 5) (Fin 5) ℂ)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      obtain ⟨v, hv, hvec⟩ := h
      exact ⟨v, hv, by simp [Matrix.sub_mulVec, hvec, Matrix.smul_mulVec]⟩
    rw [C5adj_det_sub, neg_eq_zero] at hdet
    have hfac : (μ - 2) * (μ ^ 2 + μ - 1) ^ 2 = 0 := by linear_combination hdet
    set s : ℂ := (Real.sqrt 5 : ℂ) with hs
    have h5 : s ^ 2 = 5 := by
      rw [hs]; norm_cast; exact Real.sq_sqrt (by norm_num)
    have hsplit : (μ - 2) * ((μ - (-1 + s) / 2) * (μ - (-1 - s) / 2)) ^ 2 = 0 := by
      have key : (μ - (-1 + s) / 2) * (μ - (-1 - s) / 2) = μ ^ 2 + μ - 1 := by
        linear_combination (-(1 : ℂ) / 4) * h5
      rw [key]; exact hfac
    rcases mul_eq_zero.mp hsplit with h1 | h2
    · refine ⟨0, by norm_num, ?_⟩
      rw [sub_eq_zero.mp h1]
      norm_num
    · have h2' : (μ - (-1 + s) / 2) * (μ - (-1 - s) / 2) = 0 := by
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases mul_eq_zero.mp h2' with h3 | h4
      · refine ⟨1, by norm_num, ?_⟩
        have hμ : μ = (-1 + s) / 2 := sub_eq_zero.mp h3
        have harg : 2 * Real.pi * ((1 : ℕ) : ℝ) / 5 = 2 * Real.pi / 5 := by push_cast; ring
        rw [hμ, hs, harg, cos_two_pi_div_five]
        push_cast
        ring
      · refine ⟨2, by norm_num, ?_⟩
        have hμ : μ = (-1 - s) / 2 := sub_eq_zero.mp h4
        have harg : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = 4 * Real.pi / 5 := by push_cast; ring
        rw [hμ, hs, harg, cos_four_pi_div_five]
        push_cast
        ring
  · rintro ⟨k, -, rfl⟩
    exact C5adj_hasEigenvector k

end Chem

