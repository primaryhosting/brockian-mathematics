/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the 5-cycle `C₅`

The Hückel secular problem for the cyclic polyene `C₅H₅` reduces (after removing the
Coulomb integral `α` and dividing by the resonance integral `β`) to the eigenvalue
problem for the adjacency matrix of the cycle graph `C₅`.

The main result `Chem.huckel_C5` states that the eigenvalues of that adjacency matrix
are exactly the five numbers `2 * cos (2 * π * k / 5)`, `k = 0, 1, 2, 3, 4`
(equivalently `2`, `(√5 - 1)/2` twice and `-(√5 + 1)/2` twice).
-/

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where `α = 0`, `β = 1`). -/
def C5adj : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

/-- `C5adj` really is the adjacency matrix of the cycle graph on five vertices. -/
theorem C5adj_eq_adjMatrix : C5adj = (SimpleGraph.cycleGraph 5).adjMatrix ℂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C5adj, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph_adj] <;> decide

section Auxiliary

/-- For a fifth root of unity `z`, the vector `(1, z, z², z³, z⁴)` is an eigenvector of
the `C₅` adjacency matrix with eigenvalue `z + z⁴ = z + z⁻¹`. -/
private lemma C5adj_mulVec_pow (z : ℂ) (h5 : z ^ 5 = 1) :
    C5adj.mulVec ![1, z, z ^ 2, z ^ 3, z ^ 4] = (z + z ^ 4) • ![1, z, z ^ 2, z ^ 3, z ^ 4] := by
  have h6 : z ^ 6 = z := by linear_combination z * h5
  have h7 : z ^ 7 = z ^ 2 := by linear_combination z ^ 2 * h5
  have h8 : z ^ 8 = z ^ 3 := by linear_combination z ^ 3 * h5
  funext i
  fin_cases i <;>
    simp [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] <;>
    ring_nf <;> simp only [h5, h6, h7, h8] <;> ring

/-- `exp (2πik/5)` is a fifth root of unity. -/
private lemma exp_pow_five (k : ℕ) :
    (Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)) ^ 5 = 1 := by
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [show (5 : ℂ) * ((2 * (Real.pi : ℂ) * k / 5) * Complex.I)
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k

/-- `exp (2πik/5) + exp (2πik/5)⁴ = 2 cos (2πk/5)`. -/
private lemma exp_add_pow_four (k : ℕ) :
    Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)
        + (Complex.exp (((2 * Real.pi * k / 5 : ℝ) : ℂ) * Complex.I)) ^ 4
      = ((2 * Real.cos (2 * Real.pi * k / 5) : ℝ) : ℂ) := by
  set t : ℝ := 2 * Real.pi * k / 5 with ht
  have h5 := exp_pow_five k
  rw [← ht] at h5
  have h4 : Complex.exp ((t : ℂ) * Complex.I) ^ 4 = Complex.exp (-(t : ℂ) * Complex.I) := by
    have e : ((4 : ℕ) : ℂ) * ((t : ℂ) * Complex.I)
        = (5 : ℕ) * ((t : ℂ) * Complex.I) + (-(t : ℂ) * Complex.I) := by push_cast; ring
    rw [← Complex.exp_nat_mul, e, Complex.exp_add, Complex.exp_nat_mul, h5, one_mul]
  rw [h4]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]

private lemma cos_two_pi_one_div_five : Real.cos (2 * Real.pi * ((1 : ℕ) : ℝ) / 5)
    = (Real.sqrt 5 - 1) / 4 := by
  have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 5 = 2 * (Real.pi / 5) := by push_cast; ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

private lemma cos_two_pi_two_div_five : Real.cos (2 * Real.pi * ((2 : ℕ) : ℝ) / 5)
    = -(1 + Real.sqrt 5) / 4 := by
  have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 5 = Real.pi - Real.pi / 5 := by push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

end Auxiliary

/-- **Hückel eigenvalues of `C₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₅` if and only if `μ = 2 cos (2πk/5)` for some
`k ∈ {0, 1, 2, 3, 4}`. -/
theorem huckel_C5 (μ : ℂ) :
    (∃ v : Fin 5 → ℂ, v ≠ 0 ∧ C5adj.mulVec v = μ • v) ↔
      ∃ k : Fin 5, μ = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 5) : ℝ) : ℂ) := by
  constructor
  · rintro ⟨v, hv, h⟩
    -- the five scalar equations of the eigenvalue problem
    have e0 : v 1 + v 4 = μ * v 0 := by
      have := congrFun h 0
      simpa [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
    have e1 : v 0 + v 2 = μ * v 1 := by
      have := congrFun h 1
      simpa [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
    have e2 : v 1 + v 3 = μ * v 2 := by
      have := congrFun h 2
      simpa [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
    have e3 : v 2 + v 4 = μ * v 3 := by
      have := congrFun h 3
      simpa [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
    have e4 : v 0 + v 3 = μ * v 4 := by
      have := congrFun h 4
      simpa [C5adj, Matrix.mulVec, dotProduct, Fin.sum_univ_five] using this
    -- the minimal polynomial `(μ - 2)(μ² + μ - 1)` annihilates every coordinate
    have key : ∀ i : Fin 5, (μ - 2) * (μ ^ 2 + μ - 1) * v i = 0 := by
      intro i
      fin_cases i
      · show (μ - 2) * (μ ^ 2 + μ - 1) * v 0 = 0
        linear_combination (-(μ ^ 2) + μ + 1) * e0 + (1 - μ) * e1 - e2 - e3 + (1 - μ) * e4
      · show (μ - 2) * (μ ^ 2 + μ - 1) * v 1 = 0
        linear_combination (1 - μ) * e0 + (-(μ ^ 2) + μ + 1) * e1 + (1 - μ) * e2 - e3 - e4
      · show (μ - 2) * (μ ^ 2 + μ - 1) * v 2 = 0
        linear_combination -e0 + (1 - μ) * e1 + (-(μ ^ 2) + μ + 1) * e2 + (1 - μ) * e3 - e4
      · show (μ - 2) * (μ ^ 2 + μ - 1) * v 3 = 0
        linear_combination -e0 - e1 + (1 - μ) * e2 + (-(μ ^ 2) + μ + 1) * e3 + (1 - μ) * e4
      · show (μ - 2) * (μ ^ 2 + μ - 1) * v 4 = 0
        linear_combination (1 - μ) * e0 - e1 - e2 + (1 - μ) * e3 + (-(μ ^ 2) + μ + 1) * e4
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hv (funext fun i => hc i)
    have hq : (μ - 2) * (μ ^ 2 + μ - 1) = 0 := by
      rcases mul_eq_zero.1 (key i) with h' | h'
      · exact h'
      · exact absurd h' hi
    -- identify the three roots
    have hs : ((Real.sqrt 5 : ℝ) : ℂ) ^ 2 = 5 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    have hfac : μ ^ 2 + μ - 1
        = (μ - ((Real.sqrt 5 : ℝ) - 1) / 2) * (μ + (((Real.sqrt 5 : ℝ) : ℂ) + 1) / 2) := by
      linear_combination (1/4 : ℂ) * hs
    rcases mul_eq_zero.1 hq with h' | h'
    · refine ⟨0, ?_⟩
      have : μ = 2 := by linear_combination h'
      simp [this]
    · rw [hfac] at h'
      rcases mul_eq_zero.1 h' with h'' | h''
      · refine ⟨1, ?_⟩
        rw [show ((1 : Fin 5) : ℕ) = (1 : ℕ) from rfl, cos_two_pi_one_div_five]
        push_cast
        linear_combination h''
      · refine ⟨2, ?_⟩
        rw [show ((2 : Fin 5) : ℕ) = (2 : ℕ) from rfl, cos_two_pi_two_div_five]
        push_cast
        linear_combination h''
  · rintro ⟨k, rfl⟩
    set z : ℂ := Complex.exp (((2 * Real.pi * (k : ℕ) / 5 : ℝ) : ℂ) * Complex.I) with hz
    refine ⟨![1, z, z ^ 2, z ^ 3, z ^ 4], ?_, ?_⟩
    · intro hcon
      have : (![1, z, z ^ 2, z ^ 3, z ^ 4] : Fin 5 → ℂ) 0 = 0 := by rw [hcon]; rfl
      simp at this
    · rw [← exp_add_pow_four (k : ℕ), ← hz]
      exact C5adj_mulVec_pow z (exp_pow_five (k : ℕ))

end Chem

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

