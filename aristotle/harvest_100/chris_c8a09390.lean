/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Complex

namespace Chem

/-- A primitive 18-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 18)

/-- The additive character `x ↦ ω ^ x` on `Fin 18`. -/
noncomputable def ch (x : Fin 18) : ℂ := om ^ x.val

/-- The Fourier (DFT) matrix. -/
noncomputable def V : Matrix (Fin 18) (Fin 18) ℂ := fun j k => ch (j * k)

/-- Inverse of the Fourier matrix. -/
noncomputable def W : Matrix (Fin 18) (Fin 18) ℂ := fun k l => (18 : ℂ)⁻¹ * ch (-(k * l))

/-- The Hückel eigenvalues of `C₁₈`. -/
noncomputable def mu (k : Fin 18) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)

theorem om_primitive : IsPrimitiveRoot om 18 := by
  have h := Complex.isPrimitiveRoot_exp 18 (by norm_num)
  simpa [om] using h

theorem om_pow_eighteen : om ^ (18 : ℕ) = 1 := om_primitive.pow_eq_one

theorem om_pow_mod (a : ℕ) : om ^ (a % 18) = om ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 18]
  rw [pow_add, pow_mul, om_pow_eighteen, one_pow, one_mul]

theorem ch_add (x y : Fin 18) : ch (x + y) = ch x * ch y := by
  simp only [ch, Fin.add_def, om_pow_mod, pow_add]

theorem ch_zero : ch 0 = 1 := by simp [ch]

theorem ch_ne_zero (x : Fin 18) : ch x ≠ 0 := by
  simp [ch, om, Complex.exp_ne_zero]

theorem ch_neg (x : Fin 18) : ch (-x) = (ch x)⁻¹ := by
  have h : ch x * ch (-x) = 1 := by rw [← ch_add]; simp [ch_zero]
  exact (DivisionMonoid.inv_eq_of_mul _ _ h).symm

theorem ch_mul_pow (k m : Fin 18) : ch (k * m) = (ch m) ^ k.val := by
  simp only [ch, Fin.mul_def, om_pow_mod, ← pow_mul]
  ring_nf

theorem ch_sum (m : Fin 18) : (∑ k : Fin 18, ch (k * m)) = if m = 0 then 18 else 0 := by
  simp only [ch_mul_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => (ch m) ^ i) 18]
  by_cases hm : m = 0
  · simp [hm, ch_zero]
  · have hz : ch m ≠ 1 := by
      simp only [ch]
      exact om_primitive.pow_ne_one_of_pos_of_lt (by omega) m.isLt
    have h18 : (ch m) ^ 18 = 1 := by
      simp only [ch]
      rw [← pow_mul, mul_comm, pow_mul, om_pow_eighteen, one_pow]
    rw [geom_sum_eq hz, h18, if_neg hm]
    simp

theorem ch_eq_exp (k : Fin 18) :
    ch k = Complex.exp (((2 * Real.pi * k.val / 18 : ℝ) : ℂ) * Complex.I) := by
  rw [ch, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem ch_add_ch_neg (k : Fin 18) : ch k + ch (-k) = mu k := by
  rw [ch_neg, ch_eq_exp, mu, ← Complex.exp_neg, ← neg_mul, ← Complex.two_cos]
  push_cast [Complex.ofReal_cos]
  ring

theorem V_mul_W : V * W = 1 := by
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ k : Fin 18, V j k * W k l = (18 : ℂ)⁻¹ * ch (k * (j - l)) := by
    intro k
    have h1 : V j k * W k l = ch (j * k) * ((18 : ℂ)⁻¹ * ch (-(k * l))) := rfl
    rw [h1, show k * (j - l) = j * k + -(k * l) by
      rw [mul_sub, mul_comm k j, sub_eq_add_neg], ch_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, ch_sum]
  by_cases h : j = l
  · simp [h]
  · rw [if_neg (by simpa [sub_eq_zero] using h), if_neg h]
    ring

theorem W_mul_V : W * V = 1 := mul_eq_one_comm.mp V_mul_W

theorem sub_one_ne_add_one : ∀ u : Fin 18, u - 1 ≠ u + 1 := by decide

theorem adj_mul_V : (SimpleGraph.cycleGraph 18).adjMatrix ℂ * V = V * Matrix.diagonal mu := by
  ext u k
  have hL : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * V) u k
      = Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) (fun v => V v k) u := rfl
  rw [hL, SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair (sub_one_ne_add_one u), Matrix.mul_diagonal]
  have h1 : V (u - 1) k = ch (u * k) * ch (-k) := by
    show ch ((u - 1) * k) = _
    rw [show (u - 1) * k = u * k + -k by rw [sub_mul, one_mul, sub_eq_add_neg], ch_add]
  have h2 : V (u + 1) k = ch (u * k) * ch k := by
    show ch ((u + 1) * k) = _
    rw [show (u + 1) * k = u * k + k by rw [add_mul, one_mul], ch_add]
  rw [h1, h2, show V u k = ch (u * k) from rfl, ← ch_add_ch_neg k]
  ring

/-- The Fourier matrix as a unit of the matrix algebra. -/
noncomputable def Vunit : (Matrix (Fin 18) (Fin 18) ℂ)ˣ := ⟨V, W, V_mul_W, W_mul_V⟩

/-- For every `k`, the vector `j ↦ exp (2πi jk / 18)` is a nonzero eigenvector of the adjacency
matrix of `C₁₈` with eigenvalue `2 cos (2πk/18)`. -/
theorem huckel_C18_eigenvector (k : Fin 18) :
    (fun j : Fin 18 => ch (j * k)) ≠ 0 ∧
      Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) (fun j : Fin 18 => ch (j * k))
        = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) • fun j : Fin 18 => ch (j * k) := by
  constructor
  · intro h
    exact ch_ne_zero (0 * k) (congrFun h 0)
  · funext u
    have hL : Matrix.mulVec ((SimpleGraph.cycleGraph 18).adjMatrix ℂ)
        (fun j : Fin 18 => ch (j * k)) u
        = ((SimpleGraph.cycleGraph 18).adjMatrix ℂ * V) u k := rfl
    rw [hL, adj_mul_V, Matrix.mul_diagonal]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show V u k = ch (u * k) from rfl, mu, mul_comm]

/-- **Hückel theory for the C₁₈ annulene ring.**  The spectrum of the adjacency matrix of the
cycle graph `C₁₈` is exactly `{2 cos (2πk/18) | k = 0, …, 17}`. -/
theorem huckel_C18 :
    spectrum ℂ ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) =
      Set.range fun k : Fin 18 => ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
  have hA : (SimpleGraph.cycleGraph 18).adjMatrix ℂ
      = (Vunit : Matrix (Fin 18) (Fin 18) ℂ) * Matrix.diagonal mu
        * ((Vunit⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) := by
    rw [show ((Vunit⁻¹ : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) = W from rfl,
      show ((Vunit : (Matrix (Fin 18) (Fin 18) ℂ)ˣ) : Matrix (Fin 18) (Fin 18) ℂ) = V from rfl,
      ← adj_mul_V, mul_assoc, V_mul_W, mul_one]
  rw [hA, spectrum.units_conjugate, spectrum_diagonal]
  rfl

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

