import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex Finset

namespace Chem

/-- `Fin 19` carries the commutative ring structure of `ZMod 19`
(the two types, and their additive group structures, are definitionally equal). -/
noncomputable local instance : CommRing (Fin 19) := (inferInstance : CommRing (ZMod 19))

/-- A primitive 19-th root of unity. -/
noncomputable def zeta19 : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((1 : ℕ) / (19 : ℕ)))

lemma zeta19_primitive : IsPrimitiveRoot zeta19 19 :=
  Complex.isPrimitiveRoot_exp_of_coprime 1 19 (by norm_num) (by norm_num)

lemma zeta19_pow19 : zeta19 ^ 19 = 1 := zeta19_primitive.pow_eq_one

lemma zeta19_pow_mod (m : ℕ) : zeta19 ^ (m % 19) = zeta19 ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 19]
  rw [pow_add, pow_mul, zeta19_pow19, one_pow, one_mul]

/-- The character `k ↦ ζ^k` on `Fin 19`. -/
noncomputable def ec (m : Fin 19) : ℂ := zeta19 ^ m.val

lemma ec_zero : ec 0 = 1 := by simp [ec]

lemma ec_add (a b : Fin 19) : ec (a + b) = ec a * ec b := by
  simp only [ec, Fin.val_add, zeta19_pow_mod, pow_add]

lemma ec_ne_zero (a : Fin 19) : ec a ≠ 0 := by
  simp [ec, zeta19, Complex.exp_ne_zero]

lemma ec_neg (a : Fin 19) : ec (-a) = (ec a)⁻¹ := by
  have h : ec a * ec (-a) = 1 := by rw [← ec_add, add_neg_cancel, ec_zero]
  exact (inv_eq_of_mul_eq_one_right h).symm

lemma ec_natCast_mul (m : ℕ) (d : Fin 19) : ec ((m : Fin 19) * d) = ec d ^ m := by
  induction m with
  | zero => simp [ec_zero]
  | succ m ih =>
      have : ((m + 1 : ℕ) : Fin 19) * d = (m : Fin 19) * d + d := by push_cast; ring
      rw [this, ec_add, ih, pow_succ]

lemma ec_eq_exp (k : Fin 19) :
    ec k = Complex.exp (((2 * Real.pi * k.val / 19 : ℝ) : ℂ) * Complex.I) := by
  rw [ec, zeta19, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The Hückel eigenvalues. -/
noncomputable def lam (k : Fin 19) : ℂ := ((2 * Real.cos (2 * Real.pi * k.val / 19) : ℝ) : ℂ)

lemma ec_add_ec_neg (k : Fin 19) : ec k + ec (-k) = lam k := by
  set t : ℝ := 2 * Real.pi * k.val / 19 with ht
  have h1 : ec k = Complex.exp ((t : ℂ) * Complex.I) := ec_eq_exp k
  have h2 : ec (-k) = Complex.exp (-(t : ℂ) * Complex.I) := by
    rw [ec_neg, h1, ← Complex.exp_neg]
    ring_nf
  rw [h1, h2, ← Complex.two_cos, lam, ← ht]
  push_cast
  ring

/-- The DFT matrix. -/
noncomputable def Fm : Matrix (Fin 19) (Fin 19) ℂ := fun u k => ec (u * k)

/-- The conjugate DFT matrix. -/
noncomputable def Gm : Matrix (Fin 19) (Fin 19) ℂ := fun k w => ec (-(k * w))

lemma sum_ec_mul (d : Fin 19) :
    (∑ k : Fin 19, ec (k * d)) = if d = 0 then (19 : ℂ) else 0 := by
  have hstep : ∀ k : Fin 19, ec (k * d) = ec d ^ (k : ℕ) := by
    intro k
    conv_lhs => rw [← Fin.cast_val_eq_self k]
    exact ec_natCast_mul k.val d
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [Fin.sum_univ_eq_sum_range (fun j => ec d ^ j) 19]
  by_cases hd : d = 0
  · subst hd
    simp [ec_zero]
  · have hne : ec d ≠ 1 := by
      have hv : d.val ≠ 0 := by
        intro h
        exact hd (Fin.ext (by simpa using h))
      exact zeta19_primitive.pow_ne_one_of_pos_of_lt hv d.isLt
    have hpow : ec d ^ 19 = 1 := by
      rw [ec, ← pow_mul, mul_comm, pow_mul, zeta19_pow19, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div, if_neg hd]

lemma Fm_mul_Gm : Fm * Gm = (19 : ℂ) • (1 : Matrix (Fin 19) (Fin 19) ℂ) := by
  ext u w
  rw [Matrix.mul_apply]
  have hterm : ∀ k : Fin 19, Fm u k * Gm k w = ec (k * (u - w)) := by
    intro k
    rw [Fm, Gm, ← ec_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), sum_ec_mul]
  by_cases h : u = w
  · subst h
    simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    simp [Matrix.one_apply_ne h]

lemma Fm_det_ne_zero : Fm.det ≠ 0 := by
  intro h
  have h1 : (Fm * Gm).det = 0 := by rw [Matrix.det_mul, h, zero_mul]
  rw [Fm_mul_Gm, Matrix.det_smul, Matrix.det_one, mul_one] at h1
  simp at h1

lemma adj_mul_Fm :
    ((SimpleGraph.cycleGraph 19).adjMatrix ℂ) * Fm = Fm * Matrix.diagonal lam := by
  ext u k
  have hmv : (((SimpleGraph.cycleGraph 19).adjMatrix ℂ) * Fm) u k
      = ∑ v ∈ (SimpleGraph.cycleGraph 19).neighborFinset u, Fm v k := by
    rw [Matrix.mul_apply]
    have := SimpleGraph.adjMatrix_mulVec_apply (α := ℂ) (SimpleGraph.cycleGraph 19) u
      (fun v => Fm v k)
    simpa [Matrix.mulVec, dotProduct] using this
  rw [hmv, SimpleGraph.cycleGraph_neighborFinset (n := 17),
    Finset.sum_pair (by
      intro h
      rw [sub_eq_add_neg] at h
      exact absurd (add_left_cancel h) (by decide))]
  rw [Matrix.mul_diagonal, ← ec_add_ec_neg k]
  have e1 : (u - 1) * k = u * k + (-k) := by ring
  have e2 : (u + 1) * k = u * k + k := by ring
  simp only [Fm, e1, e2, ec_add]
  ring

/-- **Hückel theory for the C₁₉ cycle.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₉` is `∏_{k=0}^{18} (X - 2 cos (2πk/19))`; equivalently, the
adjacency eigenvalues of `C₁₉` are exactly `2 cos (2πk/19)` for `k = 0, …, 18`. -/
theorem huckel_C19 :
    ((SimpleGraph.cycleGraph 19).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 19,
        (X - C ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)) := by
  set A : Matrix (Fin 19) (Fin 19) ℂ := (SimpleGraph.cycleGraph 19).adjMatrix ℂ with hA
  set D : Matrix (Fin 19) (Fin 19) ℂ := Matrix.diagonal lam with hD
  set F' : Matrix (Fin 19) (Fin 19) ℂ[X] := (C : ℂ →+* ℂ[X]).mapMatrix Fm with hF'
  have hcomm : Matrix.scalar (Fin 19) (X : ℂ[X]) * F' = F' * Matrix.scalar (Fin 19) (X : ℂ[X]) := by
    simp [Matrix.scalar, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.ext_iff.symm,
      mul_comm]
  have hmain : charmatrix A * F' = F' * charmatrix D := by
    rw [charmatrix, charmatrix, sub_mul, mul_sub, hcomm, ← map_mul, ← map_mul, adj_mul_Fm]
  have hdet : (charmatrix A).det * F'.det = F'.det * (charmatrix D).det := by
    rw [← Matrix.det_mul, ← Matrix.det_mul, hmain]
  have hF'det : F'.det = C Fm.det := by
    rw [hF', RingHom.mapMatrix_apply]
    exact (RingHom.map_det C Fm).symm
  have hne : F'.det ≠ 0 := by
    rw [hF'det]
    simpa using Fm_det_ne_zero
  have hcp : A.charpoly = (charmatrix D).det := by
    rw [Matrix.charpoly]
    rw [mul_comm F'.det (charmatrix D).det] at hdet
    exact mul_right_cancel₀ hne hdet
  rw [hcp, ← Matrix.charpoly, hD, Matrix.charpoly_diagonal]
  exact Fin.prod_univ_eq_prod_range
    (fun j => X - C ((2 * Real.cos (2 * Real.pi * j / 19) : ℝ) : ℂ)) 19

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

