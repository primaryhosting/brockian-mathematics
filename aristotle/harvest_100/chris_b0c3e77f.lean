/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a
-- plain block comment; it is repeated as the module docstring below.)

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix SimpleGraph

namespace Chem

/-- The primitive 13-th root of unity `exp (2πi/13)`. -/
noncomputable def zeta13 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (13 : ℕ))

lemma isPrimitiveRoot_zeta13 : IsPrimitiveRoot zeta13 13 :=
  Complex.isPrimitiveRoot_exp 13 (by norm_num)

lemma zeta13_pow_13 : zeta13 ^ 13 = 1 := isPrimitiveRoot_zeta13.pow_eq_one

lemma zeta13_pow_mod (n : ℕ) : zeta13 ^ (n % 13) = zeta13 ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 13]
  rw [pow_add, pow_mul, zeta13_pow_13, one_pow, one_mul]

/-- The additive character `m ↦ exp (2πi m /13)` on `Fin 13`. -/
noncomputable def xi (m : Fin 13) : ℂ := zeta13 ^ m.val

lemma xi_zero : xi 0 = 1 := by simp [xi]

lemma xi_add (a b : Fin 13) : xi (a + b) = xi a * xi b := by
  simp only [xi, Fin.val_add, zeta13_pow_mod, pow_add]

lemma xi_mul_eq_pow (a b : Fin 13) : xi (a * b) = xi b ^ a.val := by
  simp only [xi, Fin.val_mul, zeta13_pow_mod, ← pow_mul, mul_comm]

lemma xi_ne_zero (a : Fin 13) : xi a ≠ 0 := by
  simp [xi, zeta13, Complex.exp_ne_zero]

lemma xi_neg (a : Fin 13) : xi (-a) = (xi a)⁻¹ :=
  eq_inv_of_mul_eq_one_right (by rw [← xi_add]; simp [xi_zero])

lemma xi_eq_exp (j : Fin 13) :
    xi j = Complex.exp ((2 * Real.pi * (j : ℕ) / 13 : ℝ) * Complex.I) := by
  rw [xi, zeta13, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the character `xi j`. -/
lemma xi_add_xi_neg (j : Fin 13) :
    xi j + xi (-j) = 2 * Real.cos (2 * Real.pi * (j : ℕ) / 13) := by
  rw [xi_neg, xi_eq_exp, ← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.ofReal_cos]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Orthogonality of the characters: the character sum is `13` for the trivial character
and `0` otherwise. -/
lemma sum_xi (m : Fin 13) : ∑ j : Fin 13, xi (j * m) = if m = 0 then 13 else 0 := by
  have h1 : ∑ j : Fin 13, xi (j * m) = ∑ i ∈ Finset.range 13, xi m ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => xi m ^ i) 13]
    exact Finset.sum_congr rfl fun j _ => xi_mul_eq_pow j m
  rw [h1]
  split_ifs with hm
  · subst hm
    simp [xi_zero]
  · have hval : m.val ≠ 0 := by simpa using hm
    have hcop : Nat.Coprime m.val 13 := by
      have hp : Nat.Prime 13 := by norm_num
      rw [Nat.coprime_comm]
      refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hdvd => ?_
      have h13 := Nat.le_of_dvd (Nat.pos_of_ne_zero hval) hdvd
      have := m.isLt
      omega
    have hprim : IsPrimitiveRoot (xi m) 13 :=
      isPrimitiveRoot_zeta13.pow_of_coprime m.val hcop
    exact hprim.geom_sum_eq_zero (by norm_num)

/-- The adjacency operator of `C₁₃` acts on vectors as the sum over the two neighbours. -/
lemma adj_mulVec (v : Fin 13 → ℂ) (x : Fin 13) :
    ((cycleGraph 13).adjMatrix ℂ *ᵥ v) x = v (x - 1) + v (x + 1) := by
  have hne : x - 1 ≠ x + 1 := by
    simp only [sub_eq_add_neg, ne_eq, add_right_inj]
    decide
  rw [SimpleGraph.adjMatrix_mulVec_apply, cycleGraph_neighborFinset, Finset.sum_pair hne]

/-- **Hückel theory for the C₁₃ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some
`k ∈ {0, …, 12}`. -/
theorem huckel_C13 (μ : ℂ) :
    (∃ v : Fin 13 → ℂ, v ≠ 0 ∧ (cycleGraph 13).adjMatrix ℂ *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 13 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 13) := by
  constructor
  · rintro ⟨v, hv0, hv⟩
    have hvx : ∀ x : Fin 13, v (x - 1) + v (x + 1) = μ * v x := by
      intro x
      rw [← adj_mulVec v x, hv]
      simp
    obtain ⟨w, hw⟩ : ∃ w : Fin 13 → ℂ, ∀ j, w j = ∑ x : Fin 13, xi (-(j * x)) * v x :=
      ⟨_, fun _ => rfl⟩
    have key : ∀ j : Fin 13, μ * w j = (xi j + xi (-j)) * w j := by
      intro j
      have e1 : ∑ y : Fin 13, xi (-(j * y)) * xi (-j) * v y
          = ∑ x : Fin 13, xi (-(j * x)) * v (x - 1) := by
        refine Fintype.sum_equiv (Equiv.addRight (1 : Fin 13)) _ _ fun y => ?_
        have hh : -(j * (y + 1)) = -(j * y) + -j := by noncomm_ring
        simp only [Equiv.coe_addRight, add_sub_cancel_right, hh, xi_add]
      have e2 : ∑ y : Fin 13, xi (-(j * y)) * xi j * v y
          = ∑ x : Fin 13, xi (-(j * x)) * v (x + 1) := by
        refine Fintype.sum_equiv (Equiv.subRight (1 : Fin 13)) _ _ fun y => ?_
        have hh : -(j * (y - 1)) = -(j * y) + j := by noncomm_ring
        simp only [Equiv.subRight_apply, sub_add_cancel, hh, xi_add]
      have expand : μ * w j = ∑ x : Fin 13, xi (-(j * x)) * (v (x - 1) + v (x + 1)) := by
        rw [hw, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hvx x]
        ring
      rw [expand]
      have : ∑ x : Fin 13, xi (-(j * x)) * (v (x - 1) + v (x + 1))
          = (∑ x : Fin 13, xi (-(j * x)) * v (x - 1))
            + ∑ x : Fin 13, xi (-(j * x)) * v (x + 1) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [this, ← e1, ← e2, hw j, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    have hex : ∃ j : Fin 13, w j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hv0
      funext x0
      have h13 : (13 : ℂ) * v x0 = 0 := by
        have hsum : (0 : ℂ) = ∑ j : Fin 13, xi (j * x0) * w j := by simp [hcon]
        rw [hsum]
        have step1 : ∑ j : Fin 13, xi (j * x0) * w j
            = ∑ j : Fin 13, ∑ x : Fin 13, xi (j * (x0 - x)) * v x := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hw, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hh : j * x0 + -(j * x) = j * (x0 - x) := by noncomm_ring
          rw [← mul_assoc, ← xi_add, hh]
        have step2 : ∑ j : Fin 13, ∑ x : Fin 13, xi (j * (x0 - x)) * v x
            = ∑ x : Fin 13, (if x0 - x = 0 then (13 : ℂ) else 0) * v x := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.sum_mul, sum_xi]
        rw [step1, step2]
        simp only [sub_eq_zero]
        rw [Finset.sum_eq_single x0]
        · simp
        · intro b _ hb
          rw [if_neg (Ne.symm hb)]
          ring
        · intro hcontra
          exact absurd (Finset.mem_univ x0) hcontra
      have : v x0 = 0 := by
        rcases mul_eq_zero.mp h13 with h | h
        · exact absurd h (by norm_num)
        · exact h
      simpa using this
    obtain ⟨j, hj⟩ := hex
    refine ⟨j.val, j.isLt, ?_⟩
    rw [mul_right_cancel₀ hj (key j), xi_add_xi_neg]
  · rintro ⟨k, hk, rfl⟩
    set j : Fin 13 := ⟨k, hk⟩ with hjdef
    refine ⟨fun x => xi (j * x), ?_, ?_⟩
    · intro hzero
      have := congrFun hzero 0
      simp only [mul_zero, xi_zero, Pi.zero_apply] at this
      exact one_ne_zero this
    · funext x
      rw [adj_mulVec]
      have h1 : xi (j * (x - 1)) = xi (j * x) * xi (-j) := by
        have hh : j * (x - 1) = j * x + -j := by noncomm_ring
        rw [hh, xi_add]
      have h2 : xi (j * (x + 1)) = xi (j * x) * xi j := by
        have hh : j * (x + 1) = j * x + j := by noncomm_ring
        rw [hh, xi_add]
      have hval : ((j : ℕ) : ℝ) = (k : ℝ) := by rw [hjdef]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [h1, h2, ← hval, ← xi_add_xi_neg j]
      ring

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

