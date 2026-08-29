/-
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial Finset

namespace Chem

/-! ### The cyclic shift operator -/

/-- The cyclic shift endomorphism of `Fin 13 → ℂ`, `f ↦ (i ↦ f (i + 1))`. -/
noncomputable def shift : Module.End ℂ (Fin 13 → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun i : Fin 13 => i + 1)

@[simp] lemma shift_apply (f : Fin 13 → ℂ) (i : Fin 13) : shift f i = f (i + 1) := rfl

lemma shift_pow_apply (m : ℕ) : ∀ (f : Fin 13 → ℂ) (i : Fin 13),
    (shift ^ m) f i = f (i + m • (1 : Fin 13)) := by
  induction m with
  | zero => intro f i; simp
  | succ m ih =>
      intro f i
      rw [pow_succ]
      show (shift ^ m) (shift f) i = _
      rw [ih (shift f) i, shift_apply, succ_nsmul, ← add_assoc]

lemma shift_pow_thirteen : shift ^ 13 = 1 := by
  refine LinearMap.ext fun f => funext fun i => ?_
  rw [shift_pow_apply, show (13 : ℕ) • (1 : Fin 13) = 0 from by decide, add_zero]
  rfl

/-! ### The adjacency operator of the cycle graph -/

/-- The adjacency operator of the cycle graph `C₁₃`, as an endomorphism of `Fin 13 → ℂ`. -/
noncomputable def cycA : Module.End ℂ (Fin 13 → ℂ) := shift + shift ^ 12

lemma cycA_apply (f : Fin 13 → ℂ) (i : Fin 13) : cycA f i = f (i + 1) + f (i + 12) := by
  show shift f i + (shift ^ 12) f i = _
  rw [shift_apply, shift_pow_apply, show (12 : ℕ) • (1 : Fin 13) = 12 from by decide]

lemma fin13_sub_one (i : Fin 13) : i - 1 = i + 12 := by revert i; decide

lemma fin13_sub_one_ne (i : Fin 13) : (i - 1 : Fin 13) ≠ i + 1 := by revert i; decide

lemma adjMatrix_mulVec_eq (v : Fin 13 → ℂ) :
    ((SimpleGraph.cycleGraph 13).adjMatrix ℂ).mulVec v = cycA v := by
  funext i
  rw [SimpleGraph.adjMatrix_mulVec_apply, cycA_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 11) (v := i),
    Finset.sum_pair (fin13_sub_one_ne i), fin13_sub_one i]
  ring

/-! ### The 13-th roots of unity -/

/-- `ζ = exp (2πi/13)`, a primitive 13-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 13)

lemma zeta_primitive : IsPrimitiveRoot zeta 13 := by
  simpa [zeta] using Complex.isPrimitiveRoot_exp 13 (by norm_num)

lemma zeta_pow_thirteen : zeta ^ 13 = 1 := zeta_primitive.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_congr {a b : ℕ} (h : a ≡ b [MOD 13]) : zeta ^ a = zeta ^ b := by
  have key : ∀ c : ℕ, zeta ^ c = zeta ^ (c % 13) := by
    intro c
    conv_lhs => rw [← Nat.div_add_mod c 13]
    rw [pow_add, pow_mul, zeta_pow_thirteen, one_pow, one_mul]
  rw [key a, key b, h]

/-- `ζ^k + ζ^{-k} = 2 cos (2πk/13)`. -/
lemma zeta_pow_add_inv (k : ℕ) :
    zeta ^ k + (zeta ^ k)⁻¹ = 2 * (Real.cos (2 * Real.pi * k / 13) : ℂ) := by
  have hz : zeta ^ k = Complex.exp (((2 * Real.pi * k / 13 : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hz, ← Complex.exp_neg, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-! ### The characteristic factorisation -/

/-- The polynomial whose roots are the claimed eigenvalues. -/
noncomputable def qpoly : ℂ[X] := ∏ w ∈ nthRootsFinset 13 (1 : ℂ), (X - C (w + w⁻¹))

lemma qpoly_comp_eq :
    qpoly.comp (X + X ^ 12) =
      ∏ w ∈ nthRootsFinset 13 (1 : ℂ), ((X + X ^ 12) - C (w + w⁻¹)) := by
  rw [qpoly, Polynomial.prod_comp]
  refine Finset.prod_congr rfl fun w _ => ?_
  simp

lemma dvd_qpoly_comp : (X ^ 13 - 1 : ℂ[X]) ∣ qpoly.comp (X + X ^ 12) := by
  rw [qpoly_comp_eq, Polynomial.X_pow_sub_one_eq_prod (by norm_num) zeta_primitive]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun w hw => ?_
  have hw1 : w ^ 13 = 1 := (Polynomial.mem_nthRootsFinset (by norm_num) _).1 hw
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hw1
    simp at hw1
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
  have h12 : w ^ 12 = w⁻¹ := by
    field_simp
    linear_combination hw1
  simp [h12]

lemma aeval_cycA_qpoly : (Polynomial.aeval cycA) qpoly = 0 := by
  have hcyc : (Polynomial.aeval shift) (X + X ^ 12 : ℂ[X]) = cycA := by
    simp [cycA]
  obtain ⟨r, hr⟩ := dvd_qpoly_comp
  have h1 : (Polynomial.aeval shift) (qpoly.comp (X + X ^ 12)) = 0 := by
    rw [hr, map_mul, map_sub, map_pow, map_one, Polynomial.aeval_X, shift_pow_thirteen,
      sub_self, zero_mul]
  rwa [Polynomial.aeval_comp, hcyc] at h1

/-! ### Main theorem -/

/-- **Hückel theory for C₁₃.** A complex number `μ` is an eigenvalue of the adjacency matrix
of the cycle graph `C₁₃` if and only if `μ = 2 cos (2πk/13)` for some `k ∈ {0, …, 12}`. -/
theorem huckel_C13 (μ : ℂ) :
    (∃ v : Fin 13 → ℂ, v ≠ 0 ∧ ((SimpleGraph.cycleGraph 13).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 13 ∧ μ = 2 * (Real.cos (2 * Real.pi * k / 13) : ℂ) := by
  constructor
  · rintro ⟨v, hv, hA⟩
    rw [adjMatrix_mulVec_eq] at hA
    have hev : cycA.HasEigenvector μ v :=
      ⟨Module.End.mem_eigenspace_iff.2 hA, hv⟩
    have h0 : (qpoly.eval μ) • v = 0 := by
      rw [← Module.End.aeval_apply_of_hasEigenvector hev, aeval_cycA_qpoly]
      simp
    have hq : qpoly.eval μ = 0 := by
      rcases smul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hv
    rw [qpoly, Polynomial.eval_prod] at hq
    obtain ⟨w, hw, hw0⟩ := Finset.prod_eq_zero_iff.1 hq
    have hw1 : w ^ 13 = 1 := (Polynomial.mem_nthRootsFinset (by norm_num) _).1 hw
    obtain ⟨k, hk, rfl⟩ := zeta_primitive.eq_pow_of_pow_eq_one hw1
    refine ⟨k, hk, ?_⟩
    rw [← zeta_pow_add_inv k]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hw0
    exact sub_eq_zero.1 hw0
  · rintro ⟨k, hk, rfl⟩
    refine ⟨fun x : Fin 13 => zeta ^ (k * x.val), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · rw [adjMatrix_mulVec_eq]
      funext i
      rw [cycA_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      have hv1 : ((i + 1 : Fin 13)).val = (i.val + 1) % 13 := rfl
      have hv12 : ((i + 12 : Fin 13)).val = (i.val + 12) % 13 := rfl
      have m1 : k * ((i + 1 : Fin 13)).val ≡ k * i.val + k [MOD 13] := by
        rw [hv1]
        calc k * ((i.val + 1) % 13)
            ≡ k * (i.val + 1) [MOD 13] := Nat.ModEq.mul_left k (Nat.mod_modEq _ _)
          _ = k * i.val + k := by ring
      have m12 : k * ((i + 12 : Fin 13)).val ≡ k * i.val + 12 * k [MOD 13] := by
        rw [hv12]
        calc k * ((i.val + 12) % 13)
            ≡ k * (i.val + 12) [MOD 13] := Nat.ModEq.mul_left k (Nat.mod_modEq _ _)
          _ = k * i.val + 12 * k := by ring
      have h12 : zeta ^ (12 * k) = (zeta ^ k)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← pow_add, show 12 * k + k = 13 * k from by ring, pow_mul, zeta_pow_thirteen,
          one_pow]
      rw [zeta_pow_congr m1, zeta_pow_congr m12, pow_add, pow_add, h12, ← zeta_pow_add_inv k]
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

