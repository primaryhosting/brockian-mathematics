import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 15)

/-- The additive character `a ↦ ζ^a` of `ZMod 15`. -/
noncomputable def chi (a : ZMod 15) : ℂ := zeta ^ a.val

/-- The adjacency matrix of the cycle graph `C₁₅`, indexed by `ZMod 15`:
vertices `i` and `j` are adjacent iff they differ by `1`. -/
def A : Matrix (ZMod 15) (ZMod 15) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The `k`-th Fourier eigenvector. -/
noncomputable def v (k : ZMod 15) : ZMod 15 → ℂ := fun j => chi (k * j)

lemma zeta_isPrimitiveRoot : IsPrimitiveRoot zeta 15 := by
  have := Complex.isPrimitiveRoot_exp 15 (by norm_num)
  simpa [zeta, mul_comm, mul_assoc, mul_left_comm] using this

lemma zeta_pow_15 : zeta ^ 15 = 1 := zeta_isPrimitiveRoot.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := by
  intro h
  have := zeta_pow_15
  rw [h] at this
  simp at this

lemma zeta_pow_mod (m : ℕ) : zeta ^ (m % 15) = zeta ^ m := by
  conv_rhs => rw [← Nat.div_add_mod m 15, pow_add, pow_mul, zeta_pow_15, one_pow, one_mul]

lemma chi_natCast (m : ℕ) : chi (m : ZMod 15) = zeta ^ m := by
  rw [chi, ZMod.val_natCast, zeta_pow_mod]

lemma chi_add (a b : ZMod 15) : chi (a + b) = chi a * chi b := by
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective a
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective b
  rw [← Nat.cast_add, chi_natCast, chi_natCast, chi_natCast, pow_add]

lemma chi_zero : chi 0 = 1 := by simp [chi]

lemma chi_ne_zero (a : ZMod 15) : chi a ≠ 0 := pow_ne_zero _ zeta_ne_zero

lemma chi_eq_one_iff (a : ZMod 15) : chi a = 1 ↔ a = 0 := by
  constructor
  · intro h
    have h15 : (15 : ℕ) ∣ a.val := (zeta_isPrimitiveRoot.pow_eq_one_iff_dvd a.val).mp h
    have hlt := ZMod.val_lt a
    have hv : a.val = 0 := by
      rcases Nat.eq_zero_or_pos a.val with h0 | h0
      · exact h0
      · exact absurd (Nat.le_of_dvd h0 h15) (by omega)
    exact (ZMod.val_eq_zero a).mp hv
  · rintro rfl; exact chi_zero

lemma chi_neg (a : ZMod 15) : chi (-a) = (chi a)⁻¹ := by
  have : chi (-a) * chi a = 1 := by rw [← chi_add]; simp [chi_zero]
  field_simp [chi_ne_zero a] at this ⊢
  linear_combination this

/-- Character sum orthogonality. -/
lemma sum_chi (a : ZMod 15) :
    ∑ k : ZMod 15, chi (k * a) = if a = 0 then 15 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [chi_zero]
  · simp only [ha, if_false]
    set S := ∑ k : ZMod 15, chi (k * a) with hS
    have hshift : ∑ k : ZMod 15, chi ((k + 1) * a) = S := by
      rw [hS]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 15)) _ _ (fun k => rfl)
    have hexp : ∑ k : ZMod 15, chi ((k + 1) * a) = chi a * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [add_mul, one_mul, chi_add, mul_comm]
    have : chi a * S = S := by rw [← hexp, hshift]
    have hne : chi a - 1 ≠ 0 := sub_ne_zero_of_ne ((chi_eq_one_iff a).not.mpr ha)
    have : (chi a - 1) * S = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h

/-- The two neighbours of `i` in `C₁₅`. -/
lemma A_apply (i j : ZMod 15) :
    A i j = (if j = i - 1 then 1 else 0) + (if j = i + 1 then 1 else 0) := by
  have h1 : (i - j = 1) ↔ j = i - 1 :=
    ⟨fun h => by linear_combination -h, fun h => by linear_combination -h⟩
  have h2 : (j - i = 1) ↔ j = i + 1 :=
    ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩
  have hne : ¬ (j = i - 1 ∧ j = i + 1) := by
    rintro ⟨rfl, h⟩
    have h2 : (2 : ZMod 15) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  unfold A
  simp only [h1, h2]
  by_cases ha : j = i - 1 <;> by_cases hb : j = i + 1 <;> simp_all

/-- Matrix-vector product with the adjacency matrix is the "neighbour sum". -/
lemma A_mulVec (x : ZMod 15 → ℂ) (i : ZMod 15) :
    (A *ᵥ x) i = x (i - 1) + x (i + 1) := by
  simp only [Matrix.mulVec, dotProduct, A_apply, add_mul, Finset.sum_add_distrib,
    ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma chi_eq_exp (k : ZMod 15) :
    chi k = Complex.exp ((2 * Real.pi * k.val / 15 : ℝ) * Complex.I) := by
  rw [chi, zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to the `k`-th Fourier mode. -/
lemma chi_add_chi_neg (k : ZMod 15) :
    chi k + chi (-k) = 2 * Real.cos (2 * Real.pi * k.val / 15) := by
  have hinv : chi (-k) = Complex.exp (-((2 * Real.pi * k.val / 15 : ℝ) : ℂ) * Complex.I) := by
    rw [chi_neg, chi_eq_exp, ← Complex.exp_neg]
    congr 1
    ring
  rw [chi_eq_exp, hinv, Complex.ofReal_cos, ← Complex.two_cos]

/-- Each Fourier vector is an eigenvector with eigenvalue `2cos(2πk/15)`. -/
lemma A_mulVec_v (k : ZMod 15) :
    A *ᵥ v k = ((2 : ℂ) * Real.cos (2 * Real.pi * k.val / 15)) • v k := by
  funext i
  rw [A_mulVec, Pi.smul_apply, smul_eq_mul, ← chi_add_chi_neg]
  show chi (k * (i - 1)) + chi (k * (i + 1)) = _
  have e1 : k * (i - 1) = -k + k * i := by ring
  have e2 : k * (i + 1) = k + k * i := by ring
  rw [e1, e2, chi_add, chi_add]
  show _ = (chi k + chi (-k)) * chi (k * i)
  ring

lemma v_ne_zero (k : ZMod 15) : v k ≠ 0 := by
  intro h
  have : v k 0 = 0 := by rw [h]; rfl
  rw [v, mul_zero, chi_zero] at this
  exact one_ne_zero this

/-- **Hückel theory for the cycle `C₁₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₅` if and only if `μ = 2·cos(2πk/15)` for some
`k ∈ {0, 1, …, 14}`. -/
theorem huckel_C15 (μ : ℂ) :
    (∃ x : ZMod 15 → ℂ, x ≠ 0 ∧ A *ᵥ x = μ • x) ↔
      ∃ k < 15, μ = 2 * Real.cos (2 * Real.pi * k / 15) := by
  constructor
  · rintro ⟨x, hx, hEq⟩
    by_contra hcon
    push_neg at hcon
    -- Fourier coefficients of `x`
    set c : ZMod 15 → ℂ := fun k => ∑ j : ZMod 15, chi (-(k * j)) * x j with hcdef
    have shift : ∀ f : ZMod 15 → ℂ, ∑ j : ZMod 15, f (j + 1) = ∑ j : ZMod 15, f j :=
      fun f => Fintype.sum_equiv (Equiv.addRight (1 : ZMod 15)) _ _ (fun j => rfl)
    have hev : ∀ j : ZMod 15, x (j - 1) + x (j + 1) = μ * x j := by
      intro j
      rw [← A_mulVec x j, hEq]
      rfl
    have key : ∀ k : ZMod 15, (chi k + chi (-k)) * c k = μ * c k := by
      intro k
      have h1 : ∑ j : ZMod 15, chi (-(k * j)) * x (j - 1) = chi (-k) * c k := by
        rw [← shift (fun j => chi (-(k * j)) * x (j - 1))]
        simp only [add_sub_cancel_right]
        rw [hcdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have : -(k * (j + 1)) = -k + -(k * j) := by ring
        rw [this, chi_add, mul_assoc]
      have h2 : ∑ j : ZMod 15, chi (-(k * j)) * x (j + 1) = chi k * c k := by
        rw [← shift (fun j => chi (-(k * j)) * x (j + 1))]
        simp only [sub_add_cancel]
        rw [hcdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hj : ∀ j : ZMod 15, chi (-(k * (j - 1))) * x j = chi k * (chi (-(k * j)) * x j) := by
          intro j
          have : -(k * (j - 1)) = k + -(k * j) := by ring
          rw [this, chi_add, mul_assoc]
        exact hj (j + 1 - 1) |>.trans (by rw [add_sub_cancel_right])
      have h3 : ∑ j : ZMod 15, chi (-(k * j)) * (x (j - 1) + x (j + 1))
          = (chi (-k) + chi k) * c k := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, h1, h2, add_mul]
      have h4 : ∑ j : ZMod 15, chi (-(k * j)) * (x (j - 1) + x (j + 1)) = μ * c k := by
        rw [hcdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hev j]
        ring
      rw [← h4, h3]
      ring
    have hczero : ∀ k : ZMod 15, c k = 0 := by
      intro k
      have hne : μ ≠ chi k + chi (-k) := by
        rw [chi_add_chi_neg]
        exact_mod_cast hcon k.val (ZMod.val_lt k)
      have := key k
      rcases mul_eq_zero.mp (show (chi k + chi (-k) - μ) * c k = 0 by linear_combination this)
        with h | h
      · exact absurd (sub_eq_zero.mp h).symm hne
      · exact h
    apply hx
    funext j
    have hinv : ∑ k : ZMod 15, chi (k * j) * c k = 15 * x j := by
      have : ∀ k : ZMod 15, chi (k * j) * c k
          = ∑ j' : ZMod 15, chi (k * (j - j')) * x j' := by
        intro k
        rw [hcdef, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        have : k * (j - j') = k * j + -(k * j') := by ring
        rw [this, chi_add, mul_assoc]
      rw [Finset.sum_congr rfl (fun k _ => this k), Finset.sum_comm]
      have : ∀ j' : ZMod 15, ∑ k : ZMod 15, chi (k * (j - j')) * x j'
          = (if j - j' = 0 then (15 : ℂ) else 0) * x j' := by
        intro j'
        rw [← Finset.sum_mul, sum_chi]
      rw [Finset.sum_congr rfl (fun j' _ => this j')]
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        have : j - b ≠ 0 := sub_ne_zero_of_ne (Ne.symm hb)
        simp [this]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have : (15 : ℂ) * x j = 0 := by
      rw [← hinv]
      exact Finset.sum_eq_zero (fun k _ => by rw [hczero k, mul_zero])
    have h15 : (15 : ℂ) ≠ 0 := by norm_num
    simpa [h15] using this
  · rintro ⟨k, hk, rfl⟩
    refine ⟨v (k : ZMod 15), v_ne_zero _, ?_⟩
    have hval : ((k : ZMod 15)).val = k := ZMod.val_cast_of_lt hk
    have := A_mulVec_v (k : ZMod 15)
    rw [hval] at this
    exact this

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

