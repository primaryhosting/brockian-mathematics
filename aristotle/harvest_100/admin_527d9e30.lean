/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Polynomial

/-- The cyclic shift matrix on `ZMod n`: it sends the standard basis vector `e i` to
`e (i - 1)`, equivalently `(shift n).mulVec v i = v (i + 1)`. -/
noncomputable def shift (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The adjacency matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is adjacent to `i + 1` and `i - 1`.  In Hückel theory this is the matrix whose
eigenvalues give the π-electron energy levels (in units of `β`, relative to `α`). -/
noncomputable def cycleAdj (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

lemma shift_pow (n : ℕ) [NeZero n] (m : ℕ) :
    shift n ^ m = Matrix.of fun i j => if j = i + (m : ZMod n) then 1 else 0 := by
  induction m with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ m ih =>
      ext i j
      rw [pow_succ, Matrix.mul_apply, ih]
      rw [Finset.sum_eq_single (i + (m : ZMod n))]
      · simp [shift, add_assoc]
      · intro b _ hb
        simp [hb, shift]
      · simp

lemma shift_pow_card (n : ℕ) [NeZero n] : shift n ^ n = 1 := by
  rw [shift_pow]
  ext i j
  simp [Matrix.one_apply, eq_comm]

lemma two_ne_zero_zmod (n : ℕ) [NeZero n] (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro hc
  have h : ((2 : ℕ) : ZMod n) = 0 ↔ (n ∣ 2) := ZMod.natCast_eq_zero_iff 2 n
  have hd : n ∣ 2 := h.mp (by exact_mod_cast hc)
  have := Nat.le_of_dvd (by norm_num) hd
  omega

/-- The cycle adjacency matrix is the sum of the cyclic shift and its inverse. -/
lemma cycleAdj_eq_shift (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    cycleAdj n = shift n + shift n ^ (n - 1) := by
  have hcast : ((n - 1 : ℕ) : ZMod n) = -1 := by
    have h1 : ((n - 1 : ℕ) : ZMod n) = (n : ZMod n) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
    rw [h1]; simp
  have h2 := two_ne_zero_zmod n hn
  ext i j
  rw [shift_pow, cycleAdj]
  simp only [Matrix.add_apply, Matrix.of_apply, shift, hcast]
  have hne : (i + 1 : ZMod n) ≠ i + (-1 : ZMod n) := by
    intro h
    exact h2 (by linear_combination h)
  by_cases h1 : j = i + 1 <;> by_cases h3 : j = i + (-1 : ZMod n) <;>
    simp_all [sub_eq_add_neg]

lemma pow_val_mod (μ : ℂ) (n : ℕ) (h : μ ^ n = 1) (a : ℕ) : μ ^ (a % n) = μ ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, h, one_pow, one_mul]

lemma geom_vec_succ (n : ℕ) [NeZero n] (μ : ℂ) (h : μ ^ n = 1) (i : ZMod n) :
    μ ^ (i + 1 : ZMod n).val = μ * μ ^ i.val := by
  have hi : (i + 1 : ZMod n) = ((i.val + 1 : ℕ) : ZMod n) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    ring
  have hval : (i + 1 : ZMod n).val = (i.val + 1) % n := by
    rw [hi, ZMod.val_natCast]
  rw [hval, pow_val_mod μ n h, pow_succ]
  ring

lemma shift_mulVec (n : ℕ) [NeZero n] (v : ZMod n → ℂ) (i : ZMod n) :
    (shift n).mulVec v i = v (i + 1) := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (i + 1)]
  · simp [shift]
  · intro b _ hb; simp [shift, hb]
  · simp

/-- Every `n`-th root of unity is an eigenvalue of the cyclic shift, with the geometric
eigenvector `j ↦ μ ^ j`. -/
lemma mem_shift_spectrum (n : ℕ) [NeZero n] (μ : ℂ) (h : μ ^ n = 1) :
    μ ∈ spectrum ℂ (shift n) := by
  set v : ZMod n → ℂ := fun j => μ ^ j.val with hv
  have hv0 : v ≠ 0 := by
    intro hc
    have : v 0 = 0 := by rw [hc]; rfl
    simp [hv] at this
  have hstep : ∀ i : ZMod n, v (i + 1) = μ * v i := fun i => geom_vec_succ n μ h i
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv0, ?_⟩
  funext i
  simp only [Matrix.sub_mulVec, Pi.sub_apply, shift_mulVec, hstep, Pi.zero_apply]
  simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

/-- The spectrum of the cyclic shift matrix is exactly the set of `n`-th roots of unity. -/
lemma shift_spectrum (n : ℕ) [NeZero n] :
    spectrum ℂ (shift n) = {μ : ℂ | μ ^ n = 1} := by
  refine Set.Subset.antisymm (fun μ hμ => ?_) (fun μ hμ => mem_shift_spectrum n μ hμ)
  have hne : (spectrum ℂ (shift n)).Nonempty := ⟨1, mem_shift_spectrum n 1 (one_pow n)⟩
  have hmap := spectrum.map_polynomial_aeval_of_nonempty (shift n) (X ^ n : ℂ[X]) hne
  have h1 : (aeval (shift n)) (X ^ n : ℂ[X]) = 1 := by
    simp [map_pow, shift_pow_card]
  rw [h1, spectrum.one_eq] at hmap
  have hmem : μ ^ n ∈ ({1} : Set ℂ) := by
    rw [hmap]; exact ⟨μ, hμ, by simp⟩
  simpa using hmem

lemma pow_pred_eq_inv (μ : ℂ) (n : ℕ) (hn : 1 ≤ n) (h : μ ^ n = 1) : μ ^ (n - 1) = μ⁻¹ := by
  have hμ : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h
    exact zero_ne_one h
  have : μ ^ (n - 1) * μ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hn, h]
  field_simp at this ⊢
  linear_combination this

/-- The `k`-th root of unity contributes the Hückel energy `2 cos (2 π k / n)`. -/
lemma root_of_unity_add_inv (n k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
        + ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k)⁻¹
      = 2 * Real.cos (2 * Real.pi * k / n) := by
  rw [← Complex.exp_nat_mul]
  rw [show ((k : ℂ) * (2 * Real.pi * Complex.I / n)) = ((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [← Complex.exp_neg, neg_mul_eq_neg_mul, Complex.exp_mul_I, Complex.exp_mul_I,
    Complex.ofReal_cos, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

/-- **Hückel cycle spectrum.** The eigenvalues of the adjacency matrix of the cycle graph
`C n` (`n ≥ 3`) are exactly the numbers `2 cos (2 π k / n)` for `k = 0, …, n - 1`;
these are the Hückel π-electron energies of an `n`-membered conjugated ring
(in units of the resonance integral `β`, measured from the Coulomb integral `α`). -/
theorem huckel_cycle_spectrum (n : ℕ) [NeZero n] (hn : 3 ≤ n) :
    spectrum ℂ (cycleAdj n) =
      {z : ℂ | ∃ k : ℕ, k < n ∧ z = 2 * Real.cos (2 * Real.pi * k / n)} := by
  have hne : (spectrum ℂ (shift n)).Nonempty := ⟨1, mem_shift_spectrum n 1 (one_pow n)⟩
  have hA : cycleAdj n = aeval (shift n) (X + X ^ (n - 1) : ℂ[X]) := by
    simp [cycleAdj_eq_shift n hn]
  rw [hA, spectrum.map_polynomial_aeval_of_nonempty _ _ hne, shift_spectrum]
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, eval_add, eval_pow, eval_X]
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    obtain ⟨k, hk, rfl⟩ :=
      (Complex.isPrimitiveRoot_exp n (by omega)).eq_pow_of_pow_eq_one hμ
    refine ⟨k, hk, ?_⟩
    rw [pow_pred_eq_inv _ n (by omega) hμ, root_of_unity_add_inv]
  · rintro ⟨k, hk, rfl⟩
    have hμ : ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k) ^ n = 1 := by
      have hprim := Complex.isPrimitiveRoot_exp n (by omega)
      rw [← pow_mul, mul_comm k n, pow_mul, hprim.pow_eq_one, one_pow]
    refine ⟨(Complex.exp (2 * Real.pi * Complex.I / n)) ^ k, hμ, ?_⟩
    rw [pow_pred_eq_inv _ n (by omega) hμ, root_of_unity_add_inv]

lemma cycleAdj_mulVec (n : ℕ) [NeZero n] (hn : 3 ≤ n) (v : ZMod n → ℂ) (i : ZMod n) :
    (cycleAdj n).mulVec v i = v (i + 1) + v (i - 1) := by
  have h2 := two_ne_zero_zmod n hn
  have hne : (i + 1 : ZMod n) ≠ i - 1 := fun hh => h2 (by linear_combination hh)
  rw [Matrix.mulVec, dotProduct, ← Finset.sum_subset (Finset.subset_univ {i + 1, i - 1})]
  · rw [Finset.sum_pair hne]
    simp [cycleAdj, hne, Ne.symm hne]
  · intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp [cycleAdj, hx.1, hx.2]

/-- The explicit Hückel eigenvectors of the cycle: the "Bloch wave" `j ↦ ω ^ (k j)` with
`ω = exp (2 π i / n)` is an eigenvector of the adjacency matrix of `C n` with eigenvalue
`2 cos (2 π k / n)`. -/
theorem huckel_cycle_eigenvector (n : ℕ) [NeZero n] (hn : 3 ≤ n) (k : ℕ) :
    (cycleAdj n).mulVec (fun j => ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k) ^ j.val)
      = (2 * Real.cos (2 * Real.pi * k / n) : ℂ) •
          fun j => ((Complex.exp (2 * Real.pi * Complex.I / n)) ^ k) ^ j.val := by
  set μ : ℂ := (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k with hμdef
  have hμ : μ ^ n = 1 := by
    have hprim := Complex.isPrimitiveRoot_exp n (by omega)
    rw [hμdef, ← pow_mul, mul_comm k n, pow_mul, hprim.pow_eq_one, one_pow]
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hμ
    exact zero_ne_one hμ
  funext i
  rw [cycleAdj_mulVec n hn]
  have h1 : μ ^ (i + 1 : ZMod n).val = μ * μ ^ i.val := geom_vec_succ n μ hμ i
  have h2 : μ ^ (i : ZMod n).val = μ * μ ^ (i - 1 : ZMod n).val := by
    have := geom_vec_succ n μ hμ (i - 1)
    rwa [sub_add_cancel] at this
  have h3 : μ ^ (i - 1 : ZMod n).val = μ⁻¹ * μ ^ i.val := by
    field_simp
    linear_combination -h2
  have hcos : μ + μ⁻¹ = (2 * Real.cos (2 * Real.pi * k / n) : ℂ) := root_of_unity_add_inv n k
  simp only [Pi.smul_apply, smul_eq_mul, h1, h3]
  rw [← hcos]
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

