import Mathlib

/-!
# Hückel spectrum of the cycle graph `C₁₂`

We show that the eigenvalues (i.e. the spectrum) of the adjacency matrix of the cycle graph
`C₁₂`, viewed as a complex matrix indexed by `ZMod 12`, are exactly the numbers
`2 * cos (2 * π * k / 12)` for `k = 0, …, 11`.

The proof goes through the cyclic shift matrix `S` on `ZMod 12`: the adjacency matrix is
`S + S ^ 11`, the spectrum of `S` is the set of `12`-th roots of unity, and the polynomial
spectral mapping theorem over `ℂ` transports this to the adjacency matrix.
-/

namespace Chem

open Matrix Polynomial

/-- The cyclic shift matrix on `ZMod 12`. -/
def shift12 : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.of fun i j => if j = i + 1 then 1 else 0

/-- The adjacency matrix of the cycle graph `C₁₂`, with vertices indexed by `ZMod 12`:
two vertices are adjacent iff they differ by `1`. -/
def C12adj : Matrix (ZMod 12) (ZMod 12) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- `C12adj` is indeed the adjacency matrix of Mathlib's cycle graph on `12` vertices
(`ZMod 12` and `Fin 12` are the same type). -/
lemma C12adj_eq_adjMatrix : C12adj = (SimpleGraph.cycleGraph 12).adjMatrix ℂ := by
  ext i j
  simp only [C12adj, Matrix.of_apply, SimpleGraph.adjMatrix_apply]
  have h : ((SimpleGraph.cycleGraph 12).Adj i j) ↔ (j = i + 1 ∨ j = i - 1) := by
    revert i j; decide
  simp [h]

lemma shift12_pow (n : ℕ) :
    shift12 ^ n = Matrix.of fun i j => if j = i + (n : ZMod 12) then 1 else 0 := by
  induction n with
  | zero => ext i j; simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
      ext i j
      rw [pow_succ, Matrix.mul_apply, ih]
      simp only [Matrix.of_apply, shift12, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      push_cast
      rw [add_assoc]

lemma shift12_pow_12 : shift12 ^ 12 = 1 := by
  have h : (12 : ZMod 12) = 0 := by decide
  rw [shift12_pow]
  ext i j
  simp [Matrix.one_apply, eq_comm, h]

lemma C12adj_eq : C12adj = shift12 + shift12 ^ 11 := by
  have key : ∀ i : ZMod 12, i + 1 ≠ i - 1 := by decide
  ext i j
  have h11 : ((11 : ℕ) : ZMod 12) = -1 := by decide
  rw [shift12_pow]
  simp only [C12adj, shift12, Matrix.of_apply, Matrix.add_apply, h11, ← sub_eq_add_neg]
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
    simp [h1, h2, key i, Ne.symm (key i)]

/-- The spectrum of the cyclic shift matrix consists exactly of the `12`-th roots of unity. -/
lemma spectrum_shift12 : spectrum ℂ shift12 = {z : ℂ | z ^ 12 = 1} := by
  apply Set.eq_of_subset_of_subset
  · intro z hz
    have h1 : z ^ 12 ∈ spectrum ℂ (shift12 ^ 12) :=
      spectrum.pow_image_subset shift12 12 ⟨z, hz, rfl⟩
    rw [shift12_pow_12, spectrum.one_eq] at h1
    exact h1
  · intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rw [spectrum.mem_iff]
    intro hu
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hu
    apply hu
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun j => z ^ j.val, ?_, ?_⟩
    · intro h
      have := congrFun h 0
      simp at this
    · have pow_mod : ∀ m : ℕ, z ^ (m % 12) = z ^ m := by
        intro m
        conv_rhs => rw [← Nat.div_add_mod m 12]
        rw [pow_add, pow_mul, hz, one_pow, one_mul]
      have hval : ∀ i : ZMod 12, (i + 1).val = (i.val + 1) % 12 := by decide
      funext i
      rw [Algebra.algebraMap_eq_smul_one]
      simp only [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      have hs : (shift12.mulVec fun j => z ^ j.val) i = z ^ (i + 1).val := by
        simp [Matrix.mulVec, shift12, dotProduct]
      rw [hs, hval i, pow_mod, pow_succ]
      ring

/-- The `12`-th roots of unity, described via the complex exponential. -/
lemma rootsOfUnity12 :
    {z : ℂ | z ^ 12 = 1}
      = Set.range (fun k : Fin 12 => Complex.exp (2 * Real.pi * Complex.I * k / 12)) := by
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12)) 12 :=
    Complex.isPrimitiveRoot_exp 12 (by norm_num)
  have hpow : ∀ k : ℕ, (Complex.exp (2 * Real.pi * Complex.I / 12)) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * k / 12) := by
    intro k
    rw [← Complex.exp_nat_mul]
    ring_nf
  apply Set.eq_of_subset_of_subset
  · intro z hz
    obtain ⟨i, hi, hzi⟩ := hprim.eq_pow_of_pow_eq_one hz
    refine ⟨⟨i, hi⟩, ?_⟩
    show Complex.exp (2 * Real.pi * Complex.I * ((⟨i, hi⟩ : Fin 12) : ℕ) / 12) = z
    rw [Fin.val_mk, ← hpow i, hzi]
  · rintro _ ⟨k, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← hpow (k : ℕ), ← pow_mul, mul_comm (k : ℕ) 12, pow_mul, hprim.pow_eq_one, one_pow]

/-- For a `12`-th root of unity written as `exp (2πik/12)`, the value `z + z¹¹ = z + z⁻¹`
is `2 cos (2πk/12)`. -/
lemma exp_add_pow_eleven (k : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * k / 12)
        + (Complex.exp (2 * Real.pi * Complex.I * k / 12)) ^ 11
      = ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * k / 12 with hθ
  have hz : Complex.exp (2 * Real.pi * Complex.I * k / 12)
      = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hθ]; push_cast; ring_nf
  have h11 : (Complex.exp ((θ : ℂ) * Complex.I)) ^ 11 = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [← Complex.exp_nat_mul,
      show ((11 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I)
          = -((θ : ℂ) * Complex.I) + (k : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) from by
        rw [hθ]; push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hz, h11]
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- **Hückel theory for the 12-cycle**: the adjacency eigenvalues of the cycle graph `C₁₂`
are `2 cos (2πk/12)` for `k = 0, …, 11`. -/
theorem huckel_C12 :
    spectrum ℂ C12adj
      = Set.range (fun k : Fin 12 => ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)) := by
  have hp : C12adj = aeval shift12 (X + X ^ 11 : ℂ[X]) := by
    simp [C12adj_eq]
  have hdeg : (0 : WithBot ℕ) < (X + X ^ 11 : ℂ[X]).degree := by
    have h : (X + X ^ 11 : ℂ[X]).degree = 11 := by compute_degree!
    rw [h]; norm_num
  rw [hp, spectrum.map_polynomial_aeval_of_degree_pos _ _ hdeg,
    spectrum_shift12, rootsOfUnity12, ← Set.range_comp]
  apply congrArg Set.range
  funext k
  simpa only [Function.comp_apply, eval_add, eval_pow, eval_X] using exp_add_pow_eleven (k : ℕ)

/-- The same statement phrased with Mathlib's cycle graph `SimpleGraph.cycleGraph 12`. -/
theorem huckel_cycleGraph_12 :
    spectrum ℂ ((SimpleGraph.cycleGraph 12).adjMatrix ℂ)
      = Set.range (fun k : Fin 12 => ((2 * Real.cos (2 * Real.pi * k / 12) : ℝ) : ℂ)) := by
  have key := huckel_C12
  rw [C12adj_eq_adjMatrix] at key
  exact key

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

