/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₅`

The eigenvalues of the adjacency matrix of the cycle graph `C₁₅` are exactly the
numbers `2 cos (2πk/15)` for `k = 0, …, 14`.  (In Hückel molecular orbital theory these
are the orbital energies `α + 2β cos(2πk/15)` of a cyclic conjugated system with 15
centres, in units where `α = 0`, `β = 1`.)

The proof diagonalises the (circulant) adjacency matrix using the discrete Fourier
transform on `ZMod 15`.
-/

namespace Chem

open Complex Finset ZMod

/-- The adjacency matrix of the cycle graph `C₁₅`, with vertices indexed by `ZMod 15`:
two vertices are adjacent exactly when they differ by `1`. -/
def C15adj : Matrix (ZMod 15) (ZMod 15) ℂ :=
  fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The adjacency matrix acts on a vector by summing the values at the two neighbours. -/
lemma C15adj_mulVec (v : ZMod 15 → ℂ) (i : ZMod 15) :
    C15adj.mulVec v i = v (i - 1) + v (i + 1) := by
  classical
  have hfil : (univ.filter (fun j : ZMod 15 => i - j = 1 ∨ j - i = 1)) = {i - 1, i + 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
    · rintro (h | h)
      · left; linear_combination -h
      · right; linear_combination h
  have hne : (i - 1 : ZMod 15) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 15) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  simp only [Matrix.mulVec, dotProduct, C15adj, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    hfil]
  rw [Finset.sum_pair hne]

/-- The standard additive character satisfies `e(κ) + e(-κ) = 2 cos (2πκ/15)`. -/
lemma stdAddChar_add_neg (κ : ZMod 15) :
    (stdAddChar κ : ℂ) + (stdAddChar (-κ) : ℂ) = 2 * Real.cos (2 * Real.pi * κ.val / 15) := by
  set θ : ℝ := 2 * Real.pi * κ.val / 15 with hθ
  have h1 : (stdAddChar κ : ℂ) = Complex.exp (θ * I) := by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
    congr 1
    push_cast [hθ]
    ring
  have h2 : (stdAddChar κ : ℂ) * (stdAddChar (-κ) : ℂ) = 1 := by
    rw [← AddChar.map_add_eq_mul]; simp
  have h3 : (stdAddChar (-κ) : ℂ) = Complex.exp (-(θ * I)) := by
    rw [Complex.exp_neg]
    refine (inv_eq_of_mul_eq_one_left ?_).symm
    rw [← h1, mul_comm]; exact h2
  rw [h1, h3, ← neg_mul, ← Complex.two_cos, Complex.ofReal_cos]

/-- The discrete Fourier transform diagonalises the adjacency matrix of `C₁₅`. -/
lemma dft_C15adj_mulVec (v : ZMod 15 → ℂ) (k : ZMod 15) :
    ZMod.dft (C15adj.mulVec v) k
      = ((stdAddChar k : ℂ) + (stdAddChar (-k) : ℂ)) * ZMod.dft v k := by
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [C15adj_mulVec, smul_eq_mul, mul_add]
  rw [Finset.sum_add_distrib]
  have e1 : ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v (j - 1)
      = (stdAddChar (-k) : ℂ) * ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 15)) _ _ (fun x => ?_)
    simp only [Equiv.subRight_apply]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have e2 : ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v (j + 1)
      = (stdAddChar k : ℂ) * ∑ j : ZMod 15, (stdAddChar (-(j * k)) : ℂ) * v j := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 15)) _ _ (fun x => ?_)
    simp only [Equiv.coe_addRight]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [e1, e2]
  ring

/-- The Fourier mode `j ↦ e(jκ)` is an eigenvector of the adjacency matrix. -/
lemma C15adj_mulVec_fourier (κ : ZMod 15) :
    C15adj.mulVec (fun j => (stdAddChar (j * κ) : ℂ))
      = ((stdAddChar κ : ℂ) + (stdAddChar (-κ) : ℂ)) • (fun j => (stdAddChar (j * κ) : ℂ)) := by
  funext i
  rw [C15adj_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul]
  have h1 : ((i - 1) * κ) = (-κ) + i * κ := by ring
  have h2 : ((i + 1) * κ) = κ + i * κ := by ring
  rw [h1, h2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  ring

/-- **Hückel theory for the cycle `C₁₅`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₅` if and only if `μ = 2 cos (2πk/15)` for some
`k ∈ {0, …, 14}`. -/
theorem huckel_C15 (μ : ℂ) :
    (∃ v : ZMod 15 → ℂ, v ≠ 0 ∧ C15adj.mulVec v = μ • v) ↔
      ∃ k : Fin 15, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 15) := by
  constructor
  · rintro ⟨v, hv, hav⟩
    have hdft : ZMod.dft v ≠ 0 := by
      simpa using fun h => hv ((ZMod.dft (E := ℂ)).map_eq_zero_iff.mp h)
    obtain ⟨k, hk⟩ : ∃ k : ZMod 15, ZMod.dft v k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hdft (funext h)
    have key : ((stdAddChar k : ℂ) + (stdAddChar (-k) : ℂ)) * ZMod.dft v k = μ * ZMod.dft v k := by
      rw [← dft_C15adj_mulVec, hav, _root_.map_smul]
      simp
    have hμ : μ = (stdAddChar k : ℂ) + (stdAddChar (-k) : ℂ) :=
      (mul_right_cancel₀ hk key).symm
    refine ⟨⟨k.val, ZMod.val_lt k⟩, ?_⟩
    rw [hμ, stdAddChar_add_neg k]
  · rintro ⟨k, hk⟩
    refine ⟨fun j => (stdAddChar (j * ((k : ℕ) : ZMod 15)) : ℂ), ?_, ?_⟩
    · intro h
      have h0 := congrFun h 0
      simp at h0
    · have hval : ((k : ℕ) : ZMod 15).val = (k : ℕ) :=
        ZMod.val_natCast_of_lt k.isLt
      have := C15adj_mulVec_fourier ((k : ℕ) : ZMod 15)
      rw [this, hk, stdAddChar_add_neg ((k : ℕ) : ZMod 15), hval]

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

