/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open ComplexConjugate Finset

variable {n : ℕ}

/-- The expectation value `⟨A⟩ = ⟪ψ, A ψ⟫` of an observable `A` (given as a matrix)
in the state `ψ` (a vector of `ℂ^n`). -/
noncomputable def expect (v : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i, ∑ j, conj (v i) * (M i j * v j)

/-- The commutator `[H, A] = H A - A H` of two matrices. -/
noncomputable def commMat (H A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H * A - A * H

private lemma sum3_swap13 (F : Fin n → Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, ∑ k, F i j k = ∑ k, ∑ j, ∑ i, F i j k := by
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ j, ∑ i, ∑ k, F i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, F i j k := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k, ∑ j, ∑ i, F i j k := Finset.sum_comm

/-- Product rule for the expectation value of a time-dependent observable in a
time-dependent state. -/
lemma hasDerivAt_expect
    (ψ dψ : ℝ → Fin n → ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hψ : ∀ i, HasDerivAt (fun s => ψ s i) (dψ t i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t) :
    HasDerivAt (fun s => expect (ψ s) (A s))
      (∑ i, ∑ j, (conj (dψ t i) * (A t i j * ψ t j)
        + conj (ψ t i) * (dA t i j * ψ t j)
        + conj (ψ t i) * (A t i j * dψ t j))) t := by
  have hfun : (fun s => expect (ψ s) (A s))
      = fun s => ∑ i, ∑ j, conj (ψ s i) * (A s i j * ψ s j) := rfl
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro j _
  have h1 : HasDerivAt (fun s => conj (ψ s i)) (conj (dψ t i)) t := by
    simpa using HasDerivAt.star (𝕜 := ℝ) (F := ℂ) (hψ i)
  have h2 : HasDerivAt (fun s => A s i j * ψ s j)
      (dA t i j * ψ t j + A t i j * dψ t j) t := (hA i j).fun_mul (hψ j)
  exact (h1.fun_mul h2).congr_deriv (by ring)

/-- **Ehrenfest's theorem** (finite-dimensional form).

If the state `ψ : ℝ → ℂ^n` solves the Schrödinger equation `i ℏ ψ' = H ψ` with hermitian
Hamiltonian `H`, and `A : ℝ → Matrix` is a (possibly time-dependent) observable with time
derivative `dA`, then the expectation value `⟨A⟩` satisfies

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest
    (ℏ : ℝ) (hℏ : ℏ ≠ 0)
    (ψ dψ : ℝ → Fin n → ℂ) (H : Matrix (Fin n) (Fin n) ℂ)
    (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hψ : ∀ i, HasDerivAt (fun s => ψ s i) (dψ t i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t)
    (hH : H.IsHermitian)
    (hSch : ∀ i, (Complex.I * ℏ) * dψ t i = ∑ j, H i j * ψ t j) :
    HasDerivAt (fun s => expect (ψ s) (A s))
      ((Complex.I / ℏ) * expect (ψ t) (commMat H (A t)) + expect (ψ t) (dA t)) t := by
  have key := hasDerivAt_expect ψ dψ A dA t hψ hA
  refine key.congr_deriv ?_
  have hc : (ℏ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hℏ
  -- explicit formula for the time derivative of the state
  have hd : ∀ i, dψ t i = (-Complex.I / ℏ) * ∑ j, H i j * ψ t j := by
    intro i
    have hcancel : (-Complex.I / (ℏ : ℂ)) * ((Complex.I * ℏ) * dψ t i) = dψ t i := by
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [← hSch i, hcancel]
  -- and of its complex conjugate, using hermiticity of `H`
  have hdc : ∀ i, conj (dψ t i) = (Complex.I / ℏ) * ∑ j, H j i * conj (ψ t j) := by
    intro i
    rw [hd i, map_mul, map_sum]
    have hcj : conj (-Complex.I / (ℏ : ℂ)) = Complex.I / (ℏ : ℂ) := by
      simp [div_eq_mul_inv]
    rw [hcj]
    refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
    rw [map_mul, ← Complex.star_def, hH.apply j i]
  -- the term coming from `dψ` on the left of the inner product
  have S1 : ∑ i, ∑ j, conj (dψ t i) * (A t i j * ψ t j)
      = (Complex.I / ℏ) * ∑ i, ∑ j, conj (ψ t i) * ((H * A t) i j * ψ t j) := by
    have e1 : ∀ i j, conj (dψ t i) * (A t i j * ψ t j)
        = ∑ k, ((Complex.I / (ℏ : ℂ)) * (H k i * conj (ψ t k))) * (A t i j * ψ t j) := by
      intro i j
      rw [hdc i, Finset.mul_sum, Finset.sum_mul]
    simp only [e1]
    rw [sum3_swap13 (fun i j k =>
      ((Complex.I / (ℏ : ℂ)) * (H k i * conj (ψ t k))) * (A t i j * ψ t j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  -- the term coming from `dψ` on the right of the inner product
  have S3 : ∑ i, ∑ j, conj (ψ t i) * (A t i j * dψ t j)
      = -(Complex.I / ℏ) * ∑ i, ∑ j, conj (ψ t i) * ((A t * H) i j * ψ t j) := by
    have e3 : ∀ i j, conj (ψ t i) * (A t i j * dψ t j)
        = ∑ k, conj (ψ t i) * (A t i j * ((-Complex.I / (ℏ : ℂ)) * (H j k * ψ t k))) := by
      intro i j
      rw [hd j, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    simp only [e3]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have expand : ∑ i, ∑ j, (conj (dψ t i) * (A t i j * ψ t j)
        + conj (ψ t i) * (dA t i j * ψ t j)
        + conj (ψ t i) * (A t i j * dψ t j))
      = (∑ i, ∑ j, conj (dψ t i) * (A t i j * ψ t j))
        + (∑ i, ∑ j, conj (ψ t i) * (dA t i j * ψ t j))
        + ∑ i, ∑ j, conj (ψ t i) * (A t i j * dψ t j) := by
    simp [Finset.sum_add_distrib]
  have hcomm : expect (ψ t) (commMat H (A t))
      = (∑ i, ∑ j, conj (ψ t i) * ((H * A t) i j * ψ t j))
        - ∑ i, ∑ j, conj (ψ t i) * ((A t * H) i j * ψ t j) := by
    simp [expect, commMat, Matrix.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib]
  rw [expand, S1, S3, hcomm]
  simp only [expect]
  ring

end QPhys

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

