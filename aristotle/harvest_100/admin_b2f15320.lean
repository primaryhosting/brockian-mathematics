import Mathlib
/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands of a
file, so the mandated header comment is placed immediately after the single `import Mathlib`
line; its text is reproduced verbatim.
-/

namespace QPhys

open Finset

/-- The expectation value `⟨ψ| M |ψ⟩ = ∑ i j, conj (ψ i) * M i j * ψ j` of a (matrix)
observable `M` in the state `ψ`. -/
noncomputable def expect {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * M i j * v j

lemma expect_sub {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect (M - N) v = expect M v - expect N v := by
  simp only [expect, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Expectation value of a product, written as a triple sum. -/
lemma expect_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect (M * N) v = ∑ i, ∑ j, ∑ k, star (v i) * (M i k * N k j) * v j := by
  simp only [expect, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]

private lemma sum3_inner {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ i, ∑ k, ∑ j, f i j k :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma sum3_perm {n : ℕ} (f : Fin n → Fin n → Fin n → ℂ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k := by
  rw [sum3_inner f, Finset.sum_comm, sum3_inner fun k i j => f i j k]

lemma mulVec_apply_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i : Fin n) :
    M.mulVec v i = ∑ k, M i k * v k := rfl

/-- For a hermitian `H`, `conj ((H v) i) = ∑ k, H k i * conj (v k)`. -/
lemma star_mulVec_apply {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.IsHermitian)
    (v : Fin n → ℂ) (i : Fin n) :
    star (H.mulVec v i) = ∑ k, H k i * star (v k) := by
  rw [mulVec_apply_eq, star_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [star_mul', hH.apply k i]

/-- **Ehrenfest's theorem** (finite-dimensional form).

If the state `psi : ℝ → (Fin n → ℂ)` obeys the Schrödinger equation
`i ℏ ∂ₜ ψ = H ψ`, i.e. `∂ₜ ψ = -(i/ℏ) H ψ`, with hermitian Hamiltonian `H`, and
`A : ℝ → Matrix (Fin n) (Fin n) ℂ` is a time-dependent observable with time derivative
`dA`, then the expectation value `⟨A⟩ (t) = ⟨ψ t| A t |ψ t⟩` is differentiable in `t` with

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest {n : ℕ} (hbar : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (psi : ℝ → Fin n → ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hpsi : ∀ t i, HasDerivAt (fun s => psi s i)
      (-(Complex.I / (hbar : ℂ)) * H.mulVec (psi t) i) t)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (dA t i j) t)
    (t : ℝ) :
    HasDerivAt (fun s => expect (A s) (psi s))
      ((Complex.I / (hbar : ℂ)) * expect (H * A t - A t * H) (psi t)
        + expect (dA t) (psi t)) t := by
  set c : ℂ := Complex.I / (hbar : ℂ) with hc
  have hcs : star c = -c := by
    rw [hc]; simp [div_eq_mul_inv]
  -- derivatives of the individual factors
  have hstar : ∀ i, HasDerivAt (fun s => star (psi s i))
      (star (-c * H.mulVec (psi t) i)) t := fun i => (hpsi t i).star
  have hterm : ∀ i ∈ (univ : Finset (Fin n)), ∀ j ∈ (univ : Finset (Fin n)),
      HasDerivAt (fun s => star (psi s i) * A s i j * psi s j)
        (star (-c * H.mulVec (psi t) i) * A t i j * psi t j
          + star (psi t i) * dA t i j * psi t j
          + star (psi t i) * A t i j * (-c * H.mulVec (psi t) j)) t := by
    intro i _ j _
    have h1 := ((hstar i).mul (hA t i j)).mul (hpsi t j)
    simp only [Pi.mul_apply] at h1
    convert h1 using 1
    ring
  have hexp : (fun s => expect (A s) (psi s))
      = ∑ i : Fin n, ∑ j : Fin n, fun s => star (psi s i) * A s i j * psi s j := by
    funext s
    simp only [Finset.sum_apply, expect]
  rw [hexp]
  refine (HasDerivAt.sum fun i hi => HasDerivAt.sum fun j hj => hterm i hi j hj).congr_deriv ?_
  -- the algebraic identity
  have hstar' : ∀ i, star (-c * H.mulVec (psi t) i) = c * ∑ k, H k i * star (psi t k) := by
    intro i
    rw [star_mul', star_neg, star_mulVec_apply hH, hcs]
    ring
  simp only [hstar', Finset.sum_add_distrib]
  -- the middle sum is ⟨∂A/∂t⟩
  have hmid : ∑ i, ∑ j, star (psi t i) * dA t i j * psi t j = expect (dA t) (psi t) := rfl
  -- the first sum is (i/ℏ) ⟨H A⟩
  have hfirst : ∑ i, ∑ j, (c * ∑ k, H k i * star (psi t k)) * A t i j * psi t j
      = c * expect (H * A t) (psi t) := by
    have hL : ∑ i, ∑ j, (c * ∑ k, H k i * star (psi t k)) * A t i j * psi t j
        = ∑ i, ∑ j, ∑ k, c * (star (psi t k) * (H k i * A t i j) * psi t j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hR : c * expect (H * A t) (psi t)
        = ∑ i, ∑ j, ∑ k, c * (star (psi t i) * (H i k * A t k j) * psi t j) := by
      rw [expect_mul]
      simp only [Finset.mul_sum]
    rw [hL, hR]
    exact sum3_perm _
  -- the third sum is -(i/ℏ) ⟨A H⟩
  have hthird : ∑ i, ∑ j, star (psi t i) * A t i j * (-c * H.mulVec (psi t) j)
      = -(c * expect (A t * H) (psi t)) := by
    have hL : ∑ i, ∑ j, star (psi t i) * A t i j * (-c * H.mulVec (psi t) j)
        = ∑ i, ∑ j, ∑ k, -(c * (star (psi t i) * (A t i j * H j k) * psi t k)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_apply_eq]
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have hR : -(c * expect (A t * H) (psi t))
        = ∑ i, ∑ j, ∑ k, -(c * (star (psi t i) * (A t i k * H k j) * psi t j)) := by
      rw [expect_mul]
      simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [hL, hR]
    exact sum3_inner _
  rw [hfirst, hmid, hthird, expect_sub]
  ring

/-- Ehrenfest's theorem stated with `deriv`:
`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest_deriv {n : ℕ} (hbar : ℝ)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (psi : ℝ → Fin n → ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (hpsi : ∀ t i, HasDerivAt (fun s => psi s i)
      (-(Complex.I / (hbar : ℂ)) * H.mulVec (psi t) i) t)
    (hA : ∀ t i j, HasDerivAt (fun s => A s i j) (dA t i j) t)
    (t : ℝ) :
    deriv (fun s => expect (A s) (psi s)) t
      = (Complex.I / (hbar : ℂ)) * expect (H * A t - A t * H) (psi t)
        + expect (dA t) (psi t) :=
  (ehrenfest hbar H hH psi A dA hpsi hA t).deriv

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

