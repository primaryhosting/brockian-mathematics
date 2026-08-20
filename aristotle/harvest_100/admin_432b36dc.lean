/-
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ehrenfest
Category: Quantum Physics
Target: QPhys.ehrenfest
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

We formalise the Ehrenfest theorem for a finite-dimensional quantum system
(state space `Fin n → ℂ`, observables given by matrices).

If `ψ : ℝ → (Fin n → ℂ)` solves the Schrödinger equation `iℏ ψ'(t) = H ψ(t)`
with `H` Hermitian, and `A : ℝ → Matrix (Fin n) (Fin n) ℂ` is a (possibly time
dependent) observable, then the expectation value `⟪ψ, A ψ⟫` satisfies

  d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩ .
-/

namespace QPhys

open Matrix

variable {n : ℕ}

/-- The expectation value `⟪v, A v⟫ = ∑ i, ∑ j, conj (v i) * A i j * v j`
of the observable `A` in the state `v`. -/
noncomputable def expect (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  star v ⬝ᵥ (A *ᵥ v)

lemma expect_eq_sum (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect A v = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * A i j * v j := by
  simp [expect, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

/-- The commutator `[H, A] = H A - A H`. -/
noncomputable def commutator (H A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  H * A - A * H

/-- **Product rule** for the expectation value: the derivative of
`t ↦ ⟪ψ t, A t (ψ t)⟫` is the sum of the three obvious terms. -/
lemma hasDerivAt_expect (psi : ℝ → Fin n → ℂ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (dpsi : Fin n → ℂ) (dA : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hpsi : ∀ i, HasDerivAt (fun s => psi s i) (dpsi i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA i j) t) :
    HasDerivAt (fun s => expect (A s) (psi s))
      (star dpsi ⬝ᵥ (A t *ᵥ psi t) + star (psi t) ⬝ᵥ (dA *ᵥ psi t)
        + star (psi t) ⬝ᵥ (A t *ᵥ dpsi)) t := by
  have key : ∀ i, HasDerivAt (fun s => ∑ j, (starRingEnd ℂ) (psi s i) * A s i j * psi s j)
      (∑ j, ((starRingEnd ℂ) (dpsi i) * A t i j * psi t j
        + (starRingEnd ℂ) (psi t i) * dA i j * psi t j
        + (starRingEnd ℂ) (psi t i) * A t i j * dpsi j)) t := by
    intro i
    apply HasDerivAt.fun_sum
    intro j _
    have h1 : HasDerivAt (fun s => (starRingEnd ℂ) (psi s i)) ((starRingEnd ℂ) (dpsi i)) t := by
      simpa [Complex.star_def] using (hpsi i).star
    have := ((h1.mul (hA i j)).mul (hpsi j))
    convert this using 1
    simp only [Pi.mul_apply]
    ring
  have hsum := HasDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => key i)
  simp only [expect_eq_sum]
  convert hsum using 1
  simp only [Finset.sum_add_distrib, dotProduct, mulVec, Finset.mul_sum, mul_assoc,
    Complex.star_def, Pi.star_apply]

/-- **Ehrenfest's theorem** (finite-dimensional form).

If `ψ` solves the Schrödinger equation `i ℏ ψ'(t) = H ψ(t)` at time `t`, with `H`
Hermitian and `ℏ ≠ 0`, and `A` is a time-dependent observable with derivative `dA`
at `t`, then

  `d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest (hbar : ℝ) (hbar_ne : hbar ≠ 0)
    (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian)
    (psi : ℝ → Fin n → ℂ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (dpsi : Fin n → ℂ) (dA : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hpsi : ∀ i, HasDerivAt (fun s => psi s i) (dpsi i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA i j) t)
    (hSch : (Complex.I * hbar) • dpsi = H *ᵥ psi t) :
    HasDerivAt (fun s => expect (A s) (psi s))
      ((Complex.I / hbar) * expect (commutator H (A t)) (psi t) + expect dA (psi t)) t := by
  have h0 : (hbar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hbar_ne
  have hdpsi : dpsi = ((-Complex.I) / hbar) • (H *ᵥ psi t) := by
    rw [← hSch, smul_smul]
    have : (-Complex.I) / (hbar : ℂ) * (Complex.I * (hbar : ℂ)) = 1 := by
      field_simp
      ring_nf
      simp [Complex.I_sq]
    rw [this, one_smul]
  have hstar : star dpsi = (Complex.I / hbar) • (star (psi t) ᵥ* H) := by
    rw [hdpsi]
    rw [star_smul, Matrix.star_mulVec, hH]
    congr 1
    simp [div_eq_mul_inv, ← Complex.ofReal_inv]
  have main := hasDerivAt_expect psi A dpsi dA t hpsi hA
  convert main using 1
  rw [hstar, hdpsi]
  simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, expect, commutator,
    Matrix.sub_mulVec, dotProduct_sub]
  ring

#print axioms QPhys.ehrenfest

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

