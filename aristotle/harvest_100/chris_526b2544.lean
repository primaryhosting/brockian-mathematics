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
-/

open Finset Complex Matrix

namespace QPhys

variable {n : ℕ}

/-- The expectation value `⟨v, M v⟩` of the (matrix) observable `M` in the state `v`. -/
noncomputable def expect (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * M i j * v j

lemma expect_eq_dotProduct (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) :
    expect M v = star v ⬝ᵥ (M *ᵥ v) := by
  simp [expect, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private lemma hasDerivAt_finsum {f : Fin n → ℝ → ℂ} {f' : Fin n → ℂ} {t : ℝ}
    (h : ∀ i, HasDerivAt (f i) (f' i) t) : HasDerivAt (fun s => ∑ i, f i s) (∑ i, f' i) t := by
  have e : (fun s => ∑ i, f i s) = ∑ i, f i := by funext s; simp
  rw [e]
  exact HasDerivAt.sum (fun i _ => h i)

/-- The algebraic core of Ehrenfest's theorem: the three terms coming from the product rule
recombine into the commutator term plus the explicit time-derivative term. -/
lemma ehrenfest_algebra (hbar : ℝ) (psi : Fin n → ℂ)
    (H A dA : Matrix (Fin n) (Fin n) ℂ) (hH : H.IsHermitian) :
    ∑ i, ∑ j, (star (-(I / hbar) * (H *ᵥ psi) i) * A i j * psi j
        + star (psi i) * dA i j * psi j
        + star (psi i) * A i j * (-(I / hbar) * (H *ᵥ psi) j))
      = (I / hbar) * expect (H * A - A * H) psi + expect dA psi := by
  have dp : ∀ (u v : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ),
      ∑ i, ∑ j, u i * M i j * v j = u ⬝ᵥ (M *ᵥ v) := by
    intro u v M; simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : star (-(I / (hbar : ℂ))) = I / hbar := by simp [neg_div]
  have hstarw : star (H *ᵥ psi) = star psi ᵥ* H := by rw [Matrix.star_mulVec, hH.eq]
  have hu : (fun i => star (-(I / (hbar : ℂ)) * (H *ᵥ psi) i))
      = (I / (hbar : ℂ)) • (star psi ᵥ* H) := by
    funext i
    have hi : star ((H *ᵥ psi) i) = (star psi ᵥ* H) i := by rw [← hstarw]; rfl
    rw [star_mul', hc, hi]; rfl
  have hv : (fun j => -(I / (hbar : ℂ)) * (H *ᵥ psi) j) = (-(I / (hbar : ℂ))) • (H *ᵥ psi) := rfl
  have hsp : (fun i : Fin n => star (psi i)) = star psi := rfl
  have split : (∑ i, ∑ j, (star (-(I / (hbar : ℂ)) * (H *ᵥ psi) i) * A i j * psi j
        + star (psi i) * dA i j * psi j
        + star (psi i) * A i j * (-(I / (hbar : ℂ)) * (H *ᵥ psi) j)))
      = (∑ i, ∑ j, star (-(I / (hbar : ℂ)) * (H *ᵥ psi) i) * A i j * psi j)
        + (∑ i, ∑ j, star (psi i) * dA i j * psi j)
        + (∑ i, ∑ j, star (psi i) * A i j * (-(I / (hbar : ℂ)) * (H *ᵥ psi) j)) := by
    simp [Finset.sum_add_distrib]
  rw [split, dp (fun i => star (-(I / (hbar : ℂ)) * (H *ᵥ psi) i)) psi A,
      dp (fun i => star (psi i)) psi dA,
      dp (fun i => star (psi i)) (fun j => -(I / (hbar : ℂ)) * (H *ᵥ psi) j) A,
      hu, hv, hsp, expect_eq_dotProduct, expect_eq_dotProduct,
      smul_dotProduct, mulVec_smul, dotProduct_smul, sub_mulVec, dotProduct_sub,
      ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  simp only [smul_eq_mul]
  ring

/-- **Ehrenfest's theorem**.  If the state `psi` evolves according to the Schrödinger equation
`ψ' = -(i/ℏ) H ψ` with a Hermitian Hamiltonian `H`, and the observable `A` depends on time with
time derivative `dA`, then

`d⟨A⟩/dt = (i/ℏ) ⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem ehrenfest (hbar : ℝ) (psi : ℝ → (Fin n → ℂ))
    (H : Matrix (Fin n) (Fin n) ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hH : H.IsHermitian)
    (hsch : ∀ i, HasDerivAt (fun s => psi s i) (-(I / hbar) * (H *ᵥ psi t) i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t) :
    HasDerivAt (fun s => expect (A s) (psi s))
      ((I / hbar) * expect (H * A t - A t * H) (psi t) + expect (dA t) (psi t)) t := by
  have key : ∀ i j, HasDerivAt (fun s => star (psi s i) * A s i j * psi s j)
      (star (-(I / hbar) * (H *ᵥ psi t) i) * A t i j * psi t j
        + star (psi t i) * dA t i j * psi t j
        + star (psi t i) * A t i j * (-(I / hbar) * (H *ᵥ psi t) j)) t := by
    intro i j
    have h2 := (((hsch i).star.mul (hA i j)).mul (hsch j))
    convert h2 using 1
    simp only [Pi.mul_apply]
    ring
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, star (psi s i) * A s i j * psi s j)
      (∑ i, ∑ j, (star (-(I / hbar) * (H *ᵥ psi t) i) * A t i j * psi t j
        + star (psi t i) * dA t i j * psi t j
        + star (psi t i) * A t i j * (-(I / hbar) * (H *ᵥ psi t) j))) t :=
    hasDerivAt_finsum (fun i => hasDerivAt_finsum (fun j => key i j))
  rw [← ehrenfest_algebra hbar (psi t) H (A t) (dA t) hH]
  exact hsum

/-- Ehrenfest's theorem in Leibniz form: `d⟨A⟩/dt = (i/ℏ)⟨[H, A]⟩ + ⟨∂A/∂t⟩`. -/
theorem deriv_expect (hbar : ℝ) (psi : ℝ → (Fin n → ℂ))
    (H : Matrix (Fin n) (Fin n) ℂ) (A dA : ℝ → Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hH : H.IsHermitian)
    (hsch : ∀ i, HasDerivAt (fun s => psi s i) (-(I / hbar) * (H *ᵥ psi t) i) t)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (dA t i j) t) :
    deriv (fun s => expect (A s) (psi s)) t
      = (I / hbar) * expect (H * A t - A t * H) (psi t) + expect (dA t) (psi t) :=
  (ehrenfest hbar psi H A dA t hH hsch hA).deriv

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

