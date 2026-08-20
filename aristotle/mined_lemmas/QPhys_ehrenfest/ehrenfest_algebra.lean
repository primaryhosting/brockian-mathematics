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
