/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Monogamy of entanglement: the Coffman–Kundu–Wootters inequality

For a pure state `|ψ⟩` of three qubits `A`, `B`, `C` with amplitudes
`a i j k = ⟨ijk|ψ⟩`, the CKW inequality states

`C²(A,B) + C²(A,C) ≤ τ(A|BC)`,

where `C(A,B)`, `C(A,C)` are Wootters' concurrences of the two–qubit reduced
states `ρ_AB`, `ρ_AC`, and `τ(A|BC) = C²(A|BC) = 4 det ρ_A` is the tangle of
qubit `A` against the pair `BC`.

### How the quantities are expressed here

*The tangle* `τ(A|BC)` is `4 · det ρ_A`, with `ρ_A` the reduced density matrix
of qubit `A` (`QI.rhoA`, `QI.tangleA`).

*The two–qubit concurrences.*  Tracing out qubit `C` decomposes the reduced
state as `ρ_AB = Σ_k |w_k⟩⟨w_k|` with the (unnormalised) vectors
`(w_k)_{ij} = a i j k`.  Wootters' theory expresses the concurrence of a state
given by such a decomposition through the symmetric matrix
`T_{kl} = w_kᵀ (σ_y ⊗ σ_y) w_l`: the square roots `λ₁ ≥ λ₂ ≥ …` of the
eigenvalues of `ρ ρ̃` are exactly the singular values `s₁ ≥ s₂` of `T`
(all further ones vanish, `ρ_AB` having rank at most two), so

`C(A,B) = max (0, λ₁ - λ₂ - λ₃ - λ₄) = s₁ - s₂`, hence
`C²(A,B) = s₁² + s₂² - 2 s₁ s₂ = ‖T‖_F² - 2 |det T|`.

Accordingly `QI.concSq` computes `‖T‖_F² - 2|det T|` and the two concurrences
squared are `QI.concSqAB` and `QI.concSqAC`, built from the matrices `QI.TAB`
and `QI.TAC`.  The bridge back to the density matrix is recorded in
`QI.trace_rhoAB_spinFlip` (`tr (ρ_AB ρ̃_AB) = ‖T‖_F² = λ₁² + λ₂²`) and
`QI.trace_rhoAC_spinFlip`.

### The proof

Everything follows from one polynomial identity in the amplitudes
(`QI.frobenius_add_frobenius_eq_tangle`):

`‖T_AB‖_F² + ‖T_AC‖_F² = 4 det ρ_A`,

together with `det T_AB = det T_AC` (`QI.det_TAB_eq_det_TAC`), whose modulus is
a quarter of the residual three–tangle.  This yields the CKW *equality*
`C²(A,B) + C²(A,C) + τ₃ = τ(A|BC)` (`QI.ckw_equality`) and hence the
inequality, since `τ₃ ≥ 0`.

No normalisation of the amplitudes is needed: every quantity involved is
homogeneous of bidegree `(2,2)` in `(a, ā)`, so the statements hold verbatim
for normalised states.
-/

namespace QI

open Complex Matrix

/-- Amplitudes `a i j k = ⟨ijk|ψ⟩` of a three–qubit state. -/
abbrev Amp : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`. -/

theorem frobenius_add_frobenius_eq_tangle (a : Amp) :
    frob (TAB a) + frob (TAC a) = tangleA a := by
  rw [tangleA_eq]
  simp only [frob, TAB, TAC, Matrix.of_apply]
  simp [Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im]
  ring

/-- The two Wootters matrices have the same determinant; its modulus is a
quarter of the three–tangle (this is the permutation invariance of the residual
tangle). -/
