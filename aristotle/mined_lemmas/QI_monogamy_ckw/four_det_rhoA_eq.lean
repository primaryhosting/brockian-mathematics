import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
mandated header block is placed immediately after the single `import Mathlib` line.

## Overview

This file formalises the Coffman–Kundu–Wootters (CKW) monogamy inequality for three qubits:
for a pure state `ψ` of three qubits,

  `τ(A|B) + τ(A|C) ≤ τ(A|BC)`,

where `τ = C²` is the tangle (squared concurrence).

The development is self-contained.  A pure three-qubit state is recorded by its amplitude
array `ψ : Fin 2 → Fin 2 → Fin 2 → ℂ`.

*  `QI.rhoA ψ` is the one-qubit reduced density matrix on `A`, and
   `QI.tangleABC ψ = 4 · det (ρ_A)` is the tangle of the bipartition `A|BC`
   (`C²_{A|BC} = 2(1 - tr ρ_A²) = 4 det ρ_A` for a `2 × 2` density matrix).

*  The two-qubit reduced state `ρ_AB = tr_C |ψ⟩⟨ψ|` has rank at most two: it is
   `|u₀⟩⟨u₀| + |u₁⟩⟨u₁|` with `(u_k)_{ij} = ψ i j k`.  Writing `Y = σ_y ⊗ σ_y` and
   `S_{kl} = u_kᵀ Y u_l`, the nonzero spectrum of `ρ_AB ρ̃_AB` (with `ρ̃ = Y ρ* Y` the
   spin flip) coincides with the spectrum of `S̄ S`, i.e. with the squared singular values
   `σ₁², σ₂²` of the symmetric matrix `S`.  Wootters' formula for a rank-two state therefore
   gives `C_AB = σ₁ - σ₂`, hence
     `τ_AB = C²_AB = σ₁² + σ₂² - 2σ₁σ₂ = ‖S‖²_F - 2|det S|`,
   using `σ₁² + σ₂² = ‖S‖²_F` and `σ₁σ₂ = |det S|`.  This closed formula is taken as the
   definition of `QI.tangleAB` (and symmetrically `QI.tangleAC`); it is well posed because
   `‖S‖²_F ≥ 2|det S|` always (`QI.two_norm_det_le_frob`).

*  The heart of the proof is the polynomial identity (`QI.four_det_rhoA_eq`)
     `4 · det ρ_A = ‖S_AB‖²_F + ‖S_AC‖²_F`,
   from which CKW is immediate, and which refines to the exact CKW identity
     `τ_{A|BC} = τ_AB + τ_AC + τ_ABC`
   with residual three-tangle `τ_ABC = 2|det S_AB| + 2|det S_AC| = 4 |Det ψ|`,
   `Det` being Cayley's hyperdeterminant (`QI.det_SAB_eq_neg_cayley`).
-/

open scoped BigOperators

namespace QI

/-- Amplitude array of a pure state of three qubits: `ψ i j k` is the coefficient of
`|i⟩ ⊗ |j⟩ ⊗ |k⟩`. -/
abbrev QState := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Normalisation of a three-qubit amplitude array. -/

theorem four_det_rhoA_eq (psi : QState) :
    4 * (rhoA psi).det = ((frob (SAB psi) + frob (SAC psi) : ℝ) : ℂ) := by
  simp only [rhoA, SAB, SAC, frob, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two,
    Complex.ofReal_add, ← Complex.mul_conj, map_add, map_sub, map_neg, map_mul]
  ring

/-- Real form of the key identity: `τ_{A|BC} = ‖S_AB‖²_F + ‖S_AC‖²_F`. -/
