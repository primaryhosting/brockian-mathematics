/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring, so the header above is a plain
-- block comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Coffman–Kundu–Wootters monogamy inequality for three qubits

A pure state of three qubits `A`, `B`, `C` is described by its amplitude tensor
`ψ : Fin 2 → Fin 2 → Fin 2 → ℂ`, `ψ i j k` being the coefficient of `|i j k⟩`.

* The **tangle across the `A|BC` cut** is `τ_{A|BC} = 4 · det ρ_A`, where `ρ_A` is the
  reduced density matrix of qubit `A`.  (For a pure state this is the squared concurrence
  of the bipartite cut.)

* For the reduced two–qubit state `ρ_AB = Tr_C |ψ⟩⟨ψ|` Wootters' concurrence is computed
  from the *spin–flip* bilinear form.  Since `ρ_AB = Σ_k |v_k⟩⟨v_k|` with the (unnormalised)
  vectors `(v_k)_{ij} = ψ i j k` indexed by the traced-out qubit `C`, the square roots of the
  eigenvalues of `ρ_AB ρ̃_AB` are the singular values `s₁ ≥ s₂` of the complex symmetric `2 × 2`
  matrix
    `T_{kl} = Σ_{i i' j j'} (σ_y)_{i i'} (σ_y)_{j j'} ψ i j k * ψ i' j' l`,
  and Wootters' formula gives `C(ρ_AB) = s₁ - s₂` (the state has rank ≤ 2, so no truncation
  at `0` occurs).  Consequently
    `C(ρ_AB)² = s₁² + s₂² - 2 s₁ s₂ = ‖T‖_F² - 2 |det T|`,
  which is the closed formula used below as the definition of `concSqAB`; `concSqAC` is the
  same expression for the pair `A, C` (tracing out `B`).  The lemma
  `QI.concSq_eq_singular_value_diff_sq` re-derives the singular-value form `(s₁ - s₂)²`
  from this formula, and `QI.concSqAB_of_product` checks it against the pure-state
  concurrence on states of the form `|χ⟩_{AB} ⊗ |φ⟩_C`.

The main results are

* `QI.tangleA_eq_frob_add_frob` : `4 det ρ_A = ‖T^{AB}‖_F² + ‖T^{AC}‖_F²`;
* `QI.monogamy_ckw`            : `C(ρ_AB)² + C(ρ_AC)² ≤ τ_{A|BC}`  (the CKW inequality);
* `QI.ckw_exact`               : the sharpened identity
  `τ_{A|BC} = C(ρ_AB)² + C(ρ_AC)² + τ₃` with the residual three-tangle `τ₃ = 4 |det T^{AB}| ≥ 0`.

All quantities are homogeneous of degree `4` in `(ψ, ψ̄)`, so the results are stated (and proved)
without a normalisation assumption; the physically meaningful case `Σ |ψ i j k|² = 1` is
recorded separately in `QI.monogamy_ckw_normalized`.
-/

namespace QI

open Complex ComplexConjugate Finset

/-- Amplitude tensor of a pure three-qubit state. -/
abbrev State3 : Type := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The Pauli matrix `σ_y`. -/

theorem tangle3_nonneg (ψ : State3) : 0 ≤ tangle3 ψ := by
  have : (0:ℝ) ≤ ‖det2 (tAB ψ)‖ := norm_nonneg _
  simp only [tangle3]
  linarith

/-! ### Sanity checks -/

/-- The squared concurrence, as defined here, is the square of the difference of the two
singular values of the spin-flip matrix. -/
