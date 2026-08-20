/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
## The Coffman–Kundu–Wootters monogamy inequality for three qubits

A pure state of three qubits `A`, `B`, `C` is given by its amplitudes
`ψ i j k` (`i` the `A`-index, `j` the `B`-index, `k` the `C`-index).

* The *tangle* of the bipartition `A|BC` is `τ_{A(BC)} = 4 · det ρ_A`
  (equivalently `2(1 - Tr ρ_A²)` for a normalized state, see `QI.tangleA_eq_purity`).
* The two-qubit tangles `τ_{AB}`, `τ_{AC}` are the squared Wootters concurrences of the
  reduced states `ρ_{AB} = Tr_C |ψ⟩⟨ψ|` and `ρ_{AC} = Tr_B |ψ⟩⟨ψ|`.  Both reduced states
  have rank at most two, so their Wootters concurrence is `max (0, s₁ - s₂)` where
  `s₁ ≥ s₂ ≥ 0` are the singular values of the symmetric `2 × 2` matrix
  `S_{kl} = ⟨χ_k| σ_y ⊗ σ_y |χ_l^*⟩` built from the (unnormalized) conditional states
  `|χ_k⟩ = ⟨k|_C ψ`.  Since `s₁² + s₂² = ‖S‖_F²` and `s₁ s₂ = |det S|`, this gives
  `τ_{AB} = ‖S‖_F² - 2 |det S|`, which is the formula we take as the definition
  (`QI.tangleAB`, `QI.tangleAC`); the lemma `QI.tangle_of_singular_values` records that this
  is indeed `(s₁ - s₂)²`.
* The residual three-tangle is `τ_{ABC} = 4 |det S|` (four times the modulus of Cayley's
  hyperdeterminant), `QI.tangle3`.

The main results are the exact CKW identity `QI.ckw_identity`
`τ_{A(BC)} = τ_{AB} + τ_{AC} + τ_{ABC}` and the monogamy inequality
`QI.monogamy_ckw` : `τ_{AB} + τ_{AC} ≤ τ_{A(BC)}`.
-/

namespace QI

open Complex Matrix

/-- Amplitudes of a (not necessarily normalized) pure state of three qubits:
`ψ i j k` with `i` the `A`-index, `j` the `B`-index and `k` the `C`-index. -/
abbrev Amp := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The reduced density matrix of qubit `A`, `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`. -/

theorem two_norm_det_le_fro (S : Matrix (Fin 2) (Fin 2) ℂ) : 2 * ‖S.det‖ ≤ fro S := by
  have h : ‖S.det‖ ≤ ‖S 0 0‖ * ‖S 1 1‖ + ‖S 0 1‖ * ‖S 1 0‖ := by
    rw [Matrix.det_fin_two]
    calc ‖S 0 0 * S 1 1 - S 0 1 * S 1 0‖ ≤ ‖S 0 0 * S 1 1‖ + ‖S 0 1 * S 1 0‖ :=
          norm_sub_le _ _
      _ = _ := by rw [norm_mul, norm_mul]
  have e : fro S = ‖S 0 0‖ ^ 2 + ‖S 0 1‖ ^ 2 + ‖S 1 0‖ ^ 2 + ‖S 1 1‖ ^ 2 := by
    simp [fro, Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
    ring
  nlinarith [sq_nonneg (‖S 0 0‖ - ‖S 1 1‖), sq_nonneg (‖S 0 1‖ - ‖S 1 0‖)]

/-- The two-qubit tangles are nonnegative. -/
