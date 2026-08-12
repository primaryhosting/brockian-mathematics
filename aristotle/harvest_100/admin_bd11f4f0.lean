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

A pure state of three qubits is described by its amplitude array
`a : Fin 2 → Fin 2 → Fin 2 → ℂ`, i.e. `|ψ⟩ = ∑_{i,j,k} a i j k • |i j k⟩`
(the three tensor factors are called `A`, `B`, `C`).

* `QI.rhoA a` is the reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|`.
* `QI.tangleA a = 4 · det ρ_A` is the tangle `τ_{A(BC)}`, i.e. the squared
  concurrence of the pure-state bipartition `A | BC`.
* `QI.concSqAB a` and `QI.concSqAC a` are the squared Wootters concurrences of
  the two-qubit mixed states `ρ_AB = Tr_C |ψ⟩⟨ψ|` and `ρ_AC = Tr_B |ψ⟩⟨ψ|`.

For the squared concurrences we use Wootters' singular-value description.  Since
the traced-out system is a single qubit, `ρ_AB = |u⟩⟨u| + |v⟩⟨v|` with
`u_{ij} = a i j 0` and `v_{ij} = a i j 1`, and the square roots `λ₁ ≥ λ₂ ≥ 0` of
the nonzero eigenvalues of `ρ_AB ρ̃_AB` (with `ρ̃ = (σ_y ⊗ σ_y) ρ* (σ_y ⊗ σ_y)`)
are the singular values of the complex symmetric `2 × 2` matrix
`M = !![p, q; q, r]`, where `p = ⟨u|σ_y⊗σ_y|u*⟩`, `q = ⟨u|σ_y⊗σ_y|v*⟩`,
`r = ⟨v|σ_y⊗σ_y|v*⟩` (up to an irrelevant global sign).  Hence
`C(ρ_AB) = λ₁ - λ₂` and

`C(ρ_AB)² = λ₁² + λ₂² - 2 λ₁ λ₂ = ‖M‖_F² - 2 |det M| = ‖p‖² + 2‖q‖² + ‖r‖² - 2‖p r - q²‖`,

which is the formula taken as the definition of `QI.concSqAB` below (likewise
for `QI.concSqAC`, with the roles of `B` and `C` exchanged).

The main results are the exact residual-tangle identity `QI.residual_tangle_eq`,
`τ_{A(BC)} - C(ρ_AB)² - C(ρ_AC)² = 4 |Hdet a|`, where `Hdet` is Cayley's
hyperdeterminant of the `2 × 2 × 2` amplitude array (`4 |Hdet a|` is the
three-tangle), and the resulting CKW monogamy inequality `QI.monogamy_ckw`.

No normalisation of the state is required: both sides are homogeneous of
degree `4` in the amplitudes.
-/

namespace QI

open Complex Matrix

variable (a : Fin 2 → Fin 2 → Fin 2 → ℂ)

/-- The reduced density matrix `ρ_A = Tr_{BC} |ψ⟩⟨ψ|` of the first qubit. -/
noncomputable def rhoA : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j, ∑ k, a i j k * (starRingEnd ℂ) (a i' j k)

/-- The tangle of the bipartition `A | BC`, i.e. `τ_{A(BC)} = 4 det ρ_A`. -/
noncomputable def tangleA : ℝ := 4 * ((rhoA a).det).re

/-- `p_{AB} = ⟨u|σ_y ⊗ σ_y|u*⟩` for `u_{ij} = a i j 0`. -/
def pAB : ℂ := 2 * (a 0 0 0 * a 1 1 0 - a 0 1 0 * a 1 0 0)

/-- `q_{AB} = ⟨u|σ_y ⊗ σ_y|v*⟩` for `u_{ij} = a i j 0`, `v_{ij} = a i j 1`. -/
def qAB : ℂ := a 0 0 0 * a 1 1 1 + a 1 1 0 * a 0 0 1 - a 0 1 0 * a 1 0 1 - a 1 0 0 * a 0 1 1

/-- `r_{AB} = ⟨v|σ_y ⊗ σ_y|v*⟩` for `v_{ij} = a i j 1`. -/
def rAB : ℂ := 2 * (a 0 0 1 * a 1 1 1 - a 0 1 1 * a 1 0 1)

/-- `p_{AC}`, the analogue of `pAB` with the roles of `B` and `C` exchanged. -/
def pAC : ℂ := 2 * (a 0 0 0 * a 1 0 1 - a 0 0 1 * a 1 0 0)

/-- `q_{AC}`, the analogue of `qAB` with the roles of `B` and `C` exchanged. -/
def qAC : ℂ := a 0 0 0 * a 1 1 1 + a 1 0 1 * a 0 1 0 - a 0 0 1 * a 1 1 0 - a 1 0 0 * a 0 1 1

/-- `r_{AC}`, the analogue of `rAB` with the roles of `B` and `C` exchanged. -/
def rAC : ℂ := 2 * (a 0 1 0 * a 1 1 1 - a 0 1 1 * a 1 1 0)

/-- The squared Wootters concurrence of `ρ_AB = Tr_C |ψ⟩⟨ψ|`. -/
noncomputable def concSqAB : ℝ :=
  ‖pAB a‖ ^ 2 + 2 * ‖qAB a‖ ^ 2 + ‖rAB a‖ ^ 2 - 2 * ‖pAB a * rAB a - qAB a ^ 2‖

/-- The squared Wootters concurrence of `ρ_AC = Tr_B |ψ⟩⟨ψ|`. -/
noncomputable def concSqAC : ℝ :=
  ‖pAC a‖ ^ 2 + 2 * ‖qAC a‖ ^ 2 + ‖rAC a‖ ^ 2 - 2 * ‖pAC a * rAC a - qAC a ^ 2‖

/-- Cayley's hyperdeterminant of the `2 × 2 × 2` amplitude array; `4‖Hdet‖` is
the three-tangle `τ_{ABC}`. -/
def hyperdet : ℂ := qAB a ^ 2 - pAB a * rAB a

/-- The two `2 × 2` Wootters determinants both compute (minus) the
hyperdeterminant. -/
lemma pr_sub_qsq_AB : pAB a * rAB a - qAB a ^ 2 = -hyperdet a := by
  simp only [hyperdet]; ring

lemma pr_sub_qsq_AC : pAC a * rAC a - qAC a ^ 2 = -hyperdet a := by
  simp only [hyperdet, pAB, qAB, rAB, pAC, qAC, rAC]; ring

/-- The key algebraic identity: `4 det ρ_A` equals the sum of the two squared
Frobenius norms of the Wootters matrices of `ρ_AB` and `ρ_AC`. -/
lemma four_det_rhoA :
    4 * (rhoA a).det =
      ((‖pAB a‖ ^ 2 + 2 * ‖qAB a‖ ^ 2 + ‖rAB a‖ ^ 2
        + (‖pAC a‖ ^ 2 + 2 * ‖qAC a‖ ^ 2 + ‖rAC a‖ ^ 2) : ℝ) : ℂ) := by
  have hn : ∀ z : ℂ, ((‖z‖ : ℂ)) ^ 2 = z * (starRingEnd ℂ) z := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.sq_norm z
  push_cast
  rw [hn, hn, hn, hn, hn, hn, Matrix.det_fin_two]
  simp only [rhoA, Matrix.of_apply, pAB, qAB, rAB, pAC, qAC, rAC, Fin.sum_univ_two,
    map_mul, map_sub, map_add, map_ofNat]
  ring

/-- `4 det ρ_A` is a nonnegative real number, and `tangleA` computes it. -/
lemma tangleA_eq :
    tangleA a = ‖pAB a‖ ^ 2 + 2 * ‖qAB a‖ ^ 2 + ‖rAB a‖ ^ 2
      + (‖pAC a‖ ^ 2 + 2 * ‖qAC a‖ ^ 2 + ‖rAC a‖ ^ 2) := by
  have h := congrArg Complex.re (four_det_rhoA a)
  simp only [Complex.ofReal_re] at h
  simpa [tangleA] using h

/-- **Residual tangle (three-tangle) identity.**  For a pure three-qubit state,
`τ_{A(BC)} - C(ρ_AB)² - C(ρ_AC)² = 4 ‖Hdet‖`. -/
theorem residual_tangle_eq :
    tangleA a - concSqAB a - concSqAC a = 4 * ‖hyperdet a‖ := by
  rw [tangleA_eq, concSqAB, concSqAC, pr_sub_qsq_AB, pr_sub_qsq_AC, norm_neg]
  ring

/-- **CKW monogamy inequality.**  For any pure state of three qubits, the squared
concurrences of the two reduced two-qubit states are bounded by the tangle of the
`A | BC` bipartition:  `C(ρ_AB)² + C(ρ_AC)² ≤ τ_{A(BC)}`. -/
theorem monogamy_ckw : concSqAB a + concSqAC a ≤ tangleA a := by
  have h := residual_tangle_eq a
  have h2 : (0:ℝ) ≤ 4 * ‖hyperdet a‖ := by positivity
  linarith

/-- Both squared concurrences are nonnegative. -/
lemma concSqAB_nonneg : 0 ≤ concSqAB a := by
  have h1 : ‖pAB a * rAB a - qAB a ^ 2‖ ≤ ‖pAB a‖ * ‖rAB a‖ + ‖qAB a‖ ^ 2 := by
    calc ‖pAB a * rAB a - qAB a ^ 2‖ ≤ ‖pAB a * rAB a‖ + ‖qAB a ^ 2‖ := norm_sub_le _ _
      _ = ‖pAB a‖ * ‖rAB a‖ + ‖qAB a‖ ^ 2 := by rw [norm_mul, norm_pow]
  have h2 : 2 * (‖pAB a‖ * ‖rAB a‖) ≤ ‖pAB a‖ ^ 2 + ‖rAB a‖ ^ 2 := by nlinarith [sq_nonneg (‖pAB a‖ - ‖rAB a‖)]
  simp only [concSqAB]
  linarith

lemma concSqAC_nonneg : 0 ≤ concSqAC a := by
  have h1 : ‖pAC a * rAC a - qAC a ^ 2‖ ≤ ‖pAC a‖ * ‖rAC a‖ + ‖qAC a‖ ^ 2 := by
    calc ‖pAC a * rAC a - qAC a ^ 2‖ ≤ ‖pAC a * rAC a‖ + ‖qAC a ^ 2‖ := norm_sub_le _ _
      _ = ‖pAC a‖ * ‖rAC a‖ + ‖qAC a‖ ^ 2 := by rw [norm_mul, norm_pow]
  have h2 : 2 * (‖pAC a‖ * ‖rAC a‖) ≤ ‖pAC a‖ ^ 2 + ‖rAC a‖ ^ 2 := by nlinarith [sq_nonneg (‖pAC a‖ - ‖rAC a‖)]
  simp only [concSqAC]
  linarith

/-- The tangle of the `A | BC` bipartition is nonnegative. -/
lemma tangleA_nonneg : 0 ≤ tangleA a := by
  have := concSqAB_nonneg a
  have := concSqAC_nonneg a
  have := monogamy_ckw a
  linarith

/-! ### Sanity checks: the GHZ and W states (unnormalised) -/

/-- The (unnormalised) GHZ state `|000⟩ + |111⟩`. -/
def ghz : Fin 2 → Fin 2 → Fin 2 → ℂ := ![![![1, 0], ![0, 0]], ![![0, 0], ![0, 1]]]

/-- The (unnormalised) W state `|100⟩ + |010⟩ + |001⟩`. -/
def wState : Fin 2 → Fin 2 → Fin 2 → ℂ := ![![![0, 1], ![1, 0]], ![![1, 0], ![0, 0]]]

example : concSqAB ghz = 0 ∧ concSqAC ghz = 0 ∧ tangleA ghz = 4 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp [concSqAB, concSqAC, tangleA_eq, pAB, qAB, rAB, pAC, qAC, rAC, ghz]
  all_goals norm_num

example : concSqAB wState = 4 ∧ concSqAC wState = 4 ∧ tangleA wState = 8 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals simp [concSqAB, concSqAC, tangleA_eq, pAB, qAB, rAB, pAC, qAC, rAC, wState]
  all_goals norm_num

end QI

