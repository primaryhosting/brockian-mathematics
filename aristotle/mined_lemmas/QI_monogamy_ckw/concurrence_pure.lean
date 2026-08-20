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

/-!
## Overview

A three-qubit pure state `ψ` is described by its amplitudes `ψ i j k`.  Tracing out one
qubit gives the two-qubit density operators `rhoAB ψ` and `rhoAC ψ`, whose entanglement is
measured by Wootters' concurrence `concurrence`, defined here as the convex roof of the
pure-state concurrence `2|det|`.  The entanglement of qubit `A` with the pair `BC` is
measured by the tangle `tangleA ψ = 2(1 - Tr ρ_A²)`.  The theorem `QI.monogamy_ckw` states
the Coffman–Kundu–Wootters inequality

`concurrence (rhoAB ψ) ^ 2 + concurrence (rhoAC ψ) ^ 2 ≤ tangleA ψ`.

The proof has two ingredients.

* An upper bound for the convex roof (`concSq_le`).  Writing `ρ_AB = |φ₀⟩⟨φ₀| + |φ₁⟩⟨φ₁|`
  for the two slices `φ_k = ψ · · k`, every `2 × 2` unitary mixing of the two slices is again
  a decomposition of `ρ_AB`.  Factoring the binary quadratic form
  `(x,y) ↦ det (x φ₀ + y φ₁) = a x² + b x y + c y²` into linear forms `(p x + q y)(r x + s y)`
  (`exists_factor`) and rotating the first member of the decomposition onto the root `(q, -p)`
  of that form leaves a single nonzero determinant, equal to `r p̄ + s q̄`.  Hence
  `concurrence (ρ_AB) ≤ 2‖r p̄ + s q̄‖`, and `key_ineq` bounds this by
  `4 (‖a‖² + ‖c‖² + ‖b‖²/2) = 4 · Sof φ₀ φ₁`.

* A polynomial identity (`detA_identity`): `det ρ_A` is exactly the sum of the two Frobenius
  invariants `Sof` belonging to the `B`-slicing and the `C`-slicing of `ψ`.

Combining them with `tangleA ψ = 4 det ρ_A` for normalized `ψ` gives the inequality.
-/

open scoped BigOperators
open ComplexConjugate

namespace QI

/-- A (possibly sub-normalized) two-qubit pure state, given by its amplitudes
`z i j = ⟨ij|z⟩`. -/
abbrev State2 := Fin 2 → Fin 2 → ℂ

/-- A three-qubit pure state, given by its amplitudes `ψ i j k = ⟨ijk|ψ⟩`. -/
abbrev State3 := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The determinant of the `2 × 2` amplitude array of a two-qubit pure state. -/

lemma concurrence_pure (z : State2) : concurrence (rhoOf ![z]) = pureConc z := by
  refine le_antisymm (by simpa using concurrence_le ![z] _ rfl) ?_
  rw [concurrence]
  refine le_csInf ⟨pureConc z, 1, ![z], rfl, by simp⟩ ?_
  rintro s ⟨n, y, hy, rfl⟩
  by_cases hz : ∀ i j, z i j = 0
  · have h0 : pureConc z = 0 := by simp [pureConc, det2, hz]
    rw [h0]
    exact Finset.sum_nonneg fun m _ => pureConc_nonneg _
  · push_neg at hz
    obtain ⟨i0, j0, hz0⟩ := hz
    set c : Fin n → ℂ := fun m => y m i0 j0 / z i0 j0 with hc
    have hym : ∀ m i j, y m i j = c m * z i j := by
      intro m i j
      have hp := rhoOf_parallel z y hy m i j i0 j0
      rw [hc, div_mul_eq_mul_div, eq_div_iff hz0]
      linear_combination hp
    have hdet : ∀ m, det2 (y m) = c m ^ 2 * det2 z := by
      intro m; simp only [det2, hym]; ring
    have hne : Complex.normSq (z i0 j0) ≠ 0 := by simpa [Complex.normSq_eq_zero] using hz0
    have h1 := rhoOf_apply_single z y hy i0 j0 i0 j0
    have h1' : ∑ m, Complex.normSq (y m i0 j0) = Complex.normSq (z i0 j0) := by
      have hcast : ((∑ m, Complex.normSq (y m i0 j0) : ℝ) : ℂ)
          = ((Complex.normSq (z i0 j0) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        simp only [← Complex.mul_conj]
        exact h1
      exact_mod_cast hcast
    have h2 : ∀ m : Fin n, Complex.normSq (y m i0 j0)
        = Complex.normSq (c m) * Complex.normSq (z i0 j0) := by
      intro m; rw [hym m i0 j0, Complex.normSq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h2 m), ← Finset.sum_mul] at h1'
    have hcsum : ∑ m, Complex.normSq (c m) = 1 := by
      have h3 : (∑ m, Complex.normSq (c m)) * Complex.normSq (z i0 j0)
          = 1 * Complex.normSq (z i0 j0) := by rw [one_mul]; exact h1'
      exact mul_right_cancel₀ hne h3
    have hfin : pureConc z = ∑ m, pureConc (y m) := by
      have hterm : ∀ m : Fin n, pureConc (y m) = Complex.normSq (c m) * pureConc z := by
        intro m
        rw [pureConc, pureConc, hdet m, norm_mul, norm_pow, ← Complex.sq_norm]
        ring
      rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.sum_mul, hcsum, one_mul]
    exact hfin.le

/-- The maximally entangled (Bell) state has concurrence one. -/
example : concurrence (rhoOf ![fun i j => if i = j then ((Real.sqrt 2)⁻¹ : ℂ) else 0]) = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  rw [concurrence_pure]
  simp [pureConc, det2, h2]

/-- The GHZ state is normalized. -/
example : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
    ‖(if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0)‖ ^ 2 = 1 := by
  simp [Fin.sum_univ_two]
  norm_num

/-- The GHZ state has maximal `A|BC` tangle. -/
example : tangleA (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0) = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  simp [tangleA, rhoA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, h2]
  norm_num

/-- Its two-qubit reduced states carry no entanglement, in accordance with monogamy. -/
example : concurrence (rhoAB (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0))
    = 0 := by
  refine le_antisymm ?_ (concurrence_nonneg _)
  have h := concurrence_le _ _
    (rhoAB_eq (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0)).symm
  simpa [Fin.sum_univ_two, pureConc, det2] using h

end QI

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

