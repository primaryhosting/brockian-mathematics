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

lemma concSq_le (z w : State2) : concurrence (rhoOf ![z, w]) ^ 2 ≤ 4 * Sof z w := by
  obtain ⟨p, q, r, s, hpq, hpr, hb, hqs⟩ := exists_factor (det2 z) (mix z w) (det2 w)
  have hN : (0:ℝ) < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rcases hpq with h | h
    · have : 0 < ‖p‖ := norm_pos_iff.mpr h
      positivity
    · have : 0 < ‖q‖ := norm_pos_iff.mpr h
      positivity
  set t : ℝ := Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2)⁻¹ with htdef
  have hts : t ^ 2 = (‖p‖ ^ 2 + ‖q‖ ^ 2)⁻¹ := Real.sq_sqrt (by positivity)
  have ht2 : (t : ℂ) ^ 2 * (p * conj p + q * conj q) = 1 := by
    have h1 : p * conj p + q * conj q = ((‖p‖ ^ 2 + ‖q‖ ^ 2 : ℝ) : ℂ) := by
      simp [Complex.mul_conj, Complex.sq_norm]
    rw [h1, ← Complex.ofReal_pow, hts, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hN),
      Complex.ofReal_one]
  have hd1 : det2 (fun i j => ((t:ℂ) * q) * z i j + (-((t:ℂ) * p)) * w i j) = 0 := by
    rw [det2_lin, ← hpr, ← hb, ← hqs]; ring
  have hd2 : det2 (fun i j => ((t:ℂ) * conj p) * z i j + ((t:ℂ) * conj q) * w i j)
      = r * conj p + s * conj q := by
    rw [det2_lin, ← hpr, ← hb, ← hqs]
    linear_combination (r * conj p + s * conj q) * ht2
  have hdecomp : rhoOf ![fun i j => ((t:ℂ) * q) * z i j + (-((t:ℂ) * p)) * w i j,
      fun i j => ((t:ℂ) * conj p) * z i j + ((t:ℂ) * conj q) * w i j] = rhoOf ![z, w] := by
    funext i j i' j'
    simp only [rhoOf, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination (z i j * conj (z i' j') + w i j * conj (w i' j')) * ht2
  have hle : concurrence (rhoOf ![z, w]) ≤ 2 * ‖r * conj p + s * conj q‖ := by
    have h := concurrence_le _ _ hdecomp
    rw [Fin.sum_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pureConc, hd1, hd2] at h
    simpa using h
  have h0 := concurrence_nonneg (rhoOf ![z, w])
  have hk := key_ineq p q r s
  have hS : Sof z w = ‖p * r‖ ^ 2 + ‖q * s‖ ^ 2 + ‖p * s + q * r‖ ^ 2 / 2 := by
    rw [Sof, hpr, hb, hqs]
  rw [hS]
  nlinarith [norm_nonneg (r * conj p + s * conj q)]

/-- The key polynomial identity: `det ρ_A` splits as the sum of the two Frobenius invariants
belonging to the `A|B` and `A|C` slicings. -/
