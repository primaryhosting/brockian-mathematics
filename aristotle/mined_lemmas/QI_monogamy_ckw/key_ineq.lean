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

lemma key_ineq (p q r s : ℂ) :
    ‖r * conj p + s * conj q‖ ^ 2 ≤ ‖p * r‖ ^ 2 + ‖q * s‖ ^ 2 + ‖p * s + q * r‖ ^ 2 / 2 := by
  have h1 : ‖r * conj p + s * conj q‖ ^ 2
      = ‖r * conj p‖ ^ 2 + ‖s * conj q‖ ^ 2 + 2 * ((r * conj p) * conj (s * conj q)).re := by
    simp [Complex.sq_norm, Complex.normSq_add, mul_pow]
  have h2 : ‖p * s + q * r‖ ^ 2 = ‖p * s‖ ^ 2 + ‖q * r‖ ^ 2 + 2 * ((p * s) * conj (q * r)).re := by
    simp [Complex.sq_norm, Complex.normSq_add, mul_pow]
  have h3 : ((r * conj p) * conj (s * conj q)).re = ((p * s) * conj (q * r)).re := by
    have h : (p * s) * conj (q * r) = conj ((r * conj p) * conj (s * conj q)) := by
      simp [map_mul]; ring
    rw [h, Complex.conj_re]
  have h4 : ((p * s) * conj (q * r)).re ≤ ‖p * s‖ * ‖q * r‖ := by
    calc ((p * s) * conj (q * r)).re ≤ ‖(p * s) * conj (q * r)‖ := Complex.re_le_norm _
      _ = ‖p * s‖ * ‖q * r‖ := by simp
  have h5 : ‖r * conj p‖ = ‖p * r‖ := by simp; ring
  have h6 : ‖s * conj q‖ = ‖q * s‖ := by simp; ring
  rw [h1, h2, h3, h5, h6]
  nlinarith [sq_nonneg (‖p * s‖ - ‖q * r‖), h4]

/-- The core bound: the convex-roof concurrence of a rank-≤2 two-qubit state is controlled by
the Frobenius invariant of its associated quadratic form. -/
