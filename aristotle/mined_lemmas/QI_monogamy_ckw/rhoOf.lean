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

noncomputable def rhoOf {n : ℕ} (z : Fin n → State2) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j i' j' => ∑ m, z m i j * conj (z m i' j')

/-- Wootters' concurrence of a two-qubit density operator, defined as the convex roof
of the pure-state concurrence: the infimum of `∑ₘ pₘ C(ψₘ)` over all decompositions
`ρ = ∑ₘ pₘ |ψₘ⟩⟨ψₘ|` (encoded with sub-normalized vectors `zₘ = √pₘ ψₘ`). -/
