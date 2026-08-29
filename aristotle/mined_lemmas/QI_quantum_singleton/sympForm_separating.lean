/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The **quantum Singleton bound** (Knill–Laflamme bound) states that an `[[n, k, d]]`
quantum error-correcting code satisfies `n - k ≥ 2 (d - 1)`.

This file formalises the bound for **stabilizer codes** in the standard symplectic
(`GF(q)`-linear) representation, which is the combinatorial model in which the
statement is usually verified.

A stabilizer code of length `n` over a finite field `F` is encoded by:

* a subspace `S ⊆ (F × F)^n` (the *stabilizer*, written additively in the symplectic
  picture, where the pair `(a, b)` at coordinate `i` records the `X`-part and the
  `Z`-part of a Pauli operator on the `i`-th qudit),
* which is **isotropic** for the symplectic form
  `ω(u, v) = ∑ i, (u i).1 * (v i).2 - (u i).2 * (v i).1`
  (this is exactly the statement that the corresponding Pauli operators commute),
* with `dim S = n - k`, so that the joint eigenspace (the code space) has
  dimension `q ^ k`.

The *normalizer* of the code is the symplectic dual `D = S^⊥`, of dimension `n + k`,
and the **distance** `d` of the code is the minimum Hamming weight of a nonzero
element of `D` (this is the distance of a *pure*, i.e. non-degenerate, code; a
degenerate code takes the minimum over `D \ S` instead).  Here `d` is required to be
*exactly* the minimum weight: it is a lower bound for all nonzero elements of `D`
(`dist_le`) and it is attained (`dist_attained`).

The proof is the symplectic Singleton argument: deleting the first `d - 1`
coordinates is injective on `D`, because a nonzero element of `D` supported on
`d - 1` coordinates would have weight `< d`.  Hence
`n + k = dim D ≤ 2 (n - (d - 1))`, which is the bound.
-/

namespace QI

open Finset

/-! ### The symplectic form on the Pauli space `(F × F)^n` -/

/-- The symplectic form on the space `(F × F)^n` of Pauli errors:
`ω(u, v) = ∑ i, (u i).1 * (v i).2 - (u i).2 * (v i).1`.
Two Pauli operators commute exactly when this form vanishes on their symplectic
representatives. -/

lemma sympForm_separating {F : Type*} [Field F] {n : ℕ} (u : Fin n → F × F)
    (hu : ∀ v, sympForm F n u v = 0) : u = 0 := by
  funext i
  have h1 := hu (Pi.single i (0, 1))
  have h2 := hu (Pi.single i (1, 0))
  simp only [sympForm_apply] at h1 h2
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [Pi.single_eq_of_ne hb]) (by simp)] at h1 h2
  simp at h1 h2
  exact Prod.ext h1 h2

