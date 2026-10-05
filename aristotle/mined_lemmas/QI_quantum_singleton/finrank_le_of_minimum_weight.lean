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

lemma finrank_le_of_minimum_weight {F : Type*} [Field F] [DecidableEq F] {n d : ℕ}
    (D : Submodule F (Fin n → F × F))
    (hd : ∀ v ∈ D, v ≠ 0 → d ≤ hammingNorm v) :
    Module.finrank F D ≤ 2 * (n - (d - 1)) := by
  set m := d - 1 with hm
  set emb : Fin (n - m) → Fin n := fun j => ⟨j + m, by omega⟩ with hemb
  have hinj : Function.Injective (((LinearMap.funLeft F (F × F) emb)).comp D.subtype) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨v, hv⟩ hker
    have hz : ∀ j : Fin (n - m), v (emb j) = 0 := by
      intro j
      have := congrFun (LinearMap.mem_ker.mp hker) j
      simpa [LinearMap.funLeft_apply] using this
    have hvz : ∀ i : Fin n, m ≤ (i : ℕ) → v i = 0 := by
      intro i hi
      have hlt : (i : ℕ) - m < n - m := by omega
      have := hz ⟨(i : ℕ) - m, hlt⟩
      simpa [hemb, Fin.ext_iff, Nat.sub_add_cancel hi] using this
    have hsub : (univ.filter (fun i : Fin n => v i ≠ 0)) ⊆
        univ.filter (fun i : Fin n => (i : ℕ) < m) := by
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi ⊢
      by_contra h
      exact hi (hvz i (by omega))
    have hcard : (univ.filter (fun i : Fin n => (i : ℕ) < m)).card ≤ m := by
      have h := Finset.card_le_card_of_injOn (s := univ.filter (fun i : Fin n => (i : ℕ) < m))
        (t := Finset.range m) (fun i => (i : ℕ))
        (by intro i hi; simp_all)
        (by intro a _ b _ h; exact Fin.ext h)
      simpa using h
    have hw : hammingNorm v ≤ m := le_trans (Finset.card_le_card hsub) hcard
    have hv0 : v = 0 := by
      by_contra hne
      have hdv := hd v hv hne
      rcases Nat.eq_zero_or_pos d with h0 | hpos
      · rw [h0] at hm
        rw [hm] at hw
        exact hne (hammingNorm_eq_zero.mp (Nat.le_zero.mp (by simpa using hw)))
      · omega
    exact (Submodule.mem_bot F).mpr (Subtype.ext hv0)
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : Module.finrank F (Fin (n - m) → F × F) = 2 * (n - m) := by
    simp [Module.finrank_pi_fintype]; ring
  rw [h2] at h1
  exact h1

/-! ### Stabilizer codes -/

/-- An `[[n, k, d]]` **stabilizer code** over the finite field `F`, in the symplectic
representation.

* `S` is the stabilizer, a subspace of the Pauli space `(F × F)^n` of dimension `n - k`,
* `isotropic` says that the corresponding Pauli operators pairwise commute,
* the normalizer is the symplectic dual `D = S^⊥`, and the fields `dist_le` and
  `dist_attained` say that `d` is exactly the minimum Hamming weight of a nonzero
  element of `D`, i.e. the code is a pure code of distance `d`. -/
structure StabilizerCode (F : Type*) [Field F] [DecidableEq F] (n k d : ℕ) where
  /-- The stabilizer subspace, in symplectic (`X`-part, `Z`-part) coordinates. -/
  S : Submodule F (Fin n → F × F)
  /-- The stabilizer has `n - k` independent generators. -/
  dim_S : Module.finrank F S = n - k
  /-- The number of encoded qudits is at most the number of physical qudits. -/
  k_le_n : k ≤ n
  /-- The stabilizer is isotropic: its Pauli operators commute pairwise. -/
  isotropic : ∀ u ∈ S, ∀ v ∈ S, sympForm F n u v = 0
  /-- Every nonzero element of the normalizer `S^⊥` has weight at least `d`. -/
  dist_le : ∀ v ∈ (sympForm F n).orthogonal S, v ≠ 0 → d ≤ hammingNorm v
  /-- The distance `d` is attained by some nonzero element of the normalizer. -/
  dist_attained : ∃ v ∈ (sympForm F n).orthogonal S, v ≠ 0 ∧ hammingNorm v = d

variable {F : Type*} [Field F] [DecidableEq F] {n k d : ℕ}

/-- The normalizer `S^⊥` of an `[[n, k, d]]` stabilizer code has dimension `n + k`. -/
