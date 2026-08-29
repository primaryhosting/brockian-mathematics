import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Setting and proof

We work with stabilizer codes over an arbitrary field `F` (the case `F = 𝔽_q` is the
usual one), in their standard symplectic linear-algebra description.  A Pauli operator
on `n` qudits is described, up to phases, by a vector of `Pauli F n = Fin n → F × F`
(the `X`- and `Z`-exponent at each site); two Pauli operators commute exactly when the
symplectic form `symp` vanishes on them.  An `[[n, k, d]]` stabilizer code is then a
self-orthogonal subspace `S ≤ Pauli F n` (`isotropic`) with `dim S = n - k`, encoding
`k ≥ 1` logical qudits, whose minimum distance is at least `d`: every element of the
normalizer `dualCode S` that is not in `S` has Hamming weight at least `d`.

`QI.quantum_singleton` is the quantum Singleton bound `n - k ≥ 2 (d - 1)` for such
codes.  The proof is the dimension-counting shadow of the usual entropic argument.
Writing `pr X` for the projection onto a set `X` of sites, `a X = dim (pr X '' S)`
and `b X = dim (S ∩ suppSub X)` (the elements of `S` supported inside `X`), we use:

* rank-nullity: `a X + b Xᶜ = dim S`;
* duality: `2 |X| ≤ a X + dim (dualCode S ∩ suppSub X)`;
* correctability: if `|X| < d` then `dualCode S ∩ suppSub X ≤ S ∩ suppSub X`, so the
  previous item reads `2 |X| ≤ a X + b X`;
* subadditivity: `b X + b Y ≤ b (X ∪ Y)` for disjoint `X`, `Y` (a direct sum).

For disjoint sets `A`, `B` of sites with `|A|, |B| < d` and `C = (A ∪ B)ᶜ` these give
`dim S = a A + b Aᶜ ≥ (2|A| - b A) + b B + b C` and the same with `A`, `B` swapped;
adding the two yields `dim S ≥ |A| + |B|`.  Taking `|A| = |B| = d - 1` (possible when
`2 (d - 1) ≤ n`) gives the bound, and if `2 (d - 1) > n` one splits all of `Fin n` into
two such sets and obtains `dim S ≥ n`, i.e. `k = 0`, contradicting `k ≥ 1`.

No Mathlib lemma states this bound; the Mathlib input is standard linear algebra
(`LinearMap.finrank_range_add_finrank_ker`, `Submodule.finrank_sup_add_finrank_inf_eq`,
`Subspace.dual_finrank_eq`).
-/

namespace QI

open Module

variable {F : Type*} [Field F] {n : ℕ}

/-- Phase-free description of a Pauli operator on `n` qudits over the field `F`:
the `i`-th coordinate records the `X`-exponent and the `Z`-exponent at site `i`. -/
abbrev Pauli (F : Type*) (n : ℕ) := Fin n → F × F

/-- The symplectic form on `Pauli F n`; two Pauli operators commute iff it vanishes. -/

lemma card_add_card_le_finrank (S : Submodule F (Pauli F n)) {A B : Finset (Fin n)}
    (hAB : Disjoint A B)
    (hA : ∀ v ∈ dualCode S, v ∈ suppSub (F := F) A → v ∈ S)
    (hB : ∀ v ∈ dualCode S, v ∈ suppSub (F := F) B → v ∈ S) :
    A.card + B.card ≤ finrank F S := by
  classical
  set C : Finset (Fin n) := (A ∪ B)ᶜ with hC
  -- notation for the "shortened" dimensions
  set bA := finrank F ↥(S ⊓ suppSub (F := F) A) with hbA
  set bB := finrank F ↥(S ⊓ suppSub (F := F) B) with hbB
  set bC := finrank F ↥(S ⊓ suppSub (F := F) C) with hbC
  have hdualA : finrank F ↥(dualCode S ⊓ suppSub (F := F) A) ≤ bA := by
    apply Submodule.finrank_mono
    rintro v ⟨h1, h2⟩
    exact ⟨hA v h1 h2, h2⟩
  have hdualB : finrank F ↥(dualCode S ⊓ suppSub (F := F) B) ≤ bB := by
    apply Submodule.finrank_mono
    rintro v ⟨h1, h2⟩
    exact ⟨hB v h1 h2, h2⟩
  have hBC : B ∪ C = Aᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, not_or]
    constructor
    · rintro (h | ⟨h1, -⟩)
      · exact fun hA' => (Finset.disjoint_left.mp hAB hA') h
      · exact h1
    · intro h
      by_cases hb : i ∈ B
      · exact Or.inl hb
      · exact Or.inr ⟨h, hb⟩
  have hAC : A ∪ C = Bᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, not_or]
    constructor
    · rintro (h | ⟨-, h2⟩)
      · exact fun hB' => (Finset.disjoint_left.mp hAB h) hB'
      · exact h2
    · intro h
      by_cases ha : i ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨ha, h⟩
  have hdisjBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro i hi
    simp [hC, hi]
  have hdisjAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro i hi
    simp [hC, hi]
  have e1 : bB + bC ≤ finrank F ↥(S ⊓ suppSub (F := F) Aᶜ) := by
    rw [← hBC]
    exact finrank_inf_suppSub_union S hdisjBC
  have e2 : bA + bC ≤ finrank F ↥(S ⊓ suppSub (F := F) Bᶜ) := by
    rw [← hAC]
    exact finrank_inf_suppSub_union S hdisjAC
  have r1 := finrank_map_prj_add S A
  have r2 := finrank_map_prj_add S B
  have k1 := key_dual S A
  have k2 := key_dual S B
  omega

/-- Erasures on a set of fewer than `d` sites are correctable. -/
