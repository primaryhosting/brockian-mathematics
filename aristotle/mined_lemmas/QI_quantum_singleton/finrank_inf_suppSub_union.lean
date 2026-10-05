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

lemma finrank_inf_suppSub_union {X Y : Finset (Fin n)} (h : Disjoint X Y) :
    finrank F ↥(S ⊓ suppSub (F := F) X) + finrank F ↥(S ⊓ suppSub (F := F) Y)
      ≤ finrank F ↥(S ⊓ suppSub (F := F) (X ∪ Y)) := by
  have hbot : (S ⊓ suppSub (F := F) X) ⊓ (S ⊓ suppSub (F := F) Y) = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨⟨-, hvX⟩, ⟨-, hvY⟩⟩
    have : v = 0 := by
      funext i
      by_cases hi : i ∈ X
      · exact hvY i (Finset.disjoint_left.mp h hi)
      · exact hvX i hi
    simpa using this
  have hle : (S ⊓ suppSub (F := F) X) ⊔ (S ⊓ suppSub (F := F) Y)
      ≤ S ⊓ suppSub (F := F) (X ∪ Y) := by
    apply sup_le
    · exact inf_le_inf_left S (fun v hv i hi => hv i (fun hx => hi (Finset.mem_union_left _ hx)))
    · exact inf_le_inf_left S (fun v hv i hi => hv i (fun hy => hi (Finset.mem_union_right _ hy)))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (S ⊓ suppSub (F := F) X) (S ⊓ suppSub (F := F) Y)
  rw [hbot] at hsum
  simp only [finrank_bot, add_zero] at hsum
  rw [← hsum]
  exact Submodule.finrank_mono hle

end Counting

/-- The main counting step: if erasures on `A` and on `B` are correctable
(every normalizer element supported on `A`, resp. `B`, is already in `S`),
then `dim S ≥ |A| + |B|`. -/
