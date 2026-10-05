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

lemma key_dual : 2 * X.card ≤
    finrank F (S.map (prj X)) + finrank F ↥(dualCode S ⊓ suppSub (F := F) X) := by
  set W := S.map (prj X) with hW
  let φ : (suppSub (F := F) X) →ₗ[F] (W →ₗ[F] F) :=
    { toFun := fun v => (symp (v : Pauli F n)).comp W.subtype
      map_add' := by intro a b; ext w; simp
      map_smul' := by intro c a; ext w; simp }
  have hker : LinearMap.ker φ
      = Submodule.comap (suppSub (F := F) X).subtype (dualCode S ⊓ suppSub (F := F) X) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.mem_inf, mem_dualCode]
    constructor
    · intro h
      refine ⟨fun u hu => ?_, v.2⟩
      have hmem : prj X u ∈ W := Submodule.mem_map_of_mem hu
      have h3 : symp (v : Pauli F n) (prj X u) = 0 := LinearMap.congr_fun h ⟨prj X u, hmem⟩
      rw [← symp_prj X v.2 u]
      exact h3
    · rintro ⟨h, -⟩
      ext w
      show symp (v : Pauli F n) (w : Pauli F n) = 0
      obtain ⟨u, hu, hw⟩ := Submodule.mem_map.mp w.2
      rw [show ((w : Pauli F n)) = prj X u from hw.symm, symp_prj X v.2 u]
      exact h u hu
  have hrn := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : finrank F (LinearMap.range φ) ≤ finrank F W := by
    calc finrank F (LinearMap.range φ) ≤ finrank F (W →ₗ[F] F) :=
          Submodule.finrank_le _
      _ = finrank F W := Subspace.dual_finrank_eq
  have hkerrank : finrank F (LinearMap.ker φ) = finrank F ↥(dualCode S ⊓ suppSub (F := F) X) := by
    rw [hker]
    exact (Submodule.comapSubtypeEquivOfLe (inf_le_right)).finrank_eq
  rw [finrank_suppSub] at hrn
  omega

/-- Subadditivity: elements of `S` supported on disjoint sets are independent. -/
