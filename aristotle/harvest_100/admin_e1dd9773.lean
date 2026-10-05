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
def symp : Pauli F n →ₗ[F] Pauli F n →ₗ[F] F :=
  LinearMap.mk₂ F (fun u v => ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1))
    (by
      intro u u' v
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (by
      intro a u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (by
      intro u v v'
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp; ring)
    (by
      intro a u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp; ring)

lemma symp_apply (u v : Pauli F n) :
    symp u v = ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1) := rfl

/-- The Hamming weight of a Pauli operator: the number of sites it acts on. -/
noncomputable def wt (v : Pauli F n) : ℕ := {i | v i ≠ 0}.ncard

/-- The subspace of Pauli operators supported inside the set of sites `X`. -/
def suppSub (X : Finset (Fin n)) : Submodule F (Pauli F n) where
  carrier := {v | ∀ i ∉ X, v i = 0}
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

lemma mem_suppSub {X : Finset (Fin n)} {v : Pauli F n} :
    v ∈ suppSub (F := F) X ↔ ∀ i ∉ X, v i = 0 := Iff.rfl

/-- Projection onto the sites in `X` (all other sites are set to zero). -/
def prj (X : Finset (Fin n)) : Pauli F n →ₗ[F] Pauli F n where
  toFun v := fun i => if i ∈ X then v i else 0
  map_add' := by intro u v; funext i; by_cases h : i ∈ X <;> simp [h]
  map_smul' := by intro a v; funext i; by_cases h : i ∈ X <;> simp [h]

lemma prj_apply (X : Finset (Fin n)) (v : Pauli F n) (i : Fin n) :
    prj X v i = if i ∈ X then v i else 0 := rfl

/-- The symplectic dual (the normalizer, modulo phases) of a set of Pauli operators. -/
def dualCode (S : Submodule F (Pauli F n)) : Submodule F (Pauli F n) where
  carrier := {v | ∀ u ∈ S, symp v u = 0}
  add_mem' := by intro a b ha hb u hu; simp [ha u hu, hb u hu]
  zero_mem' := by intro u _; simp
  smul_mem' := by intro c a ha u hu; simp [ha u hu]

lemma mem_dualCode {S : Submodule F (Pauli F n)} {v : Pauli F n} :
    v ∈ dualCode S ↔ ∀ u ∈ S, symp v u = 0 := Iff.rfl

/-- An `[[n, k, d]]` stabilizer code over the field `F`: a stabilizer group (recorded
by its symplectic representation `stab`, a self-orthogonal subspace of `Pauli F n`
of dimension `n - k`) encoding `k ≥ 1` logical qudits, with minimum distance at
least `d`, i.e. every element of the normalizer that is not in the stabilizer has
weight at least `d`. -/
structure StabilizerCode (F : Type*) [Field F] (n k d : ℕ) where
  /-- symplectic representation of the stabilizer group -/
  stab : Submodule F (Pauli F n)
  /-- the stabilizer group is abelian -/
  isotropic : stab ≤ dualCode stab
  /-- the code encodes `k` logical qudits -/
  dim_stab : finrank F stab + k = n
  /-- at least one logical qudit -/
  k_pos : 1 ≤ k
  /-- the minimum distance is at least `d` -/
  min_dist : ∀ v ∈ dualCode stab, v ∉ stab → d ≤ wt v

section Lemmas

variable (S : Submodule F (Pauli F n)) (X : Finset (Fin n))

lemma wt_le_card_of_mem_suppSub {X : Finset (Fin n)} {v : Pauli F n}
    (hv : v ∈ suppSub (F := F) X) : wt v ≤ X.card := by
  have hsub : {i | v i ≠ 0} ⊆ (X : Set (Fin n)) := by
    intro i hi
    by_contra h
    exact hi (hv i (by simpa using h))
  calc wt v ≤ (X : Set (Fin n)).ncard := Set.ncard_le_ncard hsub X.finite_toSet
    _ = X.card := by simp

/-- The space of operators supported on `X` is isomorphic to `X → F × F`. -/
def suppEquiv : (suppSub (F := F) X) ≃ₗ[F] (X → F × F) where
  toFun v := fun i => (v : Pauli F n) i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl
  invFun w := ⟨fun i => if h : i ∈ X then w ⟨i, h⟩ else 0, by
    intro i hi; simp [hi]⟩
  left_inv := by
    intro v
    apply Subtype.ext
    funext i
    by_cases h : i ∈ X
    · simp [h]
    · simp [h, v.2 i h]
  right_inv := by
    intro w
    funext i
    simp

/-- The space of operators supported on `X` has dimension `2 * |X|`. -/
lemma finrank_suppSub : finrank F (suppSub (F := F) X) = 2 * X.card := by
  rw [(suppEquiv (F := F) X).finrank_eq]
  simp [Module.finrank_pi_fintype, mul_comm]

lemma symp_prj {v : Pauli F n} (hv : v ∈ suppSub (F := F) X) (u : Pauli F n) :
    symp v (prj X u) = symp v u := by
  rw [symp_apply, symp_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ∈ X
  · simp [prj_apply, h]
  · simp [prj_apply, h, hv i h]

end Lemmas

/-- Rank-nullity for a linear map restricted to a submodule. -/
lemma finrank_map_add_finrank_inf_ker {V W : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] [AddCommGroup W] [Module F W] (f : V →ₗ[F] W)
    (p : Submodule F V) :
    finrank F (p.map f) + finrank F ↥(p ⊓ LinearMap.ker f) = finrank F p := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← h]
  congr 1
  have he : Submodule.comap p.subtype (LinearMap.ker f)
      = Submodule.comap p.subtype (p ⊓ LinearMap.ker f) := by
    simp [Submodule.comap_inf]
  rw [he]
  exact ((Submodule.comapSubtypeEquivOfLe (inf_le_left)).finrank_eq).symm

section Counting

variable (S : Submodule F (Pauli F n)) (X : Finset (Fin n))

lemma ker_prj : LinearMap.ker (prj (F := F) X) = suppSub Xᶜ := by
  ext v
  constructor
  · intro hv i hi
    have hiX : i ∈ X := by simpa using hi
    have h0 : prj (F := F) X v i = 0 := by
      rw [show prj (F := F) X v = 0 from hv]; rfl
    rwa [prj_apply, if_pos hiX] at h0
  · intro hv
    show prj (F := F) X v = 0
    funext i
    by_cases h : i ∈ X
    · simp [prj_apply, h, hv i (by simpa using h)]
    · simp [prj_apply, h]

/-- Rank-nullity for the projection onto `X`, applied to `S`. -/
lemma finrank_map_prj_add :
    finrank F (S.map (prj X)) + finrank F ↥(S ⊓ suppSub (F := F) Xᶜ) = finrank F S := by
  have h := finrank_map_add_finrank_inf_ker (V := Pauli F n) (W := Pauli F n) (prj X) S
  rwa [ker_prj (F := F) X] at h

/-- The "duality" half of the argument: operators supported on `X` and orthogonal to
`S` form a space of dimension at least `2|X| - dim (prj X '' S)`. -/
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
lemma correctable_of_card_lt {F : Type*} [Field F] {n k d : ℕ} (Q : StabilizerCode F n k d)
    {A : Finset (Fin n)} (hA : A.card < d) :
    ∀ v ∈ dualCode Q.stab, v ∈ suppSub (F := F) A → v ∈ Q.stab := by
  intro v hv hvA
  by_contra h
  have := Q.min_dist v hv h
  have := wt_le_card_of_mem_suppSub hvA
  omega

/-- **Quantum Singleton bound.** An `[[n, k, d]]` stabilizer code satisfies
`n - k ≥ 2 (d - 1)`. -/
theorem quantum_singleton {F : Type*} [Field F] {n k d : ℕ} (Q : StabilizerCode F n k d) :
    2 * (d - 1) + k ≤ n := by
  classical
  have hdim := Q.dim_stab
  rcases Nat.eq_zero_or_pos d with hd | hd
  · have hd0 : d - 1 = 0 := by omega
    rw [hd0]
    omega
  -- choose two disjoint sets of sites, each of size `m ≤ d - 1`
  have key : ∀ p q : ℕ, p + q ≤ n → p < d → q < d → p + q ≤ finrank F Q.stab := by
    intro p q hpq hp hq
    obtain ⟨A, -, hAcard⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n))) (n := p)
        (by simpa using le_trans (Nat.le_add_right p q) hpq)
    obtain ⟨B, hBsub, hBcard⟩ :=
      Finset.exists_subset_card_eq (s := Aᶜ) (n := q)
        (by rw [Finset.card_compl, hAcard, Fintype.card_fin]; omega)
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_right]
      intro i hi
      have := hBsub hi
      simpa using this
    have := card_add_card_le_finrank Q.stab hdisj
      (correctable_of_card_lt Q (by omega))
      (correctable_of_card_lt Q (by omega))
    omega
  by_cases hcase : 2 * (d - 1) ≤ n
  · have := key (d - 1) (d - 1) (by omega) (by omega) (by omega)
    omega
  · -- impossible: it would force `k = 0`
    exfalso
    have := key ((n + 1) / 2) (n - (n + 1) / 2) (by omega) (by omega) (by omega)
    have hk := Q.k_pos
    omega

/-- The quantum Singleton bound in subtracted form: `n - k ≥ 2 (d - 1)`. -/
theorem quantum_singleton' {F : Type*} [Field F] {n k d : ℕ} (Q : StabilizerCode F n k d) :
    2 * (d - 1) ≤ n - k := by
  have := quantum_singleton Q
  omega

/-- The hypotheses are not vacuous: the trivial `[[n, n, 1]]` code (empty stabilizer
group) is a stabilizer code, for every `n ≥ 1`. -/
def trivialCode (F : Type*) [Field F] (n : ℕ) (hn : 1 ≤ n) : StabilizerCode F n n 1 where
  stab := ⊥
  isotropic := bot_le
  dim_stab := by simp
  k_pos := hn
  min_dist := by
    intro v _ hv
    have hv0 : v ≠ 0 := by simpa using hv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      exact hv0 (funext fun i => by simpa using not_exists.mp h i)
    have hne : ({i | v i ≠ 0}).Nonempty := ⟨i, hi⟩
    rw [wt, Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
    exact hne.ne_empty

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

