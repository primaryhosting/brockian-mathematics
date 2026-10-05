import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

open Module

/-- The symplectic (phase-space) representation of the Pauli group on `n` qudits over the
finite field `F`: a Pauli operator is recorded by its `X`-part and `Z`-part on each qudit. -/
abbrev PSpace (F : Type*) (n : ℕ) := Fin n → F × F

variable {F : Type*} [Field F] {n : ℕ}

/-- The symplectic form on the phase space, as a bilinear map.  Two Pauli operators commute
iff their symplectic form vanishes. -/
def sympB : PSpace F n →ₗ[F] PSpace F n →ₗ[F] F :=
  LinearMap.mk₂ F (fun u v => ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1))
    (by
      intro u u' v
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro c u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro u v v'
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))
    (by
      intro c u v
      simp only [smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (by intro i _; simp; ring))

/-- The symplectic form. -/
def symp (u v : PSpace F n) : F := sympB u v

lemma symp_apply (u v : PSpace F n) :
    symp u v = ∑ i, ((u i).1 * (v i).2 - (u i).2 * (v i).1) := rfl

/-- The symplectic dual (centralizer) of a set of Pauli operators. -/
def orth (S : Submodule F (PSpace F n)) : Submodule F (PSpace F n) :=
  (Submodule.dualAnnihilator S).comap sympB

lemma mem_orth {S : Submodule F (PSpace F n)} {v : PSpace F n} :
    v ∈ orth S ↔ ∀ s ∈ S, symp v s = 0 := by
  simp [orth, Submodule.mem_dualAnnihilator, symp]

/-- The support of a Pauli operator. -/
noncomputable def supp (v : PSpace F n) : Finset (Fin n) := Finset.univ.filter (fun i => v i ≠ 0)

/-- The weight of a Pauli operator: the number of qudits it acts on nontrivially. -/
noncomputable def wt (v : PSpace F n) : ℕ := (supp v).card

/-- Pauli operators supported inside a set `A` of qudits. -/
def coordSub (A : Finset (Fin n)) : Submodule F (PSpace F n) where
  carrier := {v | ∀ i ∉ A, v i = 0}
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  zero_mem' := by intro i _; rfl
  smul_mem' := by intro c a ha i hi; simp [ha i hi]

lemma mem_coordSub {A : Finset (Fin n)} {v : PSpace F n} :
    v ∈ (coordSub A : Submodule F (PSpace F n)) ↔ ∀ i ∉ A, v i = 0 := Iff.rfl

/-- Truncation of a Pauli operator to the qudits in `A`. -/
def proj (A : Finset (Fin n)) : PSpace F n →ₗ[F] PSpace F n where
  toFun v := fun i => if i ∈ A then v i else 0
  map_add' := by intro u v; funext i; by_cases h : i ∈ A <;> simp [h]
  map_smul' := by intro c v; funext i; by_cases h : i ∈ A <;> simp [h]

/-! ### Basic lemmas -/

lemma proj_apply (A : Finset (Fin n)) (v : PSpace F n) (i : Fin n) :
    proj A v i = if i ∈ A then v i else 0 := rfl

lemma supp_subset {A : Finset (Fin n)} {v : PSpace F n}
    (hv : v ∈ (coordSub A : Submodule F (PSpace F n))) : supp v ⊆ A := by
  intro i hi
  simp only [supp, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  by_contra h
  exact hi (hv i h)

lemma wt_le_card {A : Finset (Fin n)} {v : PSpace F n}
    (hv : v ∈ (coordSub A : Submodule F (PSpace F n))) : wt v ≤ A.card :=
  Finset.card_le_card (supp_subset hv)

lemma wt_le (v : PSpace F n) : wt v ≤ n := by
  have := Finset.card_le_card (Finset.subset_univ (supp v))
  simpa [wt, Finset.card_fin] using this

lemma coordSub_mono {A B : Finset (Fin n)} (h : A ⊆ B) :
    (coordSub A : Submodule F (PSpace F n)) ≤ coordSub B := by
  intro v hv i hi
  exact hv i (fun hA => hi (h hA))

/-- Pauli operators supported in `A` are determined by their restriction to `A`. -/
noncomputable def coordEquiv (A : Finset (Fin n)) :
    (coordSub A : Submodule F (PSpace F n)) ≃ₗ[F] ({x // x ∈ A} → F × F) where
  toFun v := fun i => (v : PSpace F n) i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g := ⟨fun i => if h : i ∈ A then g ⟨i, h⟩ else 0, by intro i hi; simp [hi]⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases h : i ∈ A
    · simp [h]
    · simp [h, v.2 i h]
  right_inv g := by funext i; simp

lemma finrank_coordSub (A : Finset (Fin n)) :
    finrank F (coordSub A : Submodule F (PSpace F n)) = 2 * A.card := by
  rw [(coordEquiv A).finrank_eq, Module.finrank_pi_fintype F]
  simp [Module.finrank_prod, Fintype.card_coe, mul_comm]

lemma symp_proj {A : Finset (Fin n)} {w : PSpace F n}
    (hw : w ∈ (coordSub A : Submodule F (PSpace F n))) (s : PSpace F n) :
    symp w (proj A s) = symp w s := by
  rw [symp_apply, symp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : i ∈ A
  · simp [proj_apply, h]
  · simp [proj_apply, h, hw i h]

lemma ker_proj (A : Finset (Fin n)) :
    LinearMap.ker (proj A : PSpace F n →ₗ[F] PSpace F n) = coordSub Aᶜ := by
  ext v
  simp only [LinearMap.mem_ker, funext_iff, proj_apply, Pi.zero_apply, mem_coordSub,
    Finset.mem_compl, not_not]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ A
    · simp [hi, h i hi]
    · simp [hi]

lemma finrank_comap_subtype (p q : Submodule F (PSpace F n)) :
    finrank F (Submodule.comap p.subtype q) = finrank F (p ⊓ q : Submodule F (PSpace F n)) := by
  have h := (Submodule.equivMapOfInjective p.subtype (Submodule.injective_subtype p)
    (Submodule.comap p.subtype q)).finrank_eq
  rwa [Submodule.map_comap_subtype] at h

/-- Rank-nullity for the truncation map restricted to a code. -/
lemma finrank_map_proj_add (S : Submodule F (PSpace F n)) (A : Finset (Fin n)) :
    finrank F (S.map (proj A)) + finrank F ((S ⊓ coordSub Aᶜ : Submodule F (PSpace F n))) =
      finrank F S := by
  have h := LinearMap.finrank_range_add_finrank_ker ((proj A).domRestrict S)
  rwa [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, ker_proj,
    finrank_comap_subtype] at h

/-- Local duality: on the qudits of `A`, the centralizer of the code is at least as large as
the codimension of the truncated code. -/
lemma duality (S : Submodule F (PSpace F n)) (A : Finset (Fin n)) :
    2 * A.card ≤ finrank F (S.map (proj A)) +
      finrank F ((orth S ⊓ coordSub A : Submodule F (PSpace F n))) := by
  set T := S.map (proj A) with hT
  set Θ : (coordSub A : Submodule F (PSpace F n)) →ₗ[F] Module.Dual F T :=
    T.dualRestrict ∘ₗ (sympB ∘ₗ (coordSub A).subtype) with hΘ
  have hker : LinearMap.ker Θ = Submodule.comap (coordSub A).subtype (orth S) := by
    ext w
    simp only [hΘ, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.comp_apply,
      Submodule.dualRestrict_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      Submodule.mem_comap, mem_orth]
    constructor
    · intro h s hs
      have h2 := h ⟨proj A s, Submodule.mem_map_of_mem hs⟩
      rw [← symp_proj w.2 s]
      exact h2
    · intro h t
      obtain ⟨s, hs, hst⟩ := t.2
      have : symp (w : PSpace F n) (t : PSpace F n) = 0 := by
        rw [← hst, symp_proj w.2 s]
        exact h s hs
      exact this
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  have h1 : finrank F (LinearMap.range Θ) ≤ finrank F T := by
    calc finrank F (LinearMap.range Θ) ≤ finrank F (Module.Dual F T) := Submodule.finrank_le _
      _ = finrank F T := Subspace.dual_finrank_eq
  rw [hker, finrank_comap_subtype, finrank_coordSub, inf_comm] at hrn
  omega

lemma coordSub_inf_eq_bot {B C : Finset (Fin n)} (h : Disjoint B C) :
    (coordSub B ⊓ coordSub C : Submodule F (PSpace F n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨h1, h2⟩
  have : v = 0 := by
    funext i
    by_cases hi : i ∈ B
    · exact h2 i (Finset.disjoint_left.mp h hi)
    · exact h1 i hi
  simpa using this

lemma finrank_add_le_of_disjoint (S : Submodule F (PSpace F n)) {B C : Finset (Fin n)}
    (h : Disjoint B C) :
    finrank F ((S ⊓ coordSub B : Submodule F (PSpace F n))) +
      finrank F ((S ⊓ coordSub C : Submodule F (PSpace F n))) ≤
      finrank F ((S ⊓ coordSub (B ∪ C) : Submodule F (PSpace F n))) := by
  have hbot : ((S ⊓ coordSub B) ⊓ (S ⊓ coordSub C) : Submodule F (PSpace F n)) = ⊥ := by
    rw [eq_bot_iff, ← coordSub_inf_eq_bot h]
    exact inf_le_inf inf_le_right inf_le_right
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (S ⊓ coordSub B : Submodule F (PSpace F n)) (S ⊓ coordSub C)
  rw [hbot] at h2
  simp only [finrank_bot, add_zero] at h2
  have h3 : ((S ⊓ coordSub B) ⊔ (S ⊓ coordSub C) : Submodule F (PSpace F n)) ≤
      S ⊓ coordSub (B ∪ C) :=
    sup_le (inf_le_inf_left _ (coordSub_mono Finset.subset_union_left))
      (inf_le_inf_left _ (coordSub_mono Finset.subset_union_right))
  calc finrank F ((S ⊓ coordSub B : Submodule F (PSpace F n))) +
        finrank F ((S ⊓ coordSub C : Submodule F (PSpace F n)))
      = finrank F ((S ⊓ coordSub B) ⊔ (S ⊓ coordSub C) : Submodule F (PSpace F n)) := h2.symm
    _ ≤ finrank F ((S ⊓ coordSub (B ∪ C) : Submodule F (PSpace F n))) :=
        Submodule.finrank_mono h3

/-- A set of fewer than `d` qudits is correctable: every centralizer element supported there
already lies in the stabilizer. -/
lemma correctable {S : Submodule F (PSpace F n)} {d : ℕ} (A : Finset (Fin n))
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v) (hA : A.card < d) :
    (orth S ⊓ coordSub A : Submodule F (PSpace F n)) ≤ (S ⊓ coordSub A) := by
  rintro v ⟨hv1, hv2⟩
  refine ⟨?_, hv2⟩
  by_contra hvS
  have h1 := hd v hv1 hvS
  have h2 := wt_le_card hv2
  omega

/-- The key counting inequality attached to a correctable set `A`. -/
lemma key {S : Submodule F (PSpace F n)} {d : ℕ} (A : Finset (Fin n))
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v) (hA : A.card < d) :
    finrank F ((S ⊓ coordSub Aᶜ : Submodule F (PSpace F n))) + 2 * A.card ≤
      finrank F ((S ⊓ coordSub A : Submodule F (PSpace F n))) + finrank F S := by
  have h1 := finrank_map_proj_add S A
  have h2 := duality S A
  have h3 : finrank F ((orth S ⊓ coordSub A : Submodule F (PSpace F n))) ≤
      finrank F ((S ⊓ coordSub A : Submodule F (PSpace F n))) :=
    Submodule.finrank_mono (correctable A hd hA)
  omega

/-- The core estimate: for any two disjoint correctable sets `A`, `B`, the number of qudits
they occupy is at most the number of stabilizer generators. -/
lemma card_add_card_le {S : Submodule F (PSpace F n)} {d : ℕ} {A B : Finset (Fin n)}
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v) (hA : A.card < d) (hB : B.card < d)
    (hAB : Disjoint A B) :
    A.card + B.card ≤ finrank F S := by
  classical
  set C : Finset (Fin n) := (A ∪ B)ᶜ with hC
  have hBC : B ∪ C = Aᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, Finset.mem_union, not_or]
    constructor
    · rintro (hi | ⟨hi, -⟩)
      · exact Finset.disjoint_right.mp hAB hi
      · exact hi
    · intro hi
      by_cases hb : i ∈ B
      · exact Or.inl hb
      · exact Or.inr ⟨hi, hb⟩
  have hAC : A ∪ C = Bᶜ := by
    ext i
    simp only [hC, Finset.mem_union, Finset.mem_compl, Finset.mem_union, not_or]
    constructor
    · rintro (hi | ⟨-, hi⟩)
      · exact Finset.disjoint_left.mp hAB hi
      · exact hi
    · intro hi
      by_cases ha : i ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨ha, hi⟩
  have hdBC : Disjoint B C := by
    rw [Finset.disjoint_right]
    intro i hi hiB
    simp only [hC, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.2 hiB
  have hdAC : Disjoint A C := by
    rw [Finset.disjoint_right]
    intro i hi hiA
    simp only [hC, Finset.mem_compl, Finset.mem_union, not_or] at hi
    exact hi.1 hiA
  have k1 := key (S := S) (d := d) A hd hA
  have k2 := key (S := S) (d := d) B hd hB
  have s1 := finrank_add_le_of_disjoint S hdBC
  have s2 := finrank_add_le_of_disjoint S hdAC
  rw [hBC] at s1
  rw [hAC] at s2
  omega

lemma sympB_injective :
    Function.Injective (sympB : PSpace F n →ₗ[F] Module.Dual F (PSpace F n)) := by
  refine (injective_iff_map_eq_zero _).mpr ?_
  intro v hv
  funext i
  have h1 : sympB v (Pi.single i (0, 1)) = 0 := by rw [hv]; simp
  have h2 : sympB v (Pi.single i (1, 0)) = 0 := by rw [hv]; simp
  have e1 : sympB v (Pi.single i ((0 : F), (1 : F))) = (v i).1 := by
    rw [show (sympB v (Pi.single i ((0 : F), (1 : F)))) =
      ∑ j, ((v j).1 * ((Pi.single i ((0 : F), (1 : F))) j).2 -
        (v j).2 * ((Pi.single i ((0 : F), (1 : F))) j).1) from rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  have e2 : sympB v (Pi.single i ((1 : F), (0 : F))) = -(v i).2 := by
    rw [show (sympB v (Pi.single i ((1 : F), (0 : F)))) =
      ∑ j, ((v j).1 * ((Pi.single i ((1 : F), (0 : F))) j).2 -
        (v j).2 * ((Pi.single i ((1 : F), (0 : F))) j).1) from rfl]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  rw [e1] at h1
  rw [e2, neg_eq_zero] at h2
  exact Prod.ext h1 h2

lemma finrank_PSpace : finrank F (PSpace F n) = 2 * n := by
  simp [Module.finrank_pi_fintype, Module.finrank_prod, mul_comm]

lemma finrank_orth (S : Submodule F (PSpace F n)) :
    finrank F (orth S) + finrank F S = 2 * n := by
  have hfr : finrank F (Module.Dual F (PSpace F n)) = finrank F (PSpace F n) :=
    Subspace.dual_finrank_eq
  have hbij : Function.Bijective (sympB : PSpace F n →ₗ[F] Module.Dual F (PSpace F n)) :=
    ⟨sympB_injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfr.symm).mp sympB_injective⟩
  set e : PSpace F n ≃ₗ[F] Module.Dual F (PSpace F n) := LinearEquiv.ofBijective sympB hbij with he
  have horth : orth S = Submodule.comap (e : PSpace F n →ₗ[F] Module.Dual F (PSpace F n))
      (Submodule.dualAnnihilator S) := rfl
  have hda := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [horth, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  rw [finrank_PSpace] at hda
  omega

/-- **Quantum Singleton bound.**  For an `[[n, k, d]]` stabilizer code — that is, an isotropic
subspace `S` of the symplectic phase space `(F × F)^n` of `n` qudits, with `n - k` generators,
whose centralizer `orth S` contains a nontrivial logical operator and all of whose nontrivial
logical operators have weight at least `d` — one has `n - k ≥ 2 (d - 1)`.

The isotropy hypothesis `hiso` (i.e. the stabilizer group is abelian) is part of the definition
of a stabilizer code; it is used only to rule out the degenerate situation where the code
encodes no qudits at all. -/
theorem quantum_singleton {F : Type*} [Field F] {n k d : ℕ}
    (S : Submodule F (PSpace F n))
    (hiso : ∀ u ∈ S, ∀ v ∈ S, symp u v = 0)
    (hk : finrank F S + k = n)
    (hd : ∀ v ∈ orth S, v ∉ S → d ≤ wt v)
    (hne : ∃ v ∈ orth S, v ∉ S) :
    2 * (d - 1) ≤ n - k := by
  classical
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · simp [hd0]
  obtain ⟨v0, hv0, hv0S⟩ := hne
  have hdn : d ≤ n := le_trans (hd v0 hv0 hv0S) (wt_le v0)
  have hcard : d - 1 ≤ (Finset.univ : Finset (Fin n)).card := by
    rw [Finset.card_fin]; omega
  obtain ⟨A, -, hAcard⟩ := Finset.exists_subset_card_eq hcard
  have hAcompl : Aᶜ.card = n - (d - 1) := by
    rw [Finset.card_compl, hAcard, Finset.card_fin]
  by_cases hcase : 2 * (d - 1) ≤ n
  · have hcard2 : d - 1 ≤ Aᶜ.card := by omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hcard2
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_right]
      intro i hi hiA
      have := hBsub hi
      rw [Finset.mem_compl] at this
      exact this hiA
    have hmain := card_add_card_le (S := S) (d := d) hd (by omega) (by omega) hdisj
    omega
  · have hdisj : Disjoint A Aᶜ := disjoint_compl_right
    have hmain := card_add_card_le (S := S) (d := d) hd (by omega) (by omega) hdisj
    have hSle : S ≤ orth S := by
      intro s hs
      rw [mem_orth]
      intro t ht
      exact hiso s hs t ht
    have h2 := finrank_orth S
    have hSeq : S = orth S := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    rw [← hSeq] at hv0
    exact absurd hv0 hv0S

end QI

