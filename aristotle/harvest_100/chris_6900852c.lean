import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace CS

/-! ## A recursive description of the permanent

`pm M l C` is the weighted count of bijections from the rows listed in `l` onto the
column set `C`, where the weight of a bijection is the product of the corresponding
matrix entries.  It is a convenient recursive handle on the permanent. -/

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommSemiring R]

/-- Weighted count of the bijections from the rows in the list `l` onto the columns in `C`. -/
def pm (M : ι → ι → R) : List ι → Finset ι → R
  | [], C => if C = ∅ then 1 else 0
  | r :: rs, C => ∑ c ∈ C, M r c * pm M rs (C.erase c)

@[simp] theorem pm_nil (M : ι → ι → R) (C : Finset ι) :
    pm M [] C = if C = ∅ then 1 else 0 := rfl

theorem pm_cons (M : ι → ι → R) (r : ι) (rs : List ι) (C : Finset ι) :
    pm M (r :: rs) C = ∑ c ∈ C, M r c * pm M rs (C.erase c) := rfl

/-- If the number of available columns does not match the number of rows, there are no
bijections at all. -/
theorem pm_eq_zero_of_card_ne (M : ι → ι → R) :
    ∀ (l : List ι) (C : Finset ι), C.card ≠ l.length → pm M l C = 0 := by
  intro l
  induction l with
  | nil => intro C h; simp only [pm_nil, List.length_nil] at *; rw [if_neg]; intro hC; exact h (by simp [hC])
  | cons r rs ih =>
      intro C h
      rw [pm_cons]
      refine Finset.sum_eq_zero fun c hc => ?_
      have hpos : 0 < C.card := Finset.card_pos.mpr ⟨c, hc⟩
      have hne : (C.erase c).card ≠ rs.length := by
        rw [Finset.card_erase_of_mem hc]
        simp only [List.length_cons] at h
        omega
      rw [ih _ hne, mul_zero]

/-- Splitting the list of rows into two halves: the columns get distributed. -/
theorem pm_append (M : ι → ι → R) :
    ∀ (l₁ l₂ : List ι) (C : Finset ι),
      pm M (l₁ ++ l₂) C = ∑ D ∈ C.powersetCard l₁.length, pm M l₁ D * pm M l₂ (C \ D) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ C
      simp
  | cons r rs ih =>
      intro l₂ C
      rw [List.cons_append, pm_cons]
      have h1 : ∀ c ∈ C, M r c * pm M (rs ++ l₂) (C.erase c)
          = ∑ D ∈ (C.erase c).powersetCard rs.length,
              M r c * pm M rs D * pm M l₂ (C \ insert c D) := by
        intro c hc
        rw [ih, Finset.mul_sum]
        refine Finset.sum_congr rfl fun D hD => ?_
        have hCD : C \ insert c D = (C.erase c) \ D := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
          tauto
        rw [hCD, mul_assoc]
      rw [Finset.sum_congr rfl h1]
      have h2 : ∀ D' ∈ C.powersetCard (rs.length + 1),
          pm M (r :: rs) D' * pm M l₂ (C \ D')
            = ∑ c ∈ D', M r c * pm M rs (D'.erase c) * pm M l₂ (C \ D') := by
        intro D' _
        rw [pm_cons, Finset.sum_mul]
      rw [List.length_cons, Finset.sum_congr rfl h2, Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (i := fun p => (⟨insert p.1 p.2, p.1⟩ : (_ : Finset ι) × ι))
        (j := fun q => (⟨q.2, q.1.erase q.2⟩ : (_ : ι) × Finset ι)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp ⊢
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact hc
          · exact (Finset.mem_erase.mp (hDsub hx)).2
        · rw [Finset.card_insert_of_notMem hcD, hDcard]
      · rintro ⟨D', c⟩ hq
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq ⊢
        obtain ⟨⟨hDsub, hDcard⟩, hc⟩ := hq
        refine ⟨hDsub hc, ?_, ?_⟩
        · intro x hx
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, hDsub (Finset.mem_erase.mp hx).2⟩
        · rw [Finset.card_erase_of_mem hc, hDcard]
          omega
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        simp [Finset.erase_insert hcD]
      · rintro ⟨D', c⟩ hq
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hq
        simp [Finset.insert_erase hq.2]
      · rintro ⟨c, D⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hp
        obtain ⟨hc, hDsub, hDcard⟩ := hp
        have hcD : c ∉ D := fun hcD => (Finset.mem_erase.mp (hDsub hcD)).1 rfl
        simp [Finset.erase_insert hcD]

/-- If some available column cannot be covered by any of the rows, there is nothing to count. -/
theorem pm_eq_zero_of_unreachable (M : ι → ι → R) (c₀ : ι) :
    ∀ (l : List ι) (C : Finset ι), c₀ ∈ C → (∀ r ∈ l, M r c₀ = 0) → pm M l C = 0 := by
  intro l
  induction l with
  | nil =>
      intro C hc₀ _
      rw [pm_nil, if_neg]
      rintro rfl
      exact absurd hc₀ (Finset.notMem_empty _)
  | cons r rs ih =>
      intro C hc₀ hz
      rw [pm_cons]
      refine Finset.sum_eq_zero fun c hc => ?_
      by_cases hcc : c = c₀
      · subst hcc
        rw [hz r List.mem_cons_self, zero_mul]
      · rw [ih _ (Finset.mem_erase.mpr ⟨fun h => hcc h.symm, hc₀⟩)
            (fun r' hr' => hz r' (List.mem_cons_of_mem _ hr')), mul_zero]

/-- If all rows of `l` are supported inside `S` while `C` sticks out of `S`, nothing is counted. -/
theorem pm_eq_zero_of_not_subset (M : ι → ι → R) (S : Finset ι) (l : List ι) (C : Finset ι)
    (hsupp : ∀ r ∈ l, ∀ c, c ∉ S → M r c = 0) (hC : ¬ C ⊆ S) : pm M l C = 0 := by
  obtain ⟨c₀, hc₀C, hc₀S⟩ := Finset.not_subset.mp hC
  exact pm_eq_zero_of_unreachable M c₀ l C hc₀C fun r hr => hsupp r hr c₀ hc₀S

/-- `pm` does not depend on the order in which the rows are listed. -/
theorem pm_swap (M : ι → ι → R) (a b : ι) (l : List ι) (C : Finset ι) :
    pm M (a :: b :: l) C = pm M (b :: a :: l) C := by
  simp only [pm_cons]
  rw [Finset.sum_comm' (t' := C) (s' := fun c₂ => C.erase c₂)
    (by
      intro c₁ c₂
      simp only [Finset.mem_erase]
      constructor
      · rintro ⟨h₁, h₂, h₃⟩
        exact ⟨⟨fun h => h₂ h.symm, h₁⟩, h₃⟩
      · rintro ⟨⟨h₁, h₂⟩, h₃⟩
        exact ⟨h₂, fun h => h₁ h.symm, h₃⟩)]
  refine Finset.sum_congr rfl fun c₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c₁ _ => ?_
  rw [Finset.erase_right_comm]
  ring

theorem pm_of_perm (M : ι → ι → R) {l l' : List ι} (h : l.Perm l') (C : Finset ι) :
    pm M l C = pm M l' C := by
  induction h generalizing C with
  | nil => rfl
  | cons x _ ih => simp only [pm_cons]; exact Finset.sum_congr rfl fun c _ => by rw [ih]
  | swap x y l => exact pm_swap M y x l C
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

/-- If a column `c` can only be covered by the row `r`, peel both off. -/
theorem pm_peel_col (M : ι → ι → R) (l : List ι) (C : Finset ι) (r c : ι)
    (hr : r ∈ l) (hc : c ∈ C) (huniq : ∀ r' ∈ l, r' ≠ r → M r' c = 0) :
    pm M l C = M r c * pm M (l.erase r) (C.erase c) := by
  rw [pm_of_perm M (List.perm_cons_erase hr), pm_cons]
  rw [Finset.sum_eq_single c]
  · intro c' _ hc'
    rw [pm_eq_zero_of_unreachable M c _ _ (Finset.mem_erase.mpr ⟨hc', hc⟩)
      (fun r' hr' => huniq r' (List.mem_of_mem_erase hr') (List.ne_of_mem_erase hr')), mul_zero]
  · intro h
    exact absurd hc h

/-- Two groups of rows with disjoint column supports contribute independently. -/
theorem pm_block (M : ι → ι → R) (l₁ l₂ : List ι) (C₁ C₂ : Finset ι)
    (hsupp₁ : ∀ r ∈ l₁, ∀ c, c ∉ C₁ → M r c = 0)
    (hdisj : Disjoint C₁ C₂) (hcard : C₁.card = l₁.length) :
    pm M (l₁ ++ l₂) (C₁ ∪ C₂) = pm M l₁ C₁ * pm M l₂ C₂ := by
  rw [pm_append, Finset.sum_eq_single C₁]
  · congr 1
    rw [Finset.union_sdiff_cancel_left hdisj]
  · intro D hD hne
    rw [Finset.mem_powersetCard] at hD
    by_cases hsub : D ⊆ C₁
    · exact absurd (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hD.2])) hne
    · rw [pm_eq_zero_of_not_subset M C₁ _ _ hsupp₁ hsub, zero_mul]
  · intro h
    exact absurd (Finset.mem_powersetCard.mpr ⟨Finset.subset_union_left, hcard⟩) h

/-! ### `pm` computes the permanent -/

variable [Fintype ι]

/-- The bijections (as normalized functions) from the rows in `l` onto the columns in `C`. -/
def bijs (l : List ι) (C : Finset ι) : Finset (ι → ι) :=
  Finset.univ.filter (fun f => (∀ x, x ∉ l → f x = x) ∧
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) ∧ (∀ x ∈ l, f x ∈ C))

theorem mem_bijs {l : List ι} {C : Finset ι} {f : ι → ι} :
    f ∈ bijs l C ↔ (∀ x, x ∉ l → f x = x) ∧
      (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) ∧ (∀ x ∈ l, f x ∈ C) := by
  simp [bijs]

theorem pm_eq_sum_bijs (M : ι → ι → R) :
    ∀ (l : List ι), l.Nodup → ∀ (C : Finset ι), C.card = l.length →
      pm M l C = ∑ f ∈ bijs l C, (l.map (fun r => M r (f r))).prod := by
  intro l
  induction l with
  | nil =>
      intro _ C hcard
      have hC : C = ∅ := Finset.card_eq_zero.mp (by simpa using hcard)
      subst hC
      have : bijs ([] : List ι) (∅ : Finset ι) = {id} := by
        ext f
        simp only [mem_bijs, Finset.mem_singleton, not_false_eq_true,
          forall_const, List.mem_nil_iff, IsEmpty.forall_iff, implies_true, and_true]
        constructor
        · intro h; funext x; exact h x
        · rintro rfl x; rfl
      rw [this]
      simp
  | cons r rs ih =>
      intro hnd C hcard
      have hr : r ∉ rs := (List.nodup_cons.mp hnd).1
      have hnd' : rs.Nodup := (List.nodup_cons.mp hnd).2
      have hne : ∀ x, x ∈ rs → x ≠ r := by
        intro x hx h
        subst h
        exact hr hx
      rw [pm_cons]
      have step : ∀ c ∈ C, M r c * pm M rs (C.erase c)
          = ∑ g ∈ bijs rs (C.erase c), M r c * (rs.map (fun x => M x (g x))).prod := by
        intro c hc
        have hcard' : (C.erase c).card = rs.length := by
          rw [Finset.card_erase_of_mem hc, hcard]
          simp
        rw [ih hnd' (C.erase c) hcard', Finset.mul_sum]
      rw [Finset.sum_congr rfl step, Finset.sum_sigma']
      refine Finset.sum_nbij' (i := fun p => Function.update p.2 r p.1)
        (j := fun f => (⟨f r, Function.update f r r⟩ : (_ : ι) × (ι → ι))) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp ⊢
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        refine ⟨?_, ?_, ?_⟩
        · intro x hx
          have hxr : x ≠ r := fun h => hx (by simp [h])
          rw [Function.update_of_ne hxr]
          exact hfix x (fun h => hx (List.mem_cons_of_mem _ h))
        · intro x hx y hy hxy
          rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
          · rfl
          · exfalso
            rw [Function.update_self, Function.update_of_ne (hne y hy')] at hxy
            exact (Finset.mem_erase.mp (hmaps y hy')).1 hxy.symm
          · exfalso
            rw [Function.update_self, Function.update_of_ne (hne x hx')] at hxy
            exact (Finset.mem_erase.mp (hmaps x hx')).1 hxy
          · rw [Function.update_of_ne (hne x hx'),
              Function.update_of_ne (hne y hy')] at hxy
            exact hinj x hx' y hy' hxy
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · rwa [Function.update_self]
          · rw [Function.update_of_ne (hne x hx')]
            exact Finset.mem_of_mem_erase (hmaps x hx')
      · intro f hf
        simp only [Finset.mem_sigma, mem_bijs] at hf ⊢
        obtain ⟨hfix, hinj, hmaps⟩ := hf
        refine ⟨hmaps r List.mem_cons_self, ?_, ?_, ?_⟩
        · intro x hx
          by_cases hxr : x = r
          · subst hxr; rw [Function.update_self]
          · rw [Function.update_of_ne hxr]
            exact hfix x (by simp [List.mem_cons, hxr, hx])
        · intro x hx y hy hxy
          rw [Function.update_of_ne (hne x hx),
            Function.update_of_ne (hne y hy)] at hxy
          exact hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy
        · intro x hx
          rw [Function.update_of_ne (hne x hx)]
          refine Finset.mem_erase.mpr ⟨?_, hmaps x (List.mem_cons_of_mem _ hx)⟩
          intro hcon
          exact hr (hinj x (List.mem_cons_of_mem _ hx) r List.mem_cons_self hcon ▸ hx)
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        have hgr : g r = r := hfix r hr
        simp only [Function.update_self, Sigma.mk.injEq, heq_eq_eq, true_and]
        rw [Function.update_idem]
        funext x
        by_cases hx : x = r
        · subst hx; simp [hgr]
        · simp [Function.update_of_ne hx]
      · intro f hf
        simp only [mem_bijs] at hf
        simp only [Function.update_idem, Function.update_eq_self]
      · rintro ⟨c, g⟩ hp
        simp only [Finset.mem_sigma, mem_bijs] at hp
        obtain ⟨hc, hfix, hinj, hmaps⟩ := hp
        simp only [List.map_cons, List.prod_cons, Function.update_self]
        congr 1
        refine congrArg List.prod (List.map_congr_left ?_)
        intro x hx
        rw [Function.update_of_ne (hne x hx)]

theorem permanent_eq_sum_perm (M : Matrix ι ι R) :
    M.permanent = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  rw [← Matrix.permanent_transpose]
  rfl

theorem sum_bijs_univ (M : ι → ι → R) :
    ∑ f ∈ bijs Finset.univ.toList Finset.univ, (Finset.univ.toList.map (fun r => M r (f r))).prod
      = ∑ σ : Equiv.Perm ι, ∏ i, M i (σ i) := by
  refine (Finset.sum_nbij' (i := fun (σ : Equiv.Perm ι) => (⇑σ : ι → ι))
      (j := fun f => if h : Function.Bijective f then Equiv.ofBijective f h else 1)
      ?_ ?_ ?_ ?_ ?_).symm
  · intro σ _
    refine mem_bijs.mpr ⟨?_, ?_, ?_⟩
    · intro x hx
      exact absurd (Finset.mem_toList.mpr (Finset.mem_univ x)) hx
    · intro x _ y _ hxy
      exact σ.injective hxy
    · intro x _
      exact Finset.mem_univ _
  · intro f _
    exact Finset.mem_univ _
  · intro σ _
    dsimp only
    rw [dif_pos σ.bijective]
    exact Equiv.ext fun x => rfl
  · intro f hf
    have hinj : Function.Injective f := by
      intro x y hxy
      exact (mem_bijs.mp hf).2.1 x (Finset.mem_toList.mpr (Finset.mem_univ x)) y
        (Finset.mem_toList.mpr (Finset.mem_univ y)) hxy
    dsimp only
    rw [dif_pos (Finite.injective_iff_bijective.mp hinj)]
    rfl
  · intro σ _
    exact (Finset.prod_map_toList Finset.univ _).symm

/-- `pm` computes the permanent. -/
theorem pm_eq_permanent (M : Matrix ι ι R) :
    pm (fun i j => M i j) Finset.univ.toList Finset.univ = M.permanent := by
  rw [pm_eq_sum_bijs _ _ (Finset.nodup_toList _) _ (by simp), sum_bijs_univ,
    permanent_eq_sum_perm]

/-! ## The permanent of a 0/1 matrix is a counting function

For a matrix with entries in `{0,1}`, the permanent is literally the number of
permutations `σ` all of whose entries `M i (σ i)` are `1`, i.e. the number of perfect
matchings of the associated bipartite graph.  Membership of the 0/1 permanent in `#P`
is exactly this statement: it counts the witnesses of a relation that can be checked in
polynomial time (here: check `n` matrix entries). -/

theorem permanent_zeroOne_eq_card (M : Matrix ι ι ℕ) (h01 : ∀ i j, M i j = 0 ∨ M i j = 1) :
    M.permanent =
      ((Finset.univ : Finset (Equiv.Perm ι)).filter (fun σ => ∀ i, M i (σ i) = 1)).card := by
  rw [permanent_eq_sum_perm, Finset.card_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h : ∀ i, M i (σ i) = 1
  · rw [if_pos h, Finset.prod_congr rfl (fun i _ => h i), Finset.prod_const_one]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((h01 i (σ i)).resolve_right hi)

/-! ## Permanents and ring homomorphisms

Valiant's reduction produces a matrix with small *negative* entries; those are removed by
computing modulo a large number.  The following two lemmas are the algebraic content of
that step. -/

theorem permanent_map {S : Type*} [CommSemiring S] (f : R →+* S) (M : Matrix ι ι R) :
    (M.map f).permanent = f M.permanent := by
  simp only [Matrix.permanent, Matrix.map_apply, map_sum, map_prod]

/-- Matrices whose entries agree modulo `m` have permanents that agree modulo `m`. -/
theorem permanent_congr_mod {m : ℕ} (A B : Matrix ι ι ℤ)
    (h : ∀ i j, ((A i j : ZMod m)) = ((B i j : ZMod m))) :
    ((A.permanent : ZMod m)) = ((B.permanent : ZMod m)) := by
  have hA := permanent_map (Int.castRingHom (ZMod m)) A
  have hB := permanent_map (Int.castRingHom (ZMod m)) B
  have hAB : A.map (Int.castRingHom (ZMod m)) = B.map (Int.castRingHom (ZMod m)) := by
    ext i j
    exact h i j
  have : ((A.permanent : ℤ) : ZMod m) = (Int.castRingHom (ZMod m)) A.permanent := rfl
  rw [this, ← hA, hAB, hB]
  rfl

end CS

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

