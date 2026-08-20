import Mathlib
-- (Lean 4 requires `import` commands to precede any module docstring, so the required
-- header comment is reproduced verbatim immediately below.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Set Cardinal
open scoped Ordinal

namespace Aronszajn

/-! ## Countable ordinals -/

/-- An ordinal is countable (i.e. its set of predecessors is countable) iff it is `< ω₁`. -/
lemma countable_Iio_iff (o : Ordinal.{0}) : (Set.Iio o).Countable ↔ o < ω₁ := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one,
    ← Cardinal.ord_aleph, Cardinal.lt_ord]

/-! ## A coherent sequence of finite-to-one functions -/

/-- For `α < ω₁`, a sequence of ordinals `< α` which is cofinal in `α` in the weak sense that
every `ξ < α` satisfies `ξ ≤ cs α n` for some `n`.  Junk value otherwise. -/
noncomputable def cs (α : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  open Classical in
  if h : ∃ g : ℕ → Ordinal.{0}, ∀ ξ < α, ∃ n, ξ ≤ g n ∧ g n < α then h.choose else fun _ => 0

/-- `Good α ξ n` says that stage `cs α n` is below `α` and reaches at least `ξ`. -/
def Good (α ξ : Ordinal.{0}) (n : ℕ) : Prop := ξ ≤ cs α n ∧ cs α n < α

lemma cs_spec {α : Ordinal.{0}} (hα : α < ω₁) {ξ : Ordinal.{0}} (hξ : ξ < α) :
    ∃ n, Good α ξ n := by
  classical
  have hex : ∃ g : ℕ → Ordinal.{0}, ∀ η < α, ∃ n, η ≤ g n ∧ g n < α := by
    obtain ⟨g, hg⟩ := ((countable_Iio_iff α).2 hα).exists_eq_range ⟨ξ, hξ⟩
    refine ⟨g, fun η hη => ?_⟩
    have : η ∈ Set.range g := by rw [← hg]; exact hη
    obtain ⟨n, rfl⟩ := this
    exact ⟨n, le_rfl, hη⟩
  have : cs α = hex.choose := by rw [cs, dif_pos hex]
  obtain ⟨n, h1, h2⟩ := hex.choose_spec ξ hξ
  exact ⟨n, by rw [Good, this]; exact ⟨h1, h2⟩⟩

/-- The least `n` with `Good α ξ n`, if any. -/
noncomputable def kk (α ξ : Ordinal.{0}) : ℕ :=
  open Classical in
  if h : ∃ n, Good α ξ n then Nat.find h else 0

lemma kk_spec {α ξ : Ordinal.{0}} (h : ∃ n, Good α ξ n) : Good α ξ (kk α ξ) := by
  classical
  rw [kk, dif_pos h]; exact Nat.find_spec h

lemma kk_le {α ξ : Ordinal.{0}} {m : ℕ} (hm : Good α ξ m) : kk α ξ ≤ m := by
  classical
  rw [kk, dif_pos ⟨m, hm⟩]; exact Nat.find_le hm

/-- The coherent sequence: `ee α` is a finite-to-one function on `α`, and for `β < α` the
restriction of `ee α` to `β` differs from `ee β` in only finitely many places. -/
noncomputable def ee : Ordinal.{0} → Ordinal.{0} → ℕ
  | α => fun ξ =>
    open Classical in
    if _h : ∃ n : ℕ, Good α ξ n then max (ee (cs α (kk α ξ)) ξ) (kk α ξ) else 0
  termination_by α => α
  decreasing_by exact (kk_spec _h).2

lemma ee_of_good {α ξ : Ordinal.{0}} (h : ∃ n : ℕ, Good α ξ n) :
    ee α ξ = max (ee (cs α (kk α ξ)) ξ) (kk α ξ) := by
  classical
  rw [ee]; exact dif_pos h

lemma ee_of_not_good {α ξ : Ordinal.{0}} (h : ¬ ∃ n : ℕ, Good α ξ n) : ee α ξ = 0 := by
  classical
  rw [ee]; exact dif_neg h

lemma ee_eq_zero_of_ge {α ξ : Ordinal.{0}} (h : α ≤ ξ) : ee α ξ = 0 := by
  apply ee_of_not_good
  rintro ⟨n, h1, h2⟩
  exact absurd (h.trans h1) (not_le.2 h2)

/-- If all fibers of `ee γ` below `γ` are finite, so are the sets where `ee γ` is `≤ n`. -/
lemma le_finite_of_fibers {γ : Ordinal.{0}}
    (h : ∀ n : ℕ, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = n}.Finite) (n : ℕ) :
    {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ ≤ n}.Finite := by
  have hEq : {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ ≤ n}
      = ⋃ w ∈ Set.Iic n, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = w} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨ee γ ξ, h2, h1, rfl⟩
    · rintro ⟨w, hw, h1, rfl⟩; exact ⟨h1, hw⟩
  rw [hEq]
  exact Set.Finite.biUnion (Set.finite_Iic n) fun w _ => h w

/-- The two properties, proved by simultaneous transfinite induction:
finite fibers, and coherence with all earlier functions. -/
lemma ee_main : ∀ α : Ordinal.{0}, α < ω₁ →
    (∀ n : ℕ, {ξ : Ordinal.{0} | ξ < α ∧ ee α ξ = n}.Finite) ∧
      (∀ β < α, {ξ : Ordinal.{0} | ξ < β ∧ ee α ξ ≠ ee β ξ}.Finite) := by
  intro α
  induction α using Ordinal.induction with
  | _ α IH =>
    intro hα
    have IHfib : ∀ γ < α, ∀ n : ℕ, {ξ : Ordinal.{0} | ξ < γ ∧ ee γ ξ = n}.Finite :=
      fun γ hγ => (IH γ hγ (hγ.trans hα)).1
    have IHcoh : ∀ γ < α, ∀ δ < γ, {ξ : Ordinal.{0} | ξ < δ ∧ ee γ ξ ≠ ee δ ξ}.Finite :=
      fun γ hγ => (IH γ hγ (hγ.trans hα)).2
    constructor
    · -- finite fibers
      intro n
      set F : ℕ → Set Ordinal.{0} := fun k =>
        if cs α k < α then insert (cs α k) {ξ : Ordinal.{0} | ξ < cs α k ∧ ee (cs α k) ξ ≤ n}
        else ∅ with hFdef
      have hFfin : ∀ k, (F k).Finite := by
        intro k
        by_cases h : cs α k < α
        · simp only [hFdef, if_pos h]
          exact Set.Finite.insert _ (le_finite_of_fibers (IHfib (cs α k) h) n)
        · simp only [hFdef, if_neg h]
          exact Set.finite_empty
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic n) fun k _ => hFfin k) ?_
      rintro ξ ⟨hξα, hval⟩
      have hg : ∃ m, Good α ξ m := cs_spec hα hξα
      have hk := kk_spec hg
      have hmax : max (ee (cs α (kk α ξ)) ξ) (kk α ξ) = n := (ee_of_good hg).symm.trans hval
      have hkn : kk α ξ ≤ n := by omega
      have hwn : ee (cs α (kk α ξ)) ξ ≤ n := by omega
      refine Set.mem_biUnion (Set.mem_Iic.2 hkn) ?_
      simp only [hFdef, if_pos hk.2]
      rcases eq_or_lt_of_le hk.1 with h | h
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · exact Set.mem_insert_of_mem _ ⟨h, hwn⟩
    · -- coherence
      intro β hβ
      obtain ⟨m, hm⟩ := cs_spec hα hβ
      set F : ℕ → Set Ordinal.{0} := fun k =>
        if cs α k < α then
          insert (cs α k)
            ({ξ : Ordinal.{0} | ξ < β ∧ ξ < cs α k ∧ ee (cs α k) ξ ≠ ee β ξ} ∪
              {ξ : Ordinal.{0} | ξ < cs α k ∧ ee (cs α k) ξ ≤ k})
        else ∅ with hFdef
      have hFfin : ∀ k, (F k).Finite := by
        intro k
        by_cases h : cs α k < α
        · simp only [hFdef, if_pos h]
          refine Set.Finite.insert _ (Set.Finite.union ?_
            (le_finite_of_fibers (IHfib (cs α k) h) k))
          rcases lt_trichotomy (cs α k) β with hlt | heq | hgt
          · refine Set.Finite.subset (IHcoh β hβ (cs α k) hlt) ?_
            rintro ξ ⟨_, h2, h3⟩
            exact ⟨h2, fun hcon => h3 hcon.symm⟩
          · refine Set.Finite.subset (Set.finite_empty) ?_
            rintro ξ ⟨_, _, h3⟩
            exact absurd (by rw [heq]) h3
          · refine Set.Finite.subset (IHcoh (cs α k) h β hgt) ?_
            rintro ξ ⟨h1, _, h3⟩
            exact ⟨h1, h3⟩
        · simp only [hFdef, if_neg h]
          exact Set.finite_empty
      refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_Iic m) fun k _ => hFfin k) ?_
      rintro ξ ⟨hξβ, hne⟩
      have hξα : ξ < α := hξβ.trans hβ
      have hg : ∃ j, Good α ξ j := cs_spec hα hξα
      have hk := kk_spec hg
      have hkm : kk α ξ ≤ m := kk_le ⟨hξβ.le.trans hm.1, hm.2⟩
      have hee := ee_of_good hg
      refine Set.mem_biUnion (Set.mem_Iic.2 hkm) ?_
      simp only [hFdef, if_pos hk.2]
      rcases eq_or_lt_of_le hk.1 with h | h
      · exact Set.mem_insert_iff.2 (Or.inl h)
      · refine Set.mem_insert_of_mem _ ?_
        by_cases hle : ee (cs α (kk α ξ)) ξ ≤ kk α ξ
        · exact Or.inr ⟨h, hle⟩
        · refine Or.inl ⟨hξβ, h, ?_⟩
          rw [hee] at hne
          rwa [max_eq_left (not_le.1 hle).le] at hne

lemma ee_fiber_finite {α : Ordinal.{0}} (hα : α < ω₁) (n : ℕ) :
    {ξ : Ordinal.{0} | ξ < α ∧ ee α ξ = n}.Finite := (ee_main α hα).1 n

lemma ee_coherent {α β : Ordinal.{0}} (hα : α < ω₁) (hβ : β < α) :
    {ξ : Ordinal.{0} | ξ < β ∧ ee α ξ ≠ ee β ξ}.Finite := (ee_main α hα).2 β hβ

/-! ## The tree -/

/-- Restriction of a function to the ordinals below `γ` (with junk value `0` elsewhere). -/
noncomputable def rest (x : Ordinal.{0} → ℕ) (γ : Ordinal.{0}) : Ordinal.{0} → ℕ :=
  fun ξ => if ξ < γ then x ξ else 0

lemma rest_of_lt {x : Ordinal.{0} → ℕ} {γ ξ : Ordinal.{0}} (h : ξ < γ) : rest x γ ξ = x ξ :=
  if_pos h

lemma rest_of_ge {x : Ordinal.{0} → ℕ} {γ ξ : Ordinal.{0}} (h : γ ≤ ξ) : rest x γ ξ = 0 :=
  if_neg (not_lt.2 h)

/-- Nodes of the tree: a level `β < ω₁` together with a function which agrees below `β` with
some `ee α`, `β ≤ α < ω₁`, and vanishes from `β` on. -/
def Nice (β : Ordinal.{0}) (x : Ordinal.{0} → ℕ) : Prop :=
  β < ω₁ ∧ (∀ ξ, β ≤ ξ → x ξ = 0) ∧ ∃ α, β ≤ α ∧ α < ω₁ ∧ ∀ ξ < β, x ξ = ee α ξ

/-- The Aronszajn tree. -/
def Tree : Type 1 := {p : Ordinal.{0} × (Ordinal.{0} → ℕ) // Nice p.1 p.2}

namespace Tree

/-- The level of a node. -/
def lvl (a : Tree) : Ordinal.{0} := a.1.1

/-- The function attached to a node. -/
def fn (a : Tree) : Ordinal.{0} → ℕ := a.1.2

lemma ext' {a b : Tree} (h1 : lvl a = lvl b) (h2 : ∀ ξ < lvl a, fn a ξ = fn b ξ) : a = b := by
  refine Subtype.ext (Prod.ext h1 (funext fun ξ => ?_))
  rcases lt_or_ge ξ (lvl a) with h | h
  · exact h2 ξ h
  · rw [a.2.2.1 ξ h, b.2.2.1 ξ (h1.ge.trans h)]

instance : PartialOrder Tree where
  le a b := lvl a ≤ lvl b ∧ ∀ ξ < lvl a, fn a ξ = fn b ξ
  le_refl a := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans a b c hab hbc := ⟨hab.1.trans hbc.1, fun ξ hξ =>
    (hab.2 ξ hξ).trans (hbc.2 ξ (lt_of_lt_of_le hξ hab.1))⟩
  le_antisymm a b hab hba := ext' (le_antisymm hab.1 hba.1) hab.2

lemma le_def {a b : Tree} : a ≤ b ↔ lvl a ≤ lvl b ∧ ∀ ξ < lvl a, fn a ξ = fn b ξ := Iff.rfl

lemma lt_iff {a b : Tree} : a < b ↔ lvl a < lvl b ∧ ∀ ξ < lvl a, fn a ξ = fn b ξ := by
  rw [lt_iff_le_and_ne, le_def]
  constructor
  · rintro ⟨⟨hle, hag⟩, hne⟩
    exact ⟨lt_of_le_of_ne hle fun h => hne (ext' h hag), hag⟩
  · rintro ⟨hlt, hag⟩
    exact ⟨⟨hlt.le, hag⟩, fun h => absurd (congrArg lvl h) hlt.ne⟩

/-- The node obtained by restricting a node to a smaller level. -/
noncomputable def trunc (a : Tree) (γ : Ordinal.{0}) (hγ : γ ≤ lvl a) : Tree :=
  ⟨(γ, rest (fn a) γ), by
    obtain ⟨hlt, hzero, α, hle, hα, hval⟩ := a.2
    refine ⟨lt_of_le_of_lt hγ hlt, fun ξ hξ => if_neg (not_lt.2 hξ), α, hγ.trans hle, hα,
      fun ξ hξ => ?_⟩
    have hξ' : ξ < γ := hξ
    show rest (fn a) γ ξ = ee α ξ
    rw [rest_of_lt hξ']
    exact hval ξ (lt_of_lt_of_le hξ' hγ)⟩

lemma lvl_trunc (a : Tree) (γ : Ordinal.{0}) (hγ : γ ≤ lvl a) : lvl (trunc a γ hγ) = γ := rfl

lemma trunc_lt (a : Tree) (γ : Ordinal.{0}) (hγ : γ < lvl a) : trunc a γ hγ.le < a := by
  refine lt_iff.2 ⟨hγ, fun ξ hξ => ?_⟩
  exact if_pos hξ

lemma eq_trunc_of_lt {a b : Tree} (h : b < a) : b = trunc a (lvl b) h.le.1 := by
  refine ext' rfl fun ξ hξ => ?_
  rw [show fn (trunc a (lvl b) h.le.1) ξ = rest (fn a) (lvl b) ξ from rfl, rest_of_lt hξ]
  exact (lt_iff.1 h).2 ξ hξ

/-- The predecessors of a node `a` are order-isomorphic to the ordinals below `lvl a`. -/
noncomputable def predIso (a : Tree) : {b : Tree // b < a} ≃o Set.Iio (lvl a) where
  toFun b := ⟨lvl b.1, (lt_iff.1 b.2).1⟩
  invFun γ := ⟨trunc a γ.1 γ.2.le, trunc_lt a γ.1 γ.2⟩
  left_inv b := Subtype.ext (eq_trunc_of_lt b.2).symm
  right_inv γ := Subtype.ext rfl
  map_rel_iff' := by
    rintro ⟨b, hb⟩ ⟨b', hb'⟩
    simp only [Subtype.mk_le_mk]
    constructor
    · intro hle
      refine le_def.2 ⟨hle, fun ξ hξ => ?_⟩
      rw [(lt_iff.1 hb).2 ξ hξ, ← (lt_iff.1 hb').2 ξ (lt_of_lt_of_le hξ hle)]
    · intro hle
      exact (le_def.1 hle).1

lemma lvl_lt_omega1 (a : Tree) : lvl a < ω₁ := a.2.1

lemma exists_lvl_eq {β : Ordinal.{0}} (hβ : β < ω₁) : ∃ a : Tree, lvl a = β := by
  refine ⟨⟨(β, rest (ee β) β), hβ, fun ξ hξ => if_neg (not_lt.2 hξ), β, le_rfl, hβ,
    fun ξ hξ => if_pos hξ⟩, rfl⟩

lemma level_countable (β : Ordinal.{0}) : {a : Tree | lvl a = β}.Countable := by
  classical
  by_cases hβ : β < ω₁
  · set D : Tree → Set (Ordinal.{0} × ℕ) := fun a =>
      {p | p.1 < β ∧ fn a p.1 = p.2 ∧ fn a p.1 ≠ ee β p.1} with hDdef
    have hdiff : ∀ a : Tree, lvl a = β →
        {ξ : Ordinal.{0} | ξ < β ∧ fn a ξ ≠ ee β ξ}.Finite := by
      intro a ha
      obtain ⟨_, _, α, hle, hα, hval⟩ := a.2
      have hle' : β ≤ α := ha ▸ hle
      rcases eq_or_lt_of_le hle' with heq | hlt
      · refine Set.Finite.subset Set.finite_empty ?_
        rintro ξ ⟨h1, h2⟩
        exact absurd ((hval ξ (by rw [← ha] at h1; exact h1)).trans (by rw [heq])) h2
      · refine Set.Finite.subset (ee_coherent hα hlt) ?_
        rintro ξ ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rw [← hval ξ (by rw [← ha] at h1; exact h1)]
        exact h2
    have hfin : ∀ a : Tree, lvl a = β → (D a).Finite := by
      intro a ha
      refine Set.Finite.subset ((hdiff a ha).image (fun ξ => (ξ, fn a ξ))) ?_
      rintro ⟨ξ, v⟩ ⟨h1, h2, h3⟩
      exact ⟨ξ, ⟨h1, h3⟩, by simp [h2]⟩
    have hsub : ∀ a : Tree, D a ⊆ Set.Iio β ×ˢ (Set.univ : Set ℕ) := by
      rintro a ⟨ξ, v⟩ ⟨h1, _, _⟩
      exact ⟨h1, Set.mem_univ _⟩
    have hinj : Set.InjOn D {a : Tree | lvl a = β} := by
      intro a ha b hb hab
      have key : ∀ ξ < β, fn a ξ = fn b ξ := by
        intro ξ hξ
        by_cases h1 : fn a ξ = ee β ξ
        · by_cases h2 : fn b ξ = ee β ξ
          · rw [h1, h2]
          · have hmem : ((ξ, fn b ξ) : Ordinal.{0} × ℕ) ∈ D b := ⟨hξ, rfl, h2⟩
            rw [← hab] at hmem
            simpa using hmem.2.1
        · have hmem : ((ξ, fn a ξ) : Ordinal.{0} × ℕ) ∈ D a := ⟨hξ, rfl, h1⟩
          rw [hab] at hmem
          simpa using hmem.2.1.symm
      exact ext' (ha.trans hb.symm) (fun ξ hξ => key ξ (ha ▸ hξ))
    refine Set.countable_of_injective_of_countable_image hinj ?_
    refine Set.Countable.mono (?_ : D '' {a : Tree | lvl a = β} ⊆
      {t : Set (Ordinal.{0} × ℕ) | t.Finite ∧ t ⊆ Set.Iio β ×ˢ (Set.univ : Set ℕ)}) ?_
    · rintro t ⟨a, ha, rfl⟩
      exact ⟨hfin a ha, hsub a⟩
    · exact Set.countable_setOf_finite_subset
        (Set.Countable.prod ((countable_Iio_iff β).2 hβ) Set.countable_univ)
  · refine Set.Countable.mono (?_ : {a : Tree | lvl a = β} ⊆ ∅) Set.countable_empty
    intro a ha
    exact absurd (ha ▸ lvl_lt_omega1 a) hβ

lemma chain_countable (C : Set Tree) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  classical
  by_contra hcount
  have hagree : ∀ a ∈ C, ∀ b ∈ C, ∀ ξ, ξ < lvl a → ξ < lvl b → fn a ξ = fn b ξ := by
    intro a ha b hb ξ h1 h2
    rcases eq_or_ne a b with rfl | hne
    · rfl
    · rcases hC ha hb hne with h | h
      · exact (le_def.1 h).2 ξ h1
      · exact ((le_def.1 h).2 ξ h2).symm
  have hinj : Set.InjOn lvl C := by
    intro a ha b hb hab
    exact ext' hab (fun ξ hξ => hagree a ha b hb ξ hξ (hab ▸ hξ))
  have hBunc : ¬ (lvl '' C).Countable := fun hb =>
    hcount (Set.countable_of_injective_of_countable_image hinj hb)
  obtain ⟨x, hx⟩ : ∃ x : Ordinal.{0} → ℕ, ∀ a ∈ C, ∀ ξ < lvl a, x ξ = fn a ξ := by
    refine ⟨fun ξ => if h : ∃ a, a ∈ C ∧ ξ < lvl a then fn h.choose ξ else 0, ?_⟩
    intro a ha ξ hξ
    have h : ∃ a, a ∈ C ∧ ξ < lvl a := ⟨a, ha, hξ⟩
    show (if h : ∃ a, a ∈ C ∧ ξ < lvl a then fn h.choose ξ else 0) = fn a ξ
    rw [dif_pos h]
    exact hagree _ h.choose_spec.1 _ ha ξ h.choose_spec.2 hξ
  have huniv : ¬ (Set.Iio (ω₁ : Ordinal.{0})).Countable := by
    rw [countable_Iio_iff]; exact lt_irrefl _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ {ξ : Ordinal.{0} | ξ < ω₁ ∧ x ξ = n}.Countable := by
    by_contra hcon
    push_neg at hcon
    refine huniv (Set.Countable.mono (?_ : Set.Iio (ω₁ : Ordinal.{0}) ⊆
      ⋃ n : ℕ, {ξ : Ordinal.{0} | ξ < ω₁ ∧ x ξ = n}) (Set.countable_iUnion hcon))
    intro ξ hξ
    exact Set.mem_iUnion.2 ⟨x ξ, hξ, rfl⟩
  have hinf : {ξ : Ordinal.{0} | ξ < ω₁ ∧ x ξ = n}.Infinite := fun hfin => hn hfin.countable
  set emb := hinf.natEmbedding with hembdef
  set f : ℕ → Ordinal.{0} := fun i => (emb i : Ordinal.{0}) with hfdef
  have hfmem : ∀ i, f i < ω₁ ∧ x (f i) = n := fun i => (emb i).2
  have hδ : (⨆ i : ℕ, f i) < ω₁ := by
    have := Ordinal.iSup_sequence_lt_omega_one f (fun i => by
      rw [Cardinal.ord_aleph]; exact (hfmem i).1)
    rwa [Cardinal.ord_aleph] at this
  set δ : Ordinal.{0} := ⨆ i : ℕ, f i with hδdef
  have hleδ : ∀ i, f i ≤ δ := fun i => Ordinal.le_iSup f i
  obtain ⟨a, haC, haδ⟩ : ∃ a ∈ C, δ < lvl a := by
    by_contra hcon
    push_neg at hcon
    refine hBunc (Set.Countable.mono (?_ : lvl '' C ⊆ insert δ (Set.Iio δ))
      (Set.Countable.insert _ ((countable_Iio_iff δ).2 hδ)))
    rintro _ ⟨b, hb, rfl⟩
    rcases eq_or_lt_of_le (hcon b hb) with h | h
    · exact Set.mem_insert_iff.2 (Or.inl h)
    · exact Set.mem_insert_of_mem _ h
  obtain ⟨_, _, α, hle, hα, hval⟩ := a.2
  have hrange : Set.range f ⊆ {ξ : Ordinal.{0} | ξ < α ∧ ee α ξ = n} := by
    rintro _ ⟨i, rfl⟩
    have h1 : f i < lvl a := lt_of_le_of_lt (hleδ i) haδ
    have h2 : f i < α := lt_of_lt_of_le h1 hle
    refine ⟨h2, ?_⟩
    have h3 : x (f i) = fn a (f i) := hx a haC (f i) h1
    have h4 : fn a (f i) = ee α (f i) := hval (f i) h1
    rw [← h4, ← h3]
    exact (hfmem i).2
  have hfinj : Function.Injective f := by
    intro i j hij
    exact emb.injective (Subtype.ext hij)
  exact (Set.infinite_range_of_injective hfinj) (Set.Finite.subset (ee_fiber_finite hα n) hrange)

end Tree

end Aronszajn

namespace Frontier

open Aronszajn

/-- **There is an Aronszajn tree**: a partial order `T` in which the predecessors of every node
form a well-ordered set of order type `rk a < ω₁` (so `T` is a tree), every level `β < ω₁` is
nonempty (the tree has height `ω₁`), every level is countable, and every chain (in particular
every branch) is countable. -/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (_ : PartialOrder T) (rk : T → Ordinal.{0}),
      (∀ a : T, Nonempty ({b : T // b < a} ≃o Set.Iio (rk a))) ∧
      (∀ a : T, rk a < ω₁) ∧
      (∀ β < ω₁, ∃ a : T, rk a = β) ∧
      (∀ β : Ordinal.{0}, {a : T | rk a = β}.Countable) ∧
      (∀ C : Set T, IsChain (· ≤ ·) C → C.Countable) :=
  ⟨Tree, inferInstance, Tree.lvl, fun a => ⟨Tree.predIso a⟩, Tree.lvl_lt_omega1,
    fun _ hβ => Tree.exists_lvl_eq hβ, Tree.level_countable, Tree.chain_countable⟩

end Frontier

#print axioms Frontier.Aronszajn_tree_exists

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

