import RequestProject.Coherent

/-!
# Existence of an Aronszajn tree

An *Aronszajn tree* is a tree of height `ω₁` all of whose levels are countable and which has
no uncountable branch (equivalently, no uncountable chain).

We formalize a tree as a partial order `T` together with a rank function `rk : T → Ordinal`
whose fibres are the levels; see `Frontier.IsAronszajnTree`.  The main result is
`Frontier.Aronszajn_tree_exists`.
-/

open Ordinal Cardinal Set
open scoped Ordinal

namespace Frontier

/-- `rk` exhibits the partial order `T` as an Aronszajn tree:

* every node has rank a countable ordinal, and the rank strictly increases along the order;
* the set of predecessors of a node is a chain, and contains exactly one element of each
  rank below the rank of the node (so `T` is a tree and `rk` is the height function);
* every level `α < ω₁` is nonempty (the tree has height exactly `ω₁`) and countable;
* every chain (in particular every branch) of `T` is countable.
-/
structure IsAronszajnTree {T : Type 1} [PartialOrder T] (rk : T → Ordinal.{0}) : Prop where
  /-- Every node has countable rank. -/
  rk_lt_omega_one : ∀ t : T, rk t < ω₁
  /-- The rank increases strictly along the order. -/
  rk_mono : ∀ s t : T, s < t → rk s < rk t
  /-- The predecessors of a node form a chain. -/
  pred_chain : ∀ s₁ s₂ t : T, s₁ < t → s₂ < t → s₁ ≤ s₂ ∨ s₂ ≤ s₁
  /-- Every rank below the rank of `t` is realized by a predecessor of `t`. -/
  pred_exists : ∀ t : T, ∀ γ < rk t, ∃ s : T, s < t ∧ rk s = γ
  /-- The tree has height `ω₁`: all levels below `ω₁` are nonempty. -/
  level_nonempty : ∀ α < ω₁, ∃ t : T, rk t = α
  /-- All levels are countable. -/
  level_countable : ∀ α : Ordinal.{0}, {t : T | rk t = α}.Countable
  /-- There is no uncountable chain, in particular no uncountable branch. -/
  chain_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

/-- Truncation of a function at an ordinal. -/
noncomputable def trunc (a : Ordinal.{0}) (f : Ordinal → ℕ) : Ordinal → ℕ := fun γ => if γ < a then f γ else 0

theorem trunc_eq_of_lt {a : Ordinal.{0}} {f : Ordinal → ℕ} {γ : Ordinal} (h : γ < a) :
    trunc a f γ = f γ := if_pos h

theorem trunc_eq_zero {a : Ordinal.{0}} {f : Ordinal → ℕ} {γ : Ordinal} (h : a ≤ γ) :
    trunc a f γ = 0 := if_neg (not_lt.2 h)

/-- A node of the tree: a level `lvl < ω₁` together with an injection of `Set.Iio lvl` into `ℕ`
which is a finite modification of `cf lvl`. -/
structure Node where
  /-- The level of the node. -/
  lvl : Ordinal.{0}
  /-- The function attached to the node. -/
  val : Ordinal → ℕ
  /-- The level is a countable ordinal. -/
  lvl_lt : lvl < ω₁
  /-- The function is injective below the level. -/
  inj : Set.InjOn val (Set.Iio lvl)
  /-- The function is a finite modification of `cf lvl`. -/
  aeq : AEq lvl val (cf lvl)
  /-- Normalization: the function vanishes above the level. -/
  norm : ∀ γ, lvl ≤ γ → val γ = 0

namespace Node

theorem ext' {s t : Node} (hl : s.lvl = t.lvl) (hv : ∀ γ, γ < s.lvl → s.val γ = t.val γ) :
    s = t := by
  obtain ⟨l₁, v₁, _, _, _, n₁⟩ := s
  obtain ⟨l₂, v₂, _, _, _, n₂⟩ := t
  simp only at hl hv
  subst hl
  have : v₁ = v₂ := by
    funext γ
    by_cases h : γ < l₁
    · exact hv γ h
    · rw [n₁ γ (not_lt.1 h), n₂ γ (not_lt.1 h)]
  subst this
  rfl

instance : PartialOrder Node where
  le s t := s.lvl ≤ t.lvl ∧ ∀ γ, γ < s.lvl → s.val γ = t.val γ
  le_refl s := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans s t u h₁ h₂ := ⟨h₁.1.trans h₂.1, fun γ hγ =>
    (h₁.2 γ hγ).trans (h₂.2 γ (lt_of_lt_of_le hγ h₁.1))⟩
  le_antisymm s t h₁ h₂ := ext' (le_antisymm h₁.1 h₂.1) h₁.2

theorem le_def {s t : Node} : s ≤ t ↔ s.lvl ≤ t.lvl ∧ ∀ γ, γ < s.lvl → s.val γ = t.val γ :=
  Iff.rfl

theorem lt_iff {s t : Node} : s < t ↔ s.lvl < t.lvl ∧ ∀ γ, γ < s.lvl → s.val γ = t.val γ := by
  constructor
  · intro h
    refine ⟨lt_of_le_of_ne h.le.1 ?_, h.le.2⟩
    intro he
    exact absurd (ext' he h.le.2) (ne_of_lt h)
  · intro h
    refine lt_of_le_of_ne ⟨h.1.le, h.2⟩ ?_
    rintro rfl
    exact lt_irrefl _ h.1

/-- The truncation of a node at a smaller level is again a node. -/
noncomputable def truncNode (t : Node) (a : Ordinal.{0}) (ha : a ≤ t.lvl) : Node where
  lvl := a
  val := trunc a t.val
  lvl_lt := lt_of_le_of_lt ha t.lvl_lt
  inj := by
    intro x hx y hy hxy
    rw [trunc_eq_of_lt hx, trunc_eq_of_lt hy] at hxy
    exact t.inj (lt_of_lt_of_le hx ha) (lt_of_lt_of_le hy ha) hxy
  aeq := by
    have h1 : AEq a t.val (cf t.lvl) := t.aeq.mono ha
    have h2 : AEq a (cf t.lvl) (cf a) := by
      rcases lt_or_eq_of_le ha with h | h
      · exact cf_aeq t.lvl_lt h
      · subst h; exact AEq.refl _ _
    have h3 : AEq a t.val (cf a) := h1.trans h2
    refine h3.subset ?_
    rintro γ ⟨hγ, hne⟩
    refine ⟨hγ, ?_⟩
    rwa [trunc_eq_of_lt hγ] at hne
  norm := fun γ hγ => trunc_eq_zero hγ

theorem truncNode_le (t : Node) (a : Ordinal.{0}) (ha : a ≤ t.lvl) : truncNode t a ha ≤ t :=
  ⟨ha, fun _ hγ => trunc_eq_of_lt hγ⟩

end Node

/-- Every countable level of the tree is nonempty. -/
theorem exists_node_of_lvl (α : Ordinal.{0}) (hα : α < ω₁) : ∃ t : Node, t.lvl = α := by
  refine ⟨⟨α, trunc α (cf α), hα, ?_, ?_, fun γ hγ => trunc_eq_zero hγ⟩, rfl⟩
  · intro x hx y hy hxy
    rw [trunc_eq_of_lt hx, trunc_eq_of_lt hy] at hxy
    exact cf_injOn hα hx hy hxy
  · refine Set.Finite.subset (Set.finite_empty) ?_
    rintro γ ⟨hγ, hne⟩
    exact absurd (trunc_eq_of_lt hγ) hne

/-- Each level of the tree is countable. -/
theorem level_countable (α : Ordinal.{0}) : {t : Node | t.lvl = α}.Countable := by
  classical
  by_cases hα : α < ω₁
  swap
  · convert Set.countable_empty
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hα (h ▸ t.lvl_lt)
  set Φ : Node → Set (Ordinal × ℕ) :=
    fun t => {p | p.1 < α ∧ t.val p.1 ≠ cf α p.1 ∧ p.2 = t.val p.1} with hΦ
  set W : Set (Set (Ordinal × ℕ)) :=
    {s | s.Finite ∧ s ⊆ (Set.Iio α ×ˢ (Set.univ : Set ℕ))} with hW
  have hWc : W.Countable :=
    Set.countable_setOf_finite_subset
      ((countable_Iio_of_lt_omega_one hα).prod Set.countable_univ)
  obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 hWc
  refine Set.countable_iff_exists_injOn.2 ⟨fun t => j (Φ t), ?_⟩
  have hmem : ∀ t : Node, t.lvl = α → Φ t ∈ W := by
    intro t ht
    constructor
    · refine Set.Finite.subset (Set.Finite.image (fun γ => (γ, t.val γ)) (ht ▸ t.aeq)) ?_
      rintro ⟨γ, m⟩ ⟨h1, h2, h3⟩
      exact ⟨γ, ⟨h1, h2⟩, by simpa using h3.symm⟩
    · rintro ⟨γ, m⟩ ⟨h1, -, -⟩
      exact ⟨h1, Set.mem_univ _⟩
  intro t ht t' ht' hjj
  have hΦeq : Φ t = Φ t' := hj (hmem t ht) (hmem t' ht') hjj
  refine Node.ext' (ht.trans ht'.symm) ?_
  intro γ hγ
  rw [ht] at hγ
  by_cases hd : t.val γ = cf α γ
  · by_cases hd' : t'.val γ = cf α γ
    · rw [hd, hd']
    · have hm : (γ, t'.val γ) ∈ Φ t' := ⟨hγ, hd', rfl⟩
      rw [← hΦeq] at hm
      simpa using hm.2.2.symm
  · have hm : (γ, t.val γ) ∈ Φ t := ⟨hγ, hd, rfl⟩
    rw [hΦeq] at hm
    simpa using hm.2.2

/-- Every chain of the tree is countable; in particular there is no uncountable branch. -/
theorem chain_countable (C : Set Node) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  classical
  by_contra hunc
  have hinjlvl : Set.InjOn Node.lvl C := by
    intro s hs t ht hst
    rcases eq_or_ne s t with rfl | hne
    · rfl
    · rcases hC hs ht hne with h | h
      · exact Node.ext' hst h.2
      · exact (Node.ext' hst.symm h.2).symm
  have hunb : ∀ γ : Ordinal, γ < ω₁ → ∃ t : Node, t ∈ C ∧ γ < t.lvl := by
    intro γ hγ
    by_contra hcon
    push_neg at hcon
    apply hunc
    have hIic : (Set.Iic γ).Countable := by
      refine Set.Countable.mono ?_ ((countable_Iio_of_lt_omega_one hγ).union
        (Set.countable_singleton γ))
      intro x hx
      rcases lt_or_eq_of_le (Set.mem_Iic.1 hx) with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hcnt : (Node.lvl '' C).Countable := by
      refine hIic.mono ?_
      rintro v ⟨t, htC, rfl⟩
      exact hcon t htC
    obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 hcnt
    exact Set.countable_iff_exists_injOn.2 ⟨fun t => j t.lvl, fun s hs t ht h =>
      hinjlvl hs ht (hj (Set.mem_image_of_mem _ hs) (Set.mem_image_of_mem _ ht) h)⟩
  set F : Ordinal → ℕ :=
    fun γ => if h : ∃ t : Node, t ∈ C ∧ γ < t.lvl then h.choose.val γ else 0 with hF
  have hFeq : ∀ t : Node, t ∈ C → ∀ γ, γ < t.lvl → F γ = t.val γ := by
    intro t htC γ hγ
    have hex : ∃ t : Node, t ∈ C ∧ γ < t.lvl := ⟨t, htC, hγ⟩
    have h0 : F γ = if h : ∃ t : Node, t ∈ C ∧ γ < t.lvl then h.choose.val γ else 0 := rfl
    rw [h0, dif_pos hex]
    obtain ⟨hc1, hc2⟩ := hex.choose_spec
    rcases eq_or_ne hex.choose t with h | hne
    · rw [h]
    · rcases hC hc1 htC hne with h | h
      · exact h.2 γ hc2
      · exact (h.2 γ hγ).symm
  apply not_countable_Iio_omega_one
  refine Set.countable_iff_exists_injOn.2 ⟨F, ?_⟩
  intro x hx y hy hxy
  obtain ⟨t1, ht1, hx1⟩ := hunb x hx
  obtain ⟨t2, ht2, hy2⟩ := hunb y hy
  rcases eq_or_ne t1 t2 with rfl | hne
  · rw [hFeq t1 ht1 x hx1, hFeq t1 ht1 y hy2] at hxy
    exact t1.inj hx1 hy2 hxy
  · rcases hC ht1 ht2 hne with h | h
    · have hx2 : x < t2.lvl := lt_of_lt_of_le hx1 h.1
      rw [hFeq t2 ht2 x hx2, hFeq t2 ht2 y hy2] at hxy
      exact t2.inj hx2 hy2 hxy
    · have hy1 : y < t1.lvl := lt_of_lt_of_le hy2 h.1
      rw [hFeq t1 ht1 x hx1, hFeq t1 ht1 y hy1] at hxy
      exact t1.inj hx1 hy1 hxy

/-- **There exists an Aronszajn tree**: a tree of height `ω₁` with all levels countable and
with no uncountable branch. -/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (inst : PartialOrder T) (rk : T → Ordinal.{0}), @IsAronszajnTree T inst rk := by
  refine ⟨Node, inferInstance, Node.lvl, ?_⟩
  refine ⟨fun t => t.lvl_lt, fun s t h => (Node.lt_iff.1 h).1, ?_, ?_,
    fun α hα => exists_node_of_lvl α hα, level_countable, chain_countable⟩
  · intro s₁ s₂ t h₁ h₂
    rcases le_total s₁.lvl s₂.lvl with h | h
    · exact Or.inl ⟨h, fun γ hγ =>
        ((Node.lt_iff.1 h₁).2 γ hγ).trans ((Node.lt_iff.1 h₂).2 γ (lt_of_lt_of_le hγ h)).symm⟩
    · exact Or.inr ⟨h, fun γ hγ =>
        ((Node.lt_iff.1 h₂).2 γ hγ).trans ((Node.lt_iff.1 h₁).2 γ (lt_of_lt_of_le hγ h)).symm⟩
  · intro t γ hγ
    refine ⟨Node.truncNode t γ hγ.le, ?_, rfl⟩
    exact Node.lt_iff.2 ⟨hγ, fun δ hδ => trunc_eq_of_lt hδ⟩

end Frontier

import Mathlib

/-!
# A coherent sequence of almost injections

For every countable ordinal `a` we construct a function `cf a : Ordinal → ℕ` which is
injective on `Set.Iio a`, whose range on `Set.Iio a` has infinite complement, and which
is *coherent*: for `b < a`, the functions `cf a` and `cf b` agree below `b` outside a
finite set.

This is the standard ingredient in the construction of an Aronszajn tree.
-/

open Ordinal Cardinal Set
open scoped Ordinal

namespace Frontier

/-! ### Countability of initial segments -/

theorem countable_Iio_of_lt_omega_one {a : Ordinal.{0}} (h : a < ω₁) :
    (Set.Iio a).Countable := by
  rw [countable_iff_lt_aleph_one, mk_Iio_ordinal]
  have h2 : a.card < ℵ₁ := by rw [← Cardinal.lt_ord, ord_aleph]; exact h
  have h3 := Cardinal.lift_lt.mpr h2
  simpa using h3

theorem not_countable_Iio_omega_one : ¬ (Set.Iio (ω₁ : Ordinal.{0})).Countable := by
  intro h
  rw [countable_iff_lt_aleph_one, mk_Iio_ordinal] at h
  rw [show (ℵ₁ : Cardinal.{1}) = Cardinal.lift.{1, 0} ℵ₁ by simp, Cardinal.lift_lt,
    ← Cardinal.lt_ord, ord_aleph] at h
  exact lt_irrefl _ h

/-! ### Almost equality -/

/-- `AEq a f g` means that `f` and `g` agree below `a` outside a finite set. -/
def AEq (a : Ordinal.{0}) (f g : Ordinal → ℕ) : Prop := {b | b < a ∧ f b ≠ g b}.Finite

theorem AEq.refl (a : Ordinal.{0}) (f : Ordinal → ℕ) : AEq a f f := by
  simp [AEq]

theorem AEq.symm {a : Ordinal.{0}} {f g : Ordinal → ℕ} (h : AEq a f g) : AEq a g f := by
  refine h.subset ?_
  rintro b ⟨hb, hne⟩
  exact ⟨hb, fun h => hne h.symm⟩

theorem AEq.trans {a : Ordinal.{0}} {f g h : Ordinal → ℕ} (h₁ : AEq a f g) (h₂ : AEq a g h) :
    AEq a f h := by
  refine ((h₁.union h₂).subset ?_)
  rintro b ⟨hb, hne⟩
  by_cases hfg : f b = g b
  · exact Or.inr ⟨hb, by rw [← hfg]; exact hne⟩
  · exact Or.inl ⟨hb, hfg⟩

theorem AEq.mono {a b : Ordinal.{0}} {f g : Ordinal → ℕ} (hba : b ≤ a) (h : AEq a f g) :
    AEq b f g :=
  h.subset fun _ hc => ⟨lt_of_lt_of_le hc.1 hba, hc.2⟩

/-! ### The repair lemma -/

/-- If `h` is injective below `a` off a finite set `S`, avoids the set `K` there, and its range
misses infinitely much even after adding `K`, then `h` can be modified on `S` only, so as to
become injective on all of `Set.Iio a`, still avoid `K`, and still have infinite co-range. -/
theorem repair (a : Ordinal.{0}) (h : Ordinal → ℕ) (S : Set Ordinal) (K : Set ℕ)
    (hS : S.Finite) (hinj : Set.InjOn h (Set.Iio a \ S))
    (hK : Disjoint (h '' (Set.Iio a \ S)) K)
    (hinf : ((h '' (Set.Iio a \ S)) ∪ K)ᶜ.Infinite) :
    ∃ h' : Ordinal → ℕ, (∀ γ, γ ∉ S → h' γ = h γ) ∧ Set.InjOn h' (Set.Iio a) ∧
      Disjoint (h' '' Set.Iio a) K ∧ ((h' '' Set.Iio a)ᶜ).Infinite := by
  classical
  set C : Set ℕ := ((h '' (Set.Iio a \ S)) ∪ K)ᶜ with hCdef
  obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 hS.countable
  set e : ℕ ↪ C := hinf.natEmbedding _ with he
  set ι : Ordinal → ℕ := fun γ => (e (j γ) : ℕ) with hιdef
  have hιC : ∀ γ, ι γ ∈ C := fun γ => (e (j γ)).2
  have hιinj : Set.InjOn ι S := by
    intro x hx y hy hxy
    have : e (j x) = e (j y) := Subtype.ext hxy
    exact hj hx hy (e.injective this)
  set h' : Ordinal → ℕ := fun γ => if γ ∈ S then ι γ else h γ with hh'
  have hoff : ∀ γ, γ ∉ S → h' γ = h γ := fun γ hγ => if_neg hγ
  have hon : ∀ γ, γ ∈ S → h' γ = ι γ := fun γ hγ => if_pos hγ
  have himg : h' '' Set.Iio a ⊆ (h '' (Set.Iio a \ S)) ∪ ι '' S := by
    rintro v ⟨γ, hγ, rfl⟩
    by_cases hs : γ ∈ S
    · exact Or.inr ⟨γ, hs, (hon γ hs).symm ▸ rfl⟩
    · exact Or.inl ⟨γ, ⟨hγ, hs⟩, (hoff γ hs).symm ▸ rfl⟩
  refine ⟨h', hoff, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    by_cases hxs : x ∈ S <;> by_cases hys : y ∈ S
    · rw [hon x hxs, hon y hys] at hxy; exact hιinj hxs hys hxy
    · rw [hon x hxs, hoff y hys] at hxy
      have hc := hιC x
      rw [hxy] at hc
      have hmem : y ∈ Set.Iio a \ S := ⟨hy, hys⟩
      exact absurd (Set.mem_union_left K (Set.mem_image_of_mem h hmem)) hc
    · rw [hoff x hxs, hon y hys] at hxy
      have hc := hιC y
      rw [← hxy] at hc
      have hmem : x ∈ Set.Iio a \ S := ⟨hx, hxs⟩
      exact absurd (Set.mem_union_left K (Set.mem_image_of_mem h hmem)) hc
    · rw [hoff x hxs, hoff y hys] at hxy; exact hinj ⟨hx, hxs⟩ ⟨hy, hys⟩ hxy
  · rw [Set.disjoint_left]
    intro v hv hvK
    rcases himg hv with hv1 | ⟨γ, hγ, rfl⟩
    · exact (Set.disjoint_left.1 hK hv1) hvK
    · exact (hιC γ) (Or.inr hvK)
  · refine Set.Infinite.mono ?_ (hinf.diff (hS.image ι))
    intro v hv
    simp only [Set.mem_compl_iff]
    intro hv2
    rcases himg hv2 with h1 | h2
    · exact hv.1 (Or.inl h1)
    · exact hv.2 h2

/-! ### The coherent sequence -/

open Classical in
/-- A coherent sequence of almost injections, defined by transfinite recursion. -/
noncomputable def cf (a : Ordinal.{0}) : Ordinal → ℕ :=
  if h : ∃ E : Ordinal → ℕ, Set.InjOn E (Set.Iio a) ∧ ((E '' Set.Iio a)ᶜ).Infinite ∧
      ∀ b, ∀ _ : b < a, AEq b E (cf b) then h.choose else fun _ => 0
termination_by a
decreasing_by all_goals assumption

/-- The properties we require of `cf a`. -/
def Good (a : Ordinal.{0}) (E : Ordinal → ℕ) : Prop :=
  Set.InjOn E (Set.Iio a) ∧ ((E '' Set.Iio a)ᶜ).Infinite ∧ ∀ b, ∀ _ : b < a, AEq b E (cf b)

theorem cf_spec {a : Ordinal.{0}} (h : ∃ E : Ordinal → ℕ, Good a E) : Good a (cf a) := by
  have h' : ∃ E : Ordinal → ℕ, Set.InjOn E (Set.Iio a) ∧ ((E '' Set.Iio a)ᶜ).Infinite ∧
      ∀ b, ∀ _ : b < a, AEq b E (cf b) := h
  rw [Good, cf, dif_pos h']
  exact h'.choose_spec

theorem Iio_zero_ordinal : Set.Iio (0 : Ordinal.{0}) = ∅ := by
  ext x; simp

/-- The zero stage. -/
theorem exists_good_zero : ∃ E : Ordinal → ℕ, Good (0 : Ordinal.{0}) E := by
  refine ⟨fun _ => 0, ?_, ?_, ?_⟩
  · rw [Iio_zero_ordinal]; exact Set.injOn_empty _
  · rw [Iio_zero_ordinal]; simpa using Set.infinite_univ
  · intro b hb; exact absurd hb (by simp)

/-- The successor stage. -/
theorem exists_good_succ (b : Ordinal.{0}) (hb : Good b (cf b)) :
    ∃ E : Ordinal → ℕ, Good (Order.succ b) E := by
  have hset : Set.Iio (Order.succ b) \ {b} = Set.Iio b := by
    ext x
    simp only [Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff, Order.lt_succ_iff]
    constructor
    · rintro ⟨h1, h2⟩; exact lt_of_le_of_ne h1 h2
    · intro h; exact ⟨h.le, ne_of_lt h⟩
  obtain ⟨hinj, hinf, hcoh⟩ := hb
  obtain ⟨E, hEoff, hEinj, -, hEinf⟩ :=
    repair (Order.succ b) (cf b) {b} ∅ (Set.finite_singleton b)
      (by rw [hset]; exact hinj) (by simp)
      (by rw [hset]; simpa using hinf)
  refine ⟨E, hEinj, hEinf, ?_⟩
  intro c hc
  have hcb : c ≤ b := Order.lt_succ_iff.1 hc
  have h1 : AEq c E (cf b) := by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro γ ⟨hγ, hne⟩
    exact absurd (hEoff γ (by simp; exact ne_of_lt (lt_of_lt_of_le hγ hcb))) hne
  refine h1.trans ?_
  rcases lt_or_eq_of_le hcb with h | h
  · exact hcoh c h
  · subst h; exact AEq.refl _ _

/-! ### The limit stage -/

/-- A countable limit ordinal is the supremum of a strictly increasing `ω`-sequence. -/
theorem exists_ladder (a : Ordinal.{0}) (ha0 : a ≠ 0) (hcnt : (Set.Iio a).Countable)
    (hlim : ∀ b, b < a → Order.succ b < a) :
    ∃ al : ℕ → Ordinal.{0}, al 0 = 0 ∧ StrictMono al ∧ (∀ n, al n < a) ∧
      ∀ b, b < a → ∃ n, b < al n := by
  have hne : (Set.Iio a).Nonempty := ⟨0, pos_of_ne_zero ha0⟩
  obtain ⟨s, hs⟩ := hcnt.exists_eq_range hne
  set al : ℕ → Ordinal.{0} := fun n => Nat.rec (0 : Ordinal.{0})
    (fun n x => max (Order.succ x) (Order.succ (s n))) n with hal
  have halsucc : ∀ n, al (n + 1) = max (Order.succ (al n)) (Order.succ (s n)) := fun n => rfl
  have hsa : ∀ n, s n < a := by
    intro n
    have : s n ∈ Set.Iio a := by rw [hs]; exact ⟨n, rfl⟩
    exact this
  have hlt : ∀ n, al n < a := by
    intro n
    induction n with
    | zero => exact pos_of_ne_zero ha0
    | succ n ih =>
      rw [halsucc]
      exact max_lt (hlim _ ih) (hlim _ (hsa n))
  have hmono : StrictMono al := strictMono_nat_of_lt_succ (fun n => by
    rw [halsucc]
    exact lt_of_lt_of_le (Order.lt_succ (al n)) (le_max_left _ _))
  refine ⟨al, rfl, hmono, hlt, ?_⟩
  intro b hb
  have : b ∈ Set.range s := by rw [← hs]; exact hb
  obtain ⟨n, rfl⟩ := this
  exact ⟨n + 1, by rw [halsucc]; exact lt_of_lt_of_le (Order.lt_succ (s n)) (le_max_right _ _)⟩

/-- The invariant maintained along the `ω`-chain used at a limit stage: `f` is injective below
`al n` with infinite co-range, is a finite modification of `cf (al n)`, and avoids the finite
set `K`, which has at least `n` elements. -/
def LimInv (al : ℕ → Ordinal.{0}) (n : ℕ) (f : Ordinal → ℕ) (K : Finset ℕ) : Prop :=
  Set.InjOn f (Set.Iio (al n)) ∧ ((f '' Set.Iio (al n))ᶜ).Infinite ∧
    AEq (al n) f (cf (al n)) ∧ Disjoint (f '' Set.Iio (al n)) (↑K : Set ℕ) ∧ n ≤ K.card

/-- One step along the `ω`-chain at a limit stage. -/
theorem lim_step (al : ℕ → Ordinal.{0}) (a : Ordinal.{0}) (hlta : ∀ n, al n < a)
    (hmono : StrictMono al) (ih : ∀ b, b < a → Good b (cf b))
    (n : ℕ) (f : Ordinal → ℕ) (K : Finset ℕ) (hinv : LimInv al n f K) :
    ∃ (f' : Ordinal → ℕ) (K' : Finset ℕ), LimInv al (n + 1) f' K' ∧
      (∀ γ, γ < al n → f' γ = f γ) ∧ K ⊆ K' := by
  classical
  obtain ⟨hfinj, hfinf, hfaeq, hfdisj, hfcard⟩ := hinv
  set A := al n with hA
  set B := al (n + 1) with hB
  have hAB : A < B := hmono (Nat.lt_succ_self n)
  obtain ⟨hginj, hginf, hgcoh⟩ := ih B (hlta (n + 1))
  set g := cf B with hg
  have hfg : AEq A f g := hfaeq.trans (hgcoh A hAB).symm
  set D : Set Ordinal := {γ | γ < A ∧ f γ ≠ g γ} with hD
  have hDfin : D.Finite := hfg
  set hfun : Ordinal → ℕ := fun γ => if γ < A then f γ else g γ with hhfun
  have hfun_lt : ∀ γ, γ < A → hfun γ = f γ := fun γ h => if_pos h
  have hfun_ge : ∀ γ, A ≤ γ → hfun γ = g γ := fun γ h => if_neg (not_lt.2 h)
  set S : Set Ordinal := {γ | A ≤ γ ∧ γ < B ∧ (g γ ∈ f '' D ∨ g γ ∈ (↑K : Set ℕ))} with hS
  have hSfin : S.Finite := by
    have hginjS : Set.InjOn g S := fun x hx y hy hxy => hginj hx.2.1 hy.2.1 hxy
    refine Set.Finite.of_finite_image ?_ hginjS
    refine Set.Finite.subset ((hDfin.image f).union K.finite_toSet) ?_
    rintro v ⟨γ, hγ, rfl⟩
    exact hγ.2.2
  have hinj' : Set.InjOn hfun (Set.Iio B \ S) := by
    intro x hx y hy hxy
    rcases lt_or_ge x A with hxA | hxA <;> rcases lt_or_ge y A with hyA | hyA
    · rw [hfun_lt x hxA, hfun_lt y hyA] at hxy
      exact hfinj hxA hyA hxy
    · rw [hfun_lt x hxA, hfun_ge y hyA] at hxy
      by_cases hxD : x ∈ D
      · exact absurd (⟨hyA, hy.1, Or.inl ⟨x, hxD, hxy⟩⟩ : y ∈ S) hy.2
      · have hfx : f x = g x := by by_contra hc; exact hxD ⟨hxA, hc⟩
        rw [hfx] at hxy
        exact hginj (hxA.trans hAB) hy.1 hxy
    · rw [hfun_ge x hxA, hfun_lt y hyA] at hxy
      by_cases hyD : y ∈ D
      · exact absurd (⟨hxA, hx.1, Or.inl ⟨y, hyD, hxy.symm⟩⟩ : x ∈ S) hx.2
      · have hfy : f y = g y := by by_contra hc; exact hyD ⟨hyA, hc⟩
        rw [hfy] at hxy
        exact hginj hx.1 (hyA.trans hAB) hxy
    · rw [hfun_ge x hxA, hfun_ge y hyA] at hxy
      exact hginj hx.1 hy.1 hxy
  have hdisj' : Disjoint (hfun '' (Set.Iio B \ S)) (↑K : Set ℕ) := by
    rw [Set.disjoint_left]
    rintro v ⟨γ, hγ, rfl⟩ hvK
    rcases lt_or_ge γ A with h | h
    · rw [hfun_lt γ h] at hvK
      exact (Set.disjoint_left.1 hfdisj (Set.mem_image_of_mem f h)) hvK
    · rw [hfun_ge γ h] at hvK
      exact hγ.2 ⟨h, hγ.1, Or.inr hvK⟩
  have hsub : hfun '' (Set.Iio B \ S) ⊆ (g '' Set.Iio B) ∪ f '' D := by
    rintro v ⟨γ, hγ, rfl⟩
    rcases lt_or_ge γ A with h | h
    · rw [hfun_lt γ h]
      by_cases hd : γ ∈ D
      · exact Or.inr ⟨γ, hd, rfl⟩
      · have hfe : f γ = g γ := by by_contra hc; exact hd ⟨h, hc⟩
        rw [hfe]; exact Or.inl ⟨γ, h.trans hAB, rfl⟩
    · rw [hfun_ge γ h]; exact Or.inl ⟨γ, hγ.1, rfl⟩
  have hinf' : ((hfun '' (Set.Iio B \ S)) ∪ (↑K : Set ℕ))ᶜ.Infinite := by
    refine Set.Infinite.mono ?_ (hginf.diff ((hDfin.image f).union K.finite_toSet))
    intro v hv
    simp only [Set.mem_compl_iff, Set.mem_union]
    rintro (h1 | h2)
    · rcases hsub h1 with h | h
      · exact hv.1 h
      · exact hv.2 (Or.inl h)
    · exact hv.2 (Or.inr h2)
  obtain ⟨f', hf'off, hf'inj, hf'disj, hf'inf⟩ := repair B hfun S (↑K) hSfin hinj' hdisj' hinf'
  obtain ⟨k, hk⟩ := (hf'inf.diff K.finite_toSet).nonempty
  have hkK : k ∉ K := fun hc => hk.2 (Finset.mem_coe.2 hc)
  refine ⟨f', insert k K, ⟨hf'inj, hf'inf, ?_, ?_, ?_⟩, ?_, Finset.subset_insert k K⟩
  · refine Set.Finite.subset (hDfin.union hSfin) ?_
    rintro γ ⟨hγB, hne⟩
    by_cases hs : γ ∈ S
    · exact Or.inr hs
    · rw [hf'off γ hs] at hne
      rcases lt_or_ge γ A with h | h
      · rw [hfun_lt γ h] at hne; exact Or.inl ⟨h, hne⟩
      · rw [hfun_ge γ h] at hne; exact absurd rfl hne
  · rw [Finset.coe_insert, Set.disjoint_insert_right]
    exact ⟨hk.1, hf'disj⟩
  · rw [Finset.card_insert_of_notMem hkK]
    omega
  · intro γ hγ
    have hnS : γ ∉ S := fun hc => absurd hc.1 (not_le.2 hγ)
    rw [hf'off γ hnS, hfun_lt γ hγ]

/-- The limit stage. -/
theorem exists_good_limit (a : Ordinal.{0}) (ha : a < ω₁) (ha0 : a ≠ 0)
    (hlim : ∀ b, b < a → Order.succ b < a) (ih : ∀ b, b < a → Good b (cf b)) :
    ∃ E : Ordinal → ℕ, Good a E := by
  classical
  obtain ⟨al, hal0, hmono, hlta, hcof⟩ :=
    exists_ladder a ha0 (countable_Iio_of_lt_omega_one ha) hlim
  have hIio0 : Set.Iio (al 0) = (∅ : Set Ordinal) := by rw [hal0]; exact Iio_zero_ordinal
  have hinv0 : LimInv al 0 (fun _ => 0) ∅ := by
    refine ⟨?_, ?_, ?_, ?_, le_rfl⟩
    · rw [hIio0]; exact Set.injOn_empty _
    · rw [hIio0]; simpa using Set.infinite_univ
    · refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγ, -⟩
      rw [hal0] at hγ
      exact absurd hγ (by simp)
    · simp
  have step : ∀ (n : ℕ) (p : (Ordinal → ℕ) × Finset ℕ), ∃ q : (Ordinal → ℕ) × Finset ℕ,
      LimInv al n p.1 p.2 → (LimInv al (n + 1) q.1 q.2 ∧ (∀ γ, γ < al n → q.1 γ = p.1 γ) ∧
        p.2 ⊆ q.2) := by
    intro n p
    by_cases hp : LimInv al n p.1 p.2
    · obtain ⟨f', K', h1, h2, h3⟩ := lim_step al a hlta hmono ih n p.1 p.2 hp
      exact ⟨(f', K'), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨p, fun hc => absurd hc hp⟩
  choose G hG using step
  set P : ℕ → (Ordinal → ℕ) × Finset ℕ :=
    fun n => Nat.rec ((fun _ => 0), (∅ : Finset ℕ)) (fun n p => G n p) n with hP
  have hPs : ∀ n, P (n + 1) = G n (P n) := fun n => rfl
  have hinvn : ∀ n, LimInv al n (P n).1 (P n).2 := by
    intro n
    induction n with
    | zero => exact hinv0
    | succ n ihn => rw [hPs]; exact (hG n (P n) ihn).1
  have hagree : ∀ n γ, γ < al n → (P (n + 1)).1 γ = (P n).1 γ := by
    intro n γ hγ
    rw [hPs]
    exact (hG n (P n) (hinvn n)).2.1 γ hγ
  have hKmono : ∀ n, (P n).2 ⊆ (P (n + 1)).2 := by
    intro n
    rw [hPs]
    exact (hG n (P n) (hinvn n)).2.2
  have hagree' : ∀ m n, m ≤ n → ∀ γ, γ < al m → (P n).1 γ = (P m).1 γ := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro γ _; rfl
    | succ n hn ihn =>
      intro γ hγ
      rw [hagree n γ (lt_of_lt_of_le hγ (hmono.monotone hn)), ihn γ hγ]
  have hKmono' : ∀ m n, m ≤ n → (P m).2 ⊆ (P n).2 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hn ihn => exact ihn.trans (hKmono n)
  set E : Ordinal → ℕ := fun γ => if h : ∃ n, γ < al n then (P (Nat.find h)).1 γ else 0 with hE
  have hEeq : ∀ n γ, γ < al n → E γ = (P n).1 γ := by
    intro n γ hγ
    have hex : ∃ n, γ < al n := ⟨n, hγ⟩
    have h0 : E γ = if h : ∃ n, γ < al n then (P (Nat.find h)).1 γ else 0 := rfl
    rw [h0, dif_pos hex]
    exact (hagree' (Nat.find hex) n (Nat.find_le hγ) γ (Nat.find_spec hex)).symm
  refine ⟨E, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨n1, hn1⟩ := hcof x hx
    obtain ⟨n2, hn2⟩ := hcof y hy
    have hxN : x < al (max n1 n2) := lt_of_lt_of_le hn1 (hmono.monotone (le_max_left n1 n2))
    have hyN : y < al (max n1 n2) := lt_of_lt_of_le hn2 (hmono.monotone (le_max_right n1 n2))
    rw [hEeq _ x hxN, hEeq _ y hyN] at hxy
    exact (hinvn _).1 hxN hyN hxy
  · have hUsub : (⋃ n, (↑((P n).2) : Set ℕ)) ⊆ (E '' Set.Iio a)ᶜ := by
      intro v hv
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hv
      intro hcon
      obtain ⟨γ, hγ, hγv⟩ := hcon
      obtain ⟨m, hm⟩ := hcof γ hγ
      have hγN : γ < al (max m n) := lt_of_lt_of_le hm (hmono.monotone (le_max_left m n))
      have hmem : (P (max m n)).1 γ ∈ (P (max m n)).1 '' Set.Iio (al (max m n)) := ⟨γ, hγN, rfl⟩
      have hdis := (hinvn (max m n)).2.2.2.1
      refine (Set.disjoint_left.1 hdis hmem) ?_
      have hv2 : v = (P (max m n)).1 γ := by rw [← hγv, hEeq _ γ hγN]
      rw [← hv2]
      exact Finset.mem_coe.2 (hKmono' n (max m n) (le_max_right m n) (Finset.mem_coe.1 hn))
    refine Set.Infinite.mono hUsub ?_
    intro hfin
    have hcard : ∀ n, n ≤ hfin.toFinset.card := by
      intro n
      refine le_trans (hinvn n).2.2.2.2 (Finset.card_le_card ?_)
      intro x hx
      exact hfin.mem_toFinset.2 (Set.mem_iUnion.2 ⟨n, Finset.mem_coe.2 hx⟩)
    exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
  · intro b hb
    obtain ⟨n, hn⟩ := hcof b hb
    have h1 : AEq b E (P n).1 := by
      refine Set.Finite.subset Set.finite_empty ?_
      rintro γ ⟨hγ, hne⟩
      exact absurd (hEeq n γ (hγ.trans hn)) hne
    have h2 : AEq b (P n).1 (cf (al n)) := (hinvn n).2.2.1.mono hn.le
    have h3 : AEq b (cf (al n)) (cf b) := (ih (al n) (hlta n)).2.2 b hn
    exact (h1.trans h2).trans h3

/-- Every countable stage of the coherent sequence has the required properties. -/
theorem cf_good : ∀ a : Ordinal.{0}, a < ω₁ → Good a (cf a) := by
  intro a
  induction a using Ordinal.induction with
  | _ a IH =>
    intro ha
    apply cf_spec
    rcases eq_or_ne a 0 with rfl | h0
    · exact exists_good_zero
    by_cases hs : ∃ b, a = Order.succ b
    · obtain ⟨b, rfl⟩ := hs
      have hb : b < Order.succ b := Order.lt_succ b
      exact exists_good_succ b (IH b hb (hb.trans ha))
    · refine exists_good_limit a ha h0 ?_ (fun b hb => IH b hb (hb.trans ha))
      intro b hb
      rcases lt_or_eq_of_le (Order.succ_le_of_lt hb) with h | h
      · exact h
      · exact absurd ⟨b, h.symm⟩ hs

theorem cf_injOn {a : Ordinal.{0}} (ha : a < ω₁) : Set.InjOn (cf a) (Set.Iio a) :=
  (cf_good a ha).1

theorem cf_aeq {a b : Ordinal.{0}} (ha : a < ω₁) (hb : b < a) : AEq b (cf a) (cf b) :=
  (cf_good a ha).2.2 b hb

end Frontier

import Mathlib
import RequestProject.Aronszajn

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

