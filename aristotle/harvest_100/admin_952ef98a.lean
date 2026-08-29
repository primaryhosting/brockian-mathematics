/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Ordinal Cardinal Set

namespace Aronszajn

/-! ## Cofinal `ω`-sequences in countable limit ordinals -/

/-- `c` is a nondecreasing `ω`-indexed sequence, starting at `0`, cofinal in `l`. -/
def IsCofSeq (l : Ordinal) (c : ℕ → Ordinal) : Prop :=
  c 0 = 0 ∧ Monotone c ∧ (∀ n, c n < l) ∧ ∀ ξ < l, ∃ n, ξ < c n

theorem exists_cofSeq {l : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) :
    ∃ c, IsCofSeq l c := by
  have hpos : (0 : Ordinal) < l := hl.bot_lt
  have hcount : (Set.Iio l).Countable := by
    rw [Cardinal.countable_iff_lt_aleph_one]
    have := Cardinal.lt_omega_iff_card_lt.mp hcl
    simpa [Ordinal.card, Ordinal.mk_Iio_ordinal] using this
  have hne : (Set.Iio l).Nonempty := ⟨0, hpos⟩
  obtain ⟨g, hg⟩ := hcount.exists_surjective hne
  refine ⟨fun n => (Finset.range n).sup (fun k => (g k : Ordinal) + 1), ?_, ?_, ?_, ?_⟩
  · simp
  · intro m n hmn
    exact Finset.sup_mono (by simpa using hmn)
  · intro n
    rw [Finset.sup_lt_iff (by rw [Ordinal.bot_eq_zero]; exact hpos)]
    intro k _
    exact hl.add_one_lt (g k).2
  · intro ξ hξ
    obtain ⟨k, hk⟩ := hg ⟨ξ, hξ⟩
    refine ⟨k + 1, ?_⟩
    have : ((g k : Ordinal) + 1) ≤ (Finset.range (k+1)).sup (fun j => (g j : Ordinal) + 1) :=
      Finset.le_sup (f := fun j => (g j : Ordinal) + 1) (Finset.self_mem_range_succ k)
    have hgk : (g k : Ordinal) = ξ := congrArg Subtype.val hk
    rw [hgk] at this
    exact lt_of_lt_of_le (lt_add_one ξ) this

open Classical in
/-- A canonical choice of cofinal `ω`-sequence. -/
noncomputable def cseq (l : Ordinal) : ℕ → Ordinal :=
  if h : ∃ c, IsCofSeq l c then h.choose else fun _ => 0

theorem cseq_spec {l : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) :
    IsCofSeq l (cseq l) := by
  have h : ∃ c, IsCofSeq l c := exists_cofSeq hl hcl
  unfold cseq
  rw [dif_pos h]
  exact h.choose_spec

theorem cseq_lt {l : Ordinal} (hl : Order.IsSuccLimit l) (n : ℕ) : cseq l n < l := by
  unfold cseq
  split
  · rename_i h
    exact h.choose_spec.2.2.1 n
  · exact hl.bot_lt

/-! ## The coherent family `E` -/

/-- Index of the block of `cseq l` containing `ξ`. -/
noncomputable def idx (l ξ : Ordinal) : ℕ := sInf {n | ξ < cseq l (n + 1)}

/-- The coherent sequence of finite-to-one functions.  `E o` is (on `Set.Iio o`) a
finite-to-one function to `ℕ`, and for `β < o` it agrees with `E β` on `Set.Iio β`
up to a finite set. -/
noncomputable def E : Ordinal → Ordinal → ℕ := fun o =>
  Ordinal.limitRecOn o
    (fun _ => 0)
    (fun γ f ξ => if ξ < γ then f ξ else 0)
    (fun l hl ih ξ =>
      if ξ < l then max (ih (cseq l (idx l ξ + 1)) (cseq_lt hl _) ξ) (idx l ξ) else 0)

@[simp] theorem E_zero (ξ : Ordinal) : E 0 ξ = 0 := by
  unfold E
  rw [Ordinal.limitRecOn_zero]

theorem E_succ (γ ξ : Ordinal) : E (γ + 1) ξ = if ξ < γ then E γ ξ else 0 := by
  unfold E
  rw [show γ + 1 = Order.succ γ from (Order.succ_eq_add_one γ).symm,
    Ordinal.limitRecOn_succ]

theorem E_limit {l : Ordinal} (hl : Order.IsSuccLimit l) (ξ : Ordinal) :
    E l ξ = if ξ < l then max (E (cseq l (idx l ξ + 1)) ξ) (idx l ξ) else 0 := by
  unfold E
  rw [Ordinal.limitRecOn_limit _ _ _ _ hl]

/-! ## Basic properties of `idx` -/

theorem idx_spec {l ξ : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) (hξ : ξ < l) :
    ξ < cseq l (idx l ξ + 1) := by
  have hne : {n : ℕ | ξ < cseq l (n + 1)}.Nonempty := by
    obtain ⟨n, hn⟩ := (cseq_spec hl hcl).2.2.2 ξ hξ
    cases n with
    | zero => rw [(cseq_spec hl hcl).1] at hn; exact absurd hn (by simp)
    | succ m => exact ⟨m, hn⟩
  exact Nat.sInf_mem hne

theorem idx_lt_of_lt_cseq {l ξ : Ordinal} (hl : Order.IsSuccLimit l) (hcl : l < ω₁) {N : ℕ}
    (h : ξ < cseq l N) : idx l ξ < N := by
  cases N with
  | zero => rw [(cseq_spec hl hcl).1] at h; exact absurd h (by simp)
  | succ M =>
    have : idx l ξ ≤ M := Nat.sInf_le h
    omega

/-! ## `E` is finite-to-one and coherent -/

/-- `E o` is finite-to-one on `Set.Iio o`. -/
def Fto (o : Ordinal) : Prop := ∀ n : ℕ, {ξ : Ordinal | ξ < o ∧ E o ξ = n}.Finite

/-- `E o` agrees with `E β` on `Set.Iio β` up to a finite set, for all `β < o`. -/
def Coh (o : Ordinal) : Prop := ∀ β < o, {ξ : Ordinal | ξ < β ∧ E o ξ ≠ E β ξ}.Finite

theorem E_main : ∀ o : Ordinal, o < ω₁ → Fto o ∧ Coh o := by
  intro o
  induction o using Ordinal.limitRecOn with
  | zero =>
    intro _
    constructor
    · intro n
      apply Set.Finite.subset (Set.finite_empty)
      rintro ξ ⟨h, -⟩
      exact absurd h (by simp)
    · intro β hβ
      exact absurd hβ (by simp)
  | succ γ ih =>
    rw [Order.succ_eq_add_one]
    intro hlt
    have hγ : γ < ω₁ := lt_trans (lt_add_one γ) hlt
    obtain ⟨ihF, ihC⟩ := ih hγ
    constructor
    · intro n
      apply Set.Finite.subset (((ihF n).union (Set.finite_singleton γ)))
      rintro ξ ⟨h1, h2⟩
      rcases lt_or_eq_of_le (Order.le_of_lt_succ h1) with h | h
      · left
        rw [E_succ, if_pos h] at h2
        exact ⟨h, h2⟩
      · right; exact h
    · intro β hβ
      rcases lt_or_eq_of_le (Order.le_of_lt_succ hβ) with h | h
      · apply Set.Finite.subset (ihC β h)
        rintro ξ ⟨h1, h2⟩
        rw [E_succ, if_pos (lt_trans h1 h)] at h2
        exact ⟨h1, h2⟩
      · apply Set.Finite.subset (Set.finite_empty)
        rintro ξ ⟨h1, h2⟩
        subst h
        rw [E_succ, if_pos h1] at h2
        exact absurd rfl h2
  | limit l hl ih =>
    intro hcl
    have hclt : ∀ k : ℕ, cseq l k < l := fun k => cseq_lt hl k
    have ihk : ∀ k : ℕ, Fto (cseq l k) ∧ Coh (cseq l k) := fun k =>
      ih _ (hclt k) (lt_trans (hclt k) hcl)
    constructor
    · intro n
      apply Set.Finite.subset
        (s := ⋃ i ∈ Set.Iic n, ⋃ m ∈ Set.Iic n,
          {ξ : Ordinal | ξ < cseq l (i + 1) ∧ E (cseq l (i + 1)) ξ = m})
        ((Set.finite_Iic n).biUnion fun i _ =>
          (Set.finite_Iic n).biUnion fun m _ => (ihk (i + 1)).1 m)
      rintro ξ ⟨h1, h2⟩
      rw [E_limit hl, if_pos h1] at h2
      have hi : idx l ξ ≤ n := h2 ▸ le_max_right _ _
      have hm : E (cseq l (idx l ξ + 1)) ξ ≤ n := h2 ▸ le_max_left _ _
      simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_setOf_eq, exists_prop]
      exact ⟨idx l ξ, hi, E (cseq l (idx l ξ + 1)) ξ, hm, idx_spec hl hcl h1, rfl⟩
    · intro β hβ
      obtain ⟨N, hN⟩ := (cseq_spec hl hcl).2.2.2 β hβ
      have hmono : Monotone (cseq l) := (cseq_spec hl hcl).2.1
      have hBig : {ξ : Ordinal | ξ < cseq l N ∧ E l ξ ≠ E (cseq l N) ξ}.Finite := by
        apply Set.Finite.subset
          (s := ⋃ k ∈ Set.Iio N,
            ({ξ : Ordinal | ξ < cseq l (k + 1) ∧ E (cseq l (k + 1)) ξ ≠ E (cseq l N) ξ} ∪
              ⋃ m ∈ Set.Iio k, {ξ : Ordinal | ξ < cseq l (k + 1) ∧ E (cseq l (k + 1)) ξ = m}))
          ((Set.finite_Iio N).biUnion fun k hk => Set.Finite.union ?_
            ((Set.finite_Iio k).biUnion fun m _ => (ihk (k + 1)).1 m))
        · rintro ξ ⟨h1, h2⟩
          have hξl : ξ < l := lt_trans h1 (hclt N)
          have hiN : idx l ξ < N := idx_lt_of_lt_cseq hl hcl h1
          have hξi : ξ < cseq l (idx l ξ + 1) := idx_spec hl hcl hξl
          rw [E_limit hl, if_pos hξl] at h2
          simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_union, Set.mem_setOf_eq, exists_prop]
          refine ⟨idx l ξ, hiN, ?_⟩
          rcases le_or_gt (idx l ξ) (E (cseq l (idx l ξ + 1)) ξ) with h | h
          · left
            refine ⟨hξi, ?_⟩
            rwa [max_eq_left h] at h2
          · right
            exact ⟨E (cseq l (idx l ξ + 1)) ξ, h, hξi, rfl⟩
        · have hle : cseq l (k + 1) ≤ cseq l N := hmono (by simpa using hk)
          rcases lt_or_eq_of_le hle with h | h
          · exact ((ihk N).2 _ h).subset (by rintro ξ ⟨h1, h2⟩; exact ⟨h1, Ne.symm h2⟩)
          · apply Set.Finite.subset Set.finite_empty
            rintro ξ ⟨-, h2⟩
            rw [h] at h2
            exact absurd rfl h2
      have h2 : {ξ : Ordinal | ξ < β ∧ E (cseq l N) ξ ≠ E β ξ}.Finite := (ihk N).2 β hN
      apply Set.Finite.subset (hBig.union h2)
      rintro ξ ⟨h1, hne⟩
      rcases eq_or_ne (E l ξ) (E (cseq l N) ξ) with h | h
      · right; exact ⟨h1, by rw [← h]; exact hne⟩
      · left; exact ⟨lt_trans h1 hN, h⟩

/-! ## Facts about `ω₁` -/

theorem countable_Iio_of_lt_omega1 {α : Ordinal} (h : α < ω₁) : (Set.Iio α).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one]
  have := Cardinal.lt_omega_iff_card_lt.mp h
  simpa [Ordinal.card, Ordinal.mk_Iio_ordinal] using this

theorem not_countable_Iio_omega1 : ¬ (Set.Iio (ω₁ : Ordinal)).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one]
  simp [Ordinal.mk_Iio_ordinal]

theorem exists_bound_of_seq (f : ℕ → Ordinal) (hf : ∀ n, f n < ω₁) : ∃ α < ω₁, ∀ n, f n < α := by
  have h1 : iSup f < ω₁ := by
    have := Ordinal.iSup_sequence_lt_omega_one f (by simpa [ord_aleph] using hf)
    simpa [ord_aleph] using this
  exact ⟨iSup f + 1, (Cardinal.isSuccLimit_omega 1).add_one_lt h1,
    fun n => lt_of_le_of_lt (Ordinal.le_iSup f n) (lt_add_one _)⟩

/-! ## The tree of nodes -/

/-- A node of the tree: a function `fn : Ordinal → ℕ` which is supported on `Set.Iio len`
(for some countable ordinal `len`) and differs from `E len` only on a finite set. -/
@[ext]
structure Node where
  /-- The length (level) of the node. -/
  len : Ordinal.{0}
  /-- The underlying function, extended by `0` past `len`. -/
  fn : Ordinal.{0} → ℕ
  len_lt : len < ω₁
  fn_zero : ∀ ξ, len ≤ ξ → fn ξ = 0
  fn_coh : {ξ : Ordinal | ξ < len ∧ fn ξ ≠ E len ξ}.Finite

namespace Node

instance : PartialOrder Node where
  le s t := s.len ≤ t.len ∧ ∀ ξ < s.len, s.fn ξ = t.fn ξ
  le_refl s := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans s t u h1 h2 := ⟨h1.1.trans h2.1, fun ξ hξ =>
    (h1.2 ξ hξ).trans (h2.2 ξ (lt_of_lt_of_le hξ h1.1))⟩
  le_antisymm s t h1 h2 := by
    have hlen : s.len = t.len := le_antisymm h1.1 h2.1
    refine Node.ext hlen (funext fun ξ => ?_)
    rcases lt_or_ge ξ s.len with h | h
    · exact h1.2 ξ h
    · rw [s.fn_zero ξ h, t.fn_zero ξ (hlen ▸ h)]

theorem le_def {s t : Node} : s ≤ t ↔ s.len ≤ t.len ∧ ∀ ξ < s.len, s.fn ξ = t.fn ξ := Iff.rfl

theorem len_lt_len_of_lt {s t : Node} (h : s < t) : s.len < t.len := by
  rcases lt_or_eq_of_le h.le.1 with h' | h'
  · exact h'
  · exact absurd (le_antisymm h.le ⟨h'.ge, fun ξ hξ => (h.le.2 ξ (h' ▸ hξ)).symm⟩) h.ne

/-- Each node is a finite-to-one function on its domain. -/
theorem fn_finite_fiber (s : Node) (n : ℕ) : {ξ : Ordinal | ξ < s.len ∧ s.fn ξ = n}.Finite := by
  apply Set.Finite.subset (s.fn_coh.union ((E_main s.len s.len_lt).1 n))
  rintro ξ ⟨h1, h2⟩
  rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h | h
  · right; exact ⟨h1, by rw [← h, h2]⟩
  · left; exact ⟨h1, h⟩

/-- Restriction of a node to a smaller length. -/
noncomputable def restr (s : Node) (β : Ordinal) (h : β < s.len) : Node where
  len := β
  fn := fun ξ => if ξ < β then s.fn ξ else 0
  len_lt := lt_trans h s.len_lt
  fn_zero := fun ξ hξ => if_neg (not_lt.mpr hξ)
  fn_coh := by
    apply Set.Finite.subset (s.fn_coh.union ((E_main s.len s.len_lt).2 β h))
    rintro ξ ⟨h1, h2⟩
    rw [if_pos h1] at h2
    rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h' | h'
    · right; exact ⟨h1, by rw [← h']; exact h2⟩
    · left; exact ⟨lt_trans h1 h, h'⟩

@[simp] theorem restr_len (s : Node) (β : Ordinal) (h : β < s.len) : (s.restr β h).len = β := rfl

theorem restr_lt (s : Node) (β : Ordinal) (h : β < s.len) : s.restr β h < s := by
  refine lt_of_le_of_ne ⟨h.le, fun ξ hξ => if_pos hξ⟩ (fun hEq => ?_)
  exact absurd (congrArg Node.len hEq) h.ne

/-- The canonical node of length `α`. -/
noncomputable def canonical (α : Ordinal) (hα : α < ω₁) : Node where
  len := α
  fn := fun ξ => if ξ < α then E α ξ else 0
  len_lt := hα
  fn_zero := fun ξ hξ => if_neg (not_lt.mpr hξ)
  fn_coh := by
    apply Set.Finite.subset Set.finite_empty
    rintro ξ ⟨h1, h2⟩
    rw [if_pos h1] at h2
    exact absurd rfl h2

@[simp] theorem canonical_len (α : Ordinal) (hα : α < ω₁) : (canonical α hα).len = α := rfl

/-- The finite "deviation set" of a node, which determines it within its level. -/
def dev (s : Node) : Set (Ordinal × ℕ) :=
  (fun ξ => (ξ, s.fn ξ)) '' {ξ : Ordinal | ξ < s.len ∧ s.fn ξ ≠ E s.len ξ}

theorem dev_key {s t : Node} (hsub : dev s ⊆ dev t) {ξ : Ordinal}
    (h1 : ξ < s.len) (h2 : s.fn ξ ≠ E s.len ξ) : t.fn ξ = s.fn ξ := by
  obtain ⟨ξ', -, h⟩ : (ξ, s.fn ξ) ∈ dev t := hsub ⟨ξ, ⟨h1, h2⟩, rfl⟩
  have h₁ : ξ' = ξ := congrArg Prod.fst h
  have h₂ : t.fn ξ' = s.fn ξ := congrArg Prod.snd h
  rwa [h₁] at h₂

theorem eq_of_dev_eq {s t : Node} (hlen : s.len = t.len) (hdev : dev s = dev t) : s = t := by
  refine Node.ext hlen (funext fun ξ => ?_)
  rcases lt_or_ge ξ s.len with h | h
  · rcases eq_or_ne (s.fn ξ) (E s.len ξ) with h2 | h2
    · rcases eq_or_ne (t.fn ξ) (E t.len ξ) with h3 | h3
      · rw [h2, h3, hlen]
      · exact dev_key hdev.ge (hlen ▸ h) h3
    · exact (dev_key hdev.le h h2).symm
  · rw [s.fn_zero ξ h, t.fn_zero ξ (hlen ▸ h)]

theorem level_countable (α : Ordinal) : {s : Node | s.len = α}.Countable := by
  rcases lt_or_ge α ω₁ with hα | hα
  · refine Set.MapsTo.countable_of_injOn (f := dev)
      (t := {A : Set (Ordinal × ℕ) | A.Finite ∧ A ⊆ Set.Iio α ×ˢ (Set.univ : Set ℕ)}) ?_ ?_ ?_
    · intro s hs
      refine ⟨s.fn_coh.image _, ?_⟩
      rintro p ⟨ξ, ⟨h1, -⟩, rfl⟩
      exact ⟨by simpa [Set.mem_setOf_eq] using (hs ▸ h1 : ξ < α), trivial⟩
    · intro s hs t ht hdev
      exact eq_of_dev_eq (by rw [hs, ht]) hdev
    · exact Set.countable_setOf_finite_subset
        ((countable_Iio_of_lt_omega1 hα).prod Set.countable_univ)
  · have : {s : Node | s.len = α} = ∅ := by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ s.len_lt) (not_lt.mpr hα)
    rw [this]
    exact Set.countable_empty

/-! ## Chains are countable -/

open Classical in
/-- The union of a chain of nodes, as a function. -/
noncomputable def chainFn (C : Set Node) (ξ : Ordinal) : ℕ :=
  if h : ∃ s : Node, s ∈ C ∧ ξ < s.len then h.choose.fn ξ else 0

theorem chainFn_eq {C : Set Node} (hC : IsChain (· ≤ ·) C) {s : Node} (hs : s ∈ C) {ξ : Ordinal}
    (hξ : ξ < s.len) : chainFn C ξ = s.fn ξ := by
  classical
  have h : ∃ t : Node, t ∈ C ∧ ξ < t.len := ⟨s, hs, hξ⟩
  rw [chainFn, dif_pos h]
  obtain ⟨hmem, hlt⟩ := h.choose_spec
  rcases eq_or_ne h.choose s with heq | hne
  · rw [heq]
  · rcases hC hmem hs hne with hle | hle
    · exact hle.2 ξ hlt
    · exact (hle.2 ξ hξ).symm

theorem chain_countable (C : Set Node) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  by_contra hunc
  -- lengths are injective on `C`
  have hinj : Set.InjOn Node.len C := by
    intro s hs t ht hlen
    rcases eq_or_ne s t with h | h
    · exact h
    · rcases hC hs ht h with hle | hle
      · exact le_antisymm hle ⟨hlen.ge, fun ξ hξ => (hle.2 ξ (hlen ▸ hξ)).symm⟩
      · exact (le_antisymm hle ⟨hlen.le, fun ξ hξ => (hle.2 ξ (hlen ▸ hξ)).symm⟩).symm
  -- `C` has nodes of arbitrarily large length
  have hunbdd : ∀ α < ω₁, ∃ s ∈ C, α < s.len := by
    intro α hα
    by_contra hcon
    push_neg at hcon
    refine hunc (Set.MapsTo.countable_of_injOn (f := Node.len) (t := Set.Iio (α + 1))
      (fun s hs => lt_of_le_of_lt (hcon s hs) (lt_add_one α)) hinj ?_)
    exact countable_Iio_of_lt_omega1 ((Cardinal.isSuccLimit_omega 1).add_one_lt hα)
  -- the union of the chain is a finite-to-one function on `Set.Iio ω₁`
  have hfin : ∀ n : ℕ, {ξ : Ordinal | ξ < ω₁ ∧ chainFn C ξ = n}.Finite := by
    intro n
    rw [← Set.not_infinite]
    intro hinf
    set emb := hinf.natEmbedding with hemb
    obtain ⟨α, hα, hbound⟩ :=
      exists_bound_of_seq (fun k => ((emb k : Ordinal))) (fun k => (emb k).2.1)
    obtain ⟨s, hs, hslen⟩ := hunbdd α hα
    have hsub : Set.range (fun k => ((emb k : Ordinal))) ⊆
        {ξ : Ordinal | ξ < s.len ∧ s.fn ξ = n} := by
      rintro _ ⟨k, rfl⟩
      have h1 : ((emb k : Ordinal)) < s.len := lt_trans (hbound k) hslen
      refine ⟨h1, ?_⟩
      rw [← chainFn_eq hC hs h1]
      exact (emb k).2.2
    have hinjg : Function.Injective (fun k => ((emb k : Ordinal))) := fun a b hab =>
      emb.injective (Subtype.ext hab)
    exact Set.infinite_range_of_injective hinjg (Set.Finite.subset (s.fn_finite_fiber n) hsub)
  -- hence `Set.Iio ω₁` is countable, a contradiction
  refine not_countable_Iio_omega1 ?_
  have : Set.Iio (ω₁ : Ordinal) ⊆ ⋃ n : ℕ, {ξ : Ordinal | ξ < ω₁ ∧ chainFn C ξ = n} := by
    intro ξ hξ
    exact Set.mem_iUnion.mpr ⟨chainFn C ξ, hξ, rfl⟩
  exact Set.Countable.mono this (Set.countable_iUnion fun n => (hfin n).countable)

/-! ## Tree structure -/

theorem pred_linear (y x x' : Node) (h : x < y) (h' : x' < y) : x ≤ x' ∨ x' ≤ x := by
  rcases le_total x.len x'.len with hle | hle
  · exact Or.inl ⟨hle, fun ξ hξ => (h.le.2 ξ hξ).trans (h'.le.2 ξ (lt_of_lt_of_le hξ hle)).symm⟩
  · exact Or.inr ⟨hle, fun ξ hξ => (h'.le.2 ξ hξ).trans (h.le.2 ξ (lt_of_lt_of_le hξ hle)).symm⟩

theorem pred_exists (y : Node) (β : Ordinal) (hβ : β < y.len) :
    ∃! x : Node, x < y ∧ x.len = β := by
  refine ⟨y.restr β hβ, ⟨y.restr_lt β hβ, rfl⟩, ?_⟩
  rintro x ⟨hx, hxlen⟩
  refine Node.ext hxlen (funext fun ξ => ?_)
  rcases lt_or_ge ξ β with h | h
  · show x.fn ξ = if ξ < β then y.fn ξ else 0
    rw [if_pos h]
    exact hx.le.2 ξ (hxlen ▸ h)
  · show x.fn ξ = if ξ < β then y.fn ξ else 0
    rw [if_neg (not_lt.mpr h), x.fn_zero ξ (hxlen ▸ h)]

end Node

/-- `IsAronszajnTree T ht` states that the partial order `T`, with level function `ht`, is an
Aronszajn tree: it is a tree (the predecessors of any node form a chain, well ordered by the
level function, with exactly one predecessor at each smaller level), it has height `ω₁`
(every countable ordinal occurs as a level, and no other level occurs), every level is
countable, and there is no uncountable chain (branch). -/
structure IsAronszajnTree (T : Type*) [PartialOrder T] (ht : T → Ordinal.{0}) : Prop where
  /-- Every node lives at a countable level. -/
  ht_lt_omega1 : ∀ x, ht x < ω₁
  /-- The level function is strictly monotone. -/
  ht_strictMono : ∀ ⦃x y : T⦄, x < y → ht x < ht y
  /-- The predecessors of a node form a chain. -/
  pred_linear : ∀ y x x' : T, x < y → x' < y → x ≤ x' ∨ x' ≤ x
  /-- A node of level `α` has exactly one predecessor at each level `β < α`. -/
  pred_exists : ∀ (y : T) (β : Ordinal), β < ht y → ∃! x, x < y ∧ ht x = β
  /-- The tree has height `ω₁`: every countable level is inhabited. -/
  levels_nonempty : ∀ α < ω₁, ∃ x, ht x = α
  /-- Every level is countable. -/
  levels_countable : ∀ α, {x | ht x = α}.Countable
  /-- There is no uncountable branch. -/
  chains_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

end Aronszajn

open Aronszajn in
/-- **There is an Aronszajn tree**: a tree of height `ω₁` all of whose levels are countable
and which has no uncountable branch. -/
theorem Frontier.Aronszajn_tree_exists :
    ∃ (T : Type 1) (inst : PartialOrder T) (ht : T → Ordinal.{0}), @IsAronszajnTree T inst ht := by
  refine ⟨Node, inferInstance, Node.len, ?_⟩
  exact
    { ht_lt_omega1 := fun s => s.len_lt
      ht_strictMono := fun _ _ h => Node.len_lt_len_of_lt h
      pred_linear := Node.pred_linear
      pred_exists := Node.pred_exists
      levels_nonempty := fun α hα => ⟨Node.canonical α hα, rfl⟩
      levels_countable := Node.level_countable
      chains_countable := Node.chain_countable }

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

