import Mathlib

/-!
# Construction of an Aronszajn tree

We build the classical (special) Aronszajn tree: nodes at level `α < ω₁` are strictly
increasing bounded functions `α → ℚ`, constructed by transfinite recursion so that each
level is countable and every node can be extended to any higher level while keeping a
prescribed rational bound.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node is (the total extension by `0` of) a function from a countable ordinal to `ℚ`. -/
abbrev Nd : Type 1 := Ordinal.{0} → ℚ

/-- `SBd f α q` says the values of `f` below `α` are bounded by some rational `< q`. -/
def SBd (f : Nd) (α : Ordinal.{0}) (q : ℚ) : Prop := ∃ r : ℚ, r < q ∧ ∀ γ < α, f γ ≤ r

/-- Append the value `s` at position `δ` to `f`. -/
noncomputable def snoc (δ : Ordinal.{0}) (f : Nd) (s : ℚ) : Nd :=
  fun γ => if γ < δ then f γ else if γ = δ then s else 0

/-- Truncate `f` to the ordinals below `β`. -/
noncomputable def trunc (β : Ordinal.{0}) (f : Nd) : Nd := fun γ => if γ < β then f γ else 0

/-- An enumeration of the ordinals below `α` (when `α` is countable and positive). -/
noncomputable def enumOrd' (α : Ordinal.{0}) : ℕ → Ordinal.{0} := fun n =>
  if h : ∃ e : ℕ → Ordinal.{0}, ∀ β < α, ∃ m, e m = β then
    (if h.choose n < α then h.choose n else 0)
  else 0

theorem enumOrd'_lt {α : Ordinal.{0}} (hα : 0 < α) (n : ℕ) : enumOrd' α n < α := by
  unfold enumOrd'
  split
  · split
    · assumption
    · exact hα
  · exact hα

theorem enumOrd'_surj {α : Ordinal.{0}} (hc : (Set.Iio α).Countable) {β : Ordinal.{0}}
    (hβ : β < α) : ∃ n, enumOrd' α n = β := by
  have h : ∃ e : ℕ → Ordinal.{0}, ∀ β < α, ∃ m, e m = β := by
    rcases Set.countable_iff_exists_subset_range.mp hc with ⟨e, he⟩
    exact ⟨e, fun b hb => he hb⟩
  obtain ⟨m, hm⟩ := h.choose_spec β hβ
  refine ⟨m, ?_⟩
  unfold enumOrd'
  rw [dif_pos h, if_pos (by rw [hm]; exact hβ), hm]

/-- An increasing sequence starting at `β` and cofinal in `α`. -/
noncomputable def cseq (α β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => β
  | n + 1 => max (cseq α β n + 1) (enumOrd' α n + 1)

theorem cseq_zero (α β : Ordinal.{0}) : cseq α β 0 = β := rfl

theorem cseq_lt_succ (α β : Ordinal.{0}) (n : ℕ) : cseq α β n < cseq α β (n + 1) := by
  have : cseq α β (n+1) = max (cseq α β n + 1) (enumOrd' α n + 1) := rfl
  rw [this]
  exact lt_of_lt_of_le (Order.lt_succ _) (le_max_left _ _)

theorem cseq_strictMono (α β : Ordinal.{0}) : StrictMono (cseq α β) :=
  strictMono_nat_of_lt_succ (cseq_lt_succ α β)

theorem cseq_mono (α β : Ordinal.{0}) : Monotone (cseq α β) := (cseq_strictMono α β).monotone

theorem cseq_lt {α β : Ordinal.{0}} (hl : IsSuccLimit α) (hβ : β < α) (n : ℕ) :
    cseq α β n < α := by
  induction n with
  | zero => exact hβ
  | succ n ih =>
      have h1 : cseq α β (n+1) = max (cseq α β n + 1) (enumOrd' α n + 1) := rfl
      rw [h1]
      exact max_lt (hl.add_one_lt ih)
        (hl.add_one_lt (enumOrd'_lt (lt_of_le_of_lt (zero_le β) hβ) n))

theorem cseq_cofinal {α β : Ordinal.{0}} (hc : (Set.Iio α).Countable) {γ : Ordinal.{0}}
    (hγ : γ < α) : ∃ n, γ < cseq α β n := by
  obtain ⟨n, hn⟩ := enumOrd'_surj hc hγ
  refine ⟨n + 1, ?_⟩
  have h1 : cseq α β (n+1) = max (cseq α β n + 1) (enumOrd' α n + 1) := rfl
  rw [h1, hn]
  exact lt_of_lt_of_le (Order.lt_succ _) (le_max_right _ _)

/-- One step of the chain used to build a node at a limit level. -/
noncomputable def chainF (P : Ordinal.{0} → Set Nd) (α β : Ordinal.{0}) (f : Nd) (q : ℚ) :
    ℕ → Nd
  | 0 => f
  | n + 1 =>
      if h : ∃ g, g ∈ P (cseq α β (n+1)) ∧ (∀ γ < cseq α β n, g γ = chainF P α β f q n γ) ∧
          SBd g (cseq α β (n+1)) q then h.choose else fun _ => 0

/-- The node at a limit level obtained as the union of the chain. -/
noncomputable def limExt (P : Ordinal.{0} → Set Nd) (α β : Ordinal.{0}) (f : Nd) (q : ℚ) : Nd :=
  fun γ => if (∃ n, γ < cseq α β n) then chainF P α β f q (sInf {n | γ < cseq α β n}) γ else 0

/-- One step of the transfinite recursion defining the levels of the tree. -/
noncomputable def Lstep (α : Ordinal.{0}) (P : Ordinal.{0} → Set Nd) : Set Nd :=
  if α = 0 then {fun _ => 0}
  else if IsSuccPrelimit α then
    {g | ∃ β, β < α ∧ ∃ f ∈ P β, ∃ q : ℚ, SBd f β q ∧ g = limExt P α β f q}
  else
    {g | ∃ f ∈ P (Ordinal.pred α), ∃ s : ℚ, (∀ γ < Ordinal.pred α, f γ < s) ∧
          g = snoc (Ordinal.pred α) f s}

/-- The `α`-th level of the tree. -/
noncomputable def L : Ordinal.{0} → Set Nd :=
  Ordinal.lt_wf.fix (fun a ih => Lstep a (fun b => if h : b < a then ih b h else ∅))

/-- The family of levels below `α`. -/
noncomputable def prevOf (α : Ordinal.{0}) : Ordinal.{0} → Set Nd :=
  fun b => if b < α then L b else ∅

theorem prevOf_eq {α b : Ordinal.{0}} (h : b < α) : prevOf α b = L b := if_pos h

theorem L_eq (α : Ordinal.{0}) : L α = Lstep α (prevOf α) := by
  have hfun : (fun b => if h : b < α then L b else (∅ : Set Nd)) = prevOf α := by
    funext b
    rw [prevOf]
    by_cases h : b < α
    · rw [dif_pos h, if_pos h]
    · rw [dif_neg h, if_neg h]
  conv_lhs => rw [L, Ordinal.lt_wf.fix_eq]
  rw [← hfun]
  rfl

theorem L_zero : L 0 = {fun _ => 0} := by
  rw [L_eq, Lstep, if_pos rfl]

theorem L_succ (δ : Ordinal.{0}) :
    L (δ + 1) = {g | ∃ f ∈ L δ, ∃ s : ℚ, (∀ γ < δ, f γ < s) ∧ g = snoc δ f s} := by
  have h0 : δ + 1 ≠ 0 := by
    rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot δ
  have hnp : ¬ IsSuccPrelimit (δ + 1) := by
    rw [← Order.succ_eq_add_one]; exact Order.not_isSuccPrelimit_succ δ
  have hpred : Ordinal.pred (δ + 1) = δ := by
    rw [← Order.succ_eq_add_one]; exact Ordinal.pred_succ δ
  rw [L_eq, Lstep, if_neg h0, if_neg hnp, hpred, prevOf_eq (by exact Order.lt_succ δ)]

theorem L_limit {α : Ordinal.{0}} (hl : IsSuccLimit α) :
    L α = {g | ∃ β, β < α ∧ ∃ f ∈ L β, ∃ q : ℚ, SBd f β q ∧ g = limExt (prevOf α) α β f q} := by
  have h0 : α ≠ 0 := by
    rintro rfl
    exact hl.not_isMin isMin_bot
  rw [L_eq, Lstep, if_neg h0, if_pos hl.isSuccPrelimit]
  ext g
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨β, hβ, f, hf, q, hq, rfl⟩
    exact ⟨β, hβ, f, by rwa [prevOf_eq hβ] at hf, q, hq, rfl⟩
  · rintro ⟨β, hβ, f, hf, q, hq, rfl⟩
    exact ⟨β, hβ, f, by rwa [prevOf_eq hβ], q, hq, rfl⟩

/-! ### The invariants -/

/-- The invariants maintained by the transfinite construction of the levels. -/
structure Good (α : Ordinal.{0}) : Prop where
  zero_out : ∀ f ∈ L α, ∀ γ, α ≤ γ → f γ = 0
  mono : ∀ f ∈ L α, ∀ γ δ, γ < δ → δ < α → f γ < f δ
  coh : ∀ β < α, ∀ f ∈ L α, trunc β f ∈ L β
  ctble : (L α).Countable
  ext : ∀ β < α, ∀ f ∈ L β, ∀ q : ℚ, SBd f β q → ∃ g ∈ L α, (∀ γ < β, g γ = f γ) ∧ SBd g α q

theorem Iio_countable {α : Ordinal.{0}} (hα : α < ω₁) : (Set.Iio α).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
  exact lt_omega_iff_card_lt.mp hα

theorem good_zero : Good 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f hf γ _
    rw [L_zero] at hf
    rw [hf]
  · intro f _ γ δ _ hδ
    exact absurd hδ (by simp)
  · intro β hβ
    exact absurd hβ (by simp)
  · rw [L_zero]; exact Set.countable_singleton _
  · intro β hβ
    exact absurd hβ (by simp)

/-! ### Successor levels -/

theorem snoc_of_lt {δ γ : Ordinal.{0}} {f : Nd} {s : ℚ} (h : γ < δ) : snoc δ f s γ = f γ := by
  rw [snoc, if_pos h]

theorem snoc_self {δ : Ordinal.{0}} {f : Nd} {s : ℚ} : snoc δ f s δ = s := by
  rw [snoc, if_neg (lt_irrefl δ), if_pos rfl]

theorem trunc_self {β : Ordinal.{0}} {f : Nd} (h : ∀ γ, β ≤ γ → f γ = 0) : trunc β f = f := by
  funext γ
  rw [trunc]
  by_cases hγ : γ < β
  · rw [if_pos hγ]
  · rw [if_neg hγ, h γ (not_lt.mp hγ)]

theorem lt_succ_iff' {γ δ : Ordinal.{0}} : γ < δ + 1 ↔ γ ≤ δ := by
  rw [← Order.succ_eq_add_one]; exact Order.lt_succ_iff

theorem succ_le_iff' {γ δ : Ordinal.{0}} : δ + 1 ≤ γ ↔ δ < γ := by
  rw [← Order.succ_eq_add_one]; exact Order.succ_le_iff

theorem succ_ext {δ : Ordinal.{0}} (f₁ : Nd) (hf₁ : f₁ ∈ L δ) (Q : ℚ) (hQ : SBd f₁ δ Q) :
    ∃ g ∈ L (δ + 1), (∀ γ < δ, g γ = f₁ γ) ∧ SBd g (δ + 1) Q := by
  obtain ⟨r, hrQ, hr⟩ := hQ
  refine ⟨snoc δ f₁ ((r + Q) / 2), ?_, ?_, ?_⟩
  · rw [L_succ]
    exact ⟨f₁, hf₁, (r + Q) / 2, fun γ hγ => lt_of_le_of_lt (hr γ hγ) (by linarith), rfl⟩
  · intro γ hγ
    exact snoc_of_lt hγ
  · refine ⟨(r + Q) / 2, by linarith, ?_⟩
    intro γ hγ
    rcases lt_or_eq_of_le (lt_succ_iff'.mp hγ) with h | rfl
    · rw [snoc_of_lt h]; linarith [hr γ h]
    · rw [snoc_self]

theorem good_succ {δ : Ordinal.{0}} (hd : Good δ) : Good (δ + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg γ hγ
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    have hδγ : δ < γ := succ_le_iff'.mp hγ
    rw [snoc, if_neg (not_lt.mpr hδγ.le), if_neg hδγ.ne']
  · rintro g hg γ ε hγε hε
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    rcases lt_or_eq_of_le (lt_succ_iff'.mp hε) with h | rfl
    · rw [snoc_of_lt (hγε.trans h), snoc_of_lt h]
      exact hd.mono f hf γ ε hγε h
    · rw [snoc_of_lt hγε, snoc_self]
      exact hs γ hγε
  · rintro β hβ g hg
    rw [L_succ] at hg
    obtain ⟨f, hf, s, hs, rfl⟩ := hg
    have hβδ : β ≤ δ := lt_succ_iff'.mp hβ
    have htr : trunc β (snoc δ f s) = trunc β f := by
      funext γ
      rw [trunc, trunc]
      by_cases h : γ < β
      · rw [if_pos h, if_pos h, snoc_of_lt (lt_of_lt_of_le h hβδ)]
      · rw [if_neg h, if_neg h]
    rw [htr]
    rcases lt_or_eq_of_le hβδ with h | rfl
    · exact hd.coh β h f hf
    · rw [trunc_self (fun γ hγ => hd.zero_out f hf γ hγ)]
      exact hf
  · have hsub : L (δ + 1) ⊆ ⋃ f ∈ L δ, ⋃ s : ℚ, {snoc δ f s} := by
      intro g hg
      rw [L_succ] at hg
      obtain ⟨f, hf, s, -, rfl⟩ := hg
      exact Set.mem_biUnion hf (Set.mem_iUnion.mpr ⟨s, rfl⟩)
    exact Set.Countable.mono hsub
      (hd.ctble.biUnion (fun f _ => Set.countable_iUnion (fun s => Set.countable_singleton _)))
  · rintro β hβ f₀ hf₀ Q hQ
    have hβδ : β ≤ δ := lt_succ_iff'.mp hβ
    obtain ⟨f₁, hf₁, hag, hb⟩ : ∃ f₁ ∈ L δ, (∀ γ < β, f₁ γ = f₀ γ) ∧ SBd f₁ δ Q := by
      rcases lt_or_eq_of_le hβδ with h | rfl
      · exact hd.ext β h f₀ hf₀ Q hQ
      · exact ⟨f₀, hf₀, fun _ _ => rfl, hQ⟩
    obtain ⟨g, hg, hag', hb'⟩ := succ_ext f₁ hf₁ Q hb
    exact ⟨g, hg, fun γ hγ => (hag' γ (lt_of_lt_of_le hγ hβδ)).trans (hag γ hγ), hb'⟩

/-! ### Limit levels -/

section Limit

variable {α β : Ordinal.{0}} {f : Nd} {q : ℚ}

/-- Successor step of the chain construction at a limit level. -/
theorem chain_step (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ) (n : ℕ)
    (hn : chainF (prevOf α) α β f q n ∈ L (cseq α β n) ∧
      SBd (chainF (prevOf α) α β f q n) (cseq α β n) q) :
    chainF (prevOf α) α β f q (n + 1) ∈ L (cseq α β (n + 1)) ∧
      SBd (chainF (prevOf α) α β f q (n + 1)) (cseq α β (n + 1)) q ∧
      ∀ γ < cseq α β n, chainF (prevOf α) α β f q (n + 1) γ = chainF (prevOf α) α β f q n γ := by
  have h1 : cseq α β (n + 1) < α := cseq_lt hl hβ (n + 1)
  have hex : ∃ g, g ∈ prevOf α (cseq α β (n + 1)) ∧
      (∀ γ < cseq α β n, g γ = chainF (prevOf α) α β f q n γ) ∧
      SBd g (cseq α β (n + 1)) q := by
    obtain ⟨g, hg, ha, hb⟩ := (ih _ h1).ext (cseq α β n) (cseq_lt_succ α β n)
      (chainF (prevOf α) α β f q n) hn.1 q hn.2
    exact ⟨g, by rwa [prevOf_eq h1], ha, hb⟩
  have heq : chainF (prevOf α) α β f q (n + 1) = hex.choose := by
    rw [chainF, dif_pos hex]
  have hmem : ∀ g : Nd, g ∈ prevOf α (cseq α β (n + 1)) → g ∈ L (cseq α β (n + 1)) := by
    intro g hg
    rwa [prevOf_eq h1] at hg
  obtain ⟨hm, ha, hb⟩ := hex.choose_spec
  exact ⟨heq ▸ hmem _ hm, heq ▸ hb, fun γ hγ => by rw [heq]; exact ha γ hγ⟩

theorem chain_spec (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) :
    chainF (prevOf α) α β f q n ∈ L (cseq α β n) ∧
      SBd (chainF (prevOf α) α β f q n) (cseq α β n) q := by
  induction n with
  | zero => exact ⟨hf, hq⟩
  | succ n ihn =>
      obtain ⟨h1, h2, -⟩ := chain_step hl hβ ih n ihn
      exact ⟨h1, h2⟩

theorem chain_agree (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) :
    ∀ γ < cseq α β n, chainF (prevOf α) α β f q (n + 1) γ = chainF (prevOf α) α β f q n γ :=
  (chain_step hl hβ ih n (chain_spec hl hβ ih hf hq n)).2.2

theorem chain_agree' (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) {m n : ℕ} (hmn : m ≤ n) :
    ∀ γ < cseq α β m, chainF (prevOf α) α β f q n γ = chainF (prevOf α) α β f q m γ := by
  induction n, hmn using Nat.le_induction with
  | base => intro γ _; rfl
  | succ n hmn ihn =>
      intro γ hγ
      rw [chain_agree hl hβ ih hf hq n γ (lt_of_lt_of_le hγ (cseq_mono α β hmn))]
      exact ihn γ hγ

theorem limExt_eq (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) (n : ℕ) {γ : Ordinal.{0}} (hγ : γ < cseq α β n) :
    limExt (prevOf α) α β f q γ = chainF (prevOf α) α β f q n γ := by
  have hne : ∃ k, γ < cseq α β k := ⟨n, hγ⟩
  have hm : γ < cseq α β (sInf {k | γ < cseq α β k}) := Nat.sInf_mem hne
  have hmn : sInf {k | γ < cseq α β k} ≤ n := Nat.sInf_le hγ
  rw [limExt, if_pos hne]
  exact (chain_agree' hl hβ ih hf hq hmn γ hm).symm

theorem limExt_zero_out (hl : IsSuccLimit α) (hβ : β < α) {γ : Ordinal.{0}} (hγ : α ≤ γ) :
    limExt (prevOf α) α β f q γ = 0 := by
  have hne : ¬ ∃ k, γ < cseq α β k := by
    rintro ⟨k, hk⟩
    exact absurd (hk.trans (cseq_lt hl hβ k)) (not_lt.mpr hγ)
  rw [limExt, if_neg hne]

theorem limExt_agree (hl : IsSuccLimit α) (hβ : β < α) (ih : ∀ γ < α, Good γ)
    (hf : f ∈ L β) (hq : SBd f β q) : ∀ γ < β, limExt (prevOf α) α β f q γ = f γ := by
  intro γ hγ
  exact limExt_eq hl hβ ih hf hq 0 (by rwa [cseq_zero])

theorem limExt_lt (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable) (hβ : β < α)
    (ih : ∀ γ < α, Good γ) (hf : f ∈ L β) (hq : SBd f β q) :
    ∀ γ < α, limExt (prevOf α) α β f q γ < q := by
  intro γ hγ
  obtain ⟨n, hn⟩ := cseq_cofinal (β := β) hc hγ
  obtain ⟨r, hrq, hr⟩ := (chain_spec hl hβ ih hf hq n).2
  rw [limExt_eq hl hβ ih hf hq n hn]
  exact lt_of_le_of_lt (hr γ hn) hrq

theorem limExt_mono (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable) (hβ : β < α)
    (ih : ∀ γ < α, Good γ) (hf : f ∈ L β) (hq : SBd f β q) :
    ∀ γ δ, γ < δ → δ < α → limExt (prevOf α) α β f q γ < limExt (prevOf α) α β f q δ := by
  intro γ δ hγδ hδ
  obtain ⟨n, hn⟩ := cseq_cofinal (β := β) hc hδ
  rw [limExt_eq hl hβ ih hf hq n (hγδ.trans hn), limExt_eq hl hβ ih hf hq n hn]
  exact (ih _ (cseq_lt hl hβ n)).mono _ (chain_spec hl hβ ih hf hq n).1 γ δ hγδ hn

theorem limExt_trunc (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable) (hβ : β < α)
    (ih : ∀ γ < α, Good γ) (hf : f ∈ L β) (hq : SBd f β q) :
    ∀ β' < α, trunc β' (limExt (prevOf α) α β f q) ∈ L β' := by
  intro β' hβ'
  obtain ⟨n, hn⟩ := cseq_cofinal (β := β) hc hβ'
  have heq : trunc β' (limExt (prevOf α) α β f q) = trunc β' (chainF (prevOf α) α β f q n) := by
    funext γ
    rw [trunc, trunc]
    by_cases hγ : γ < β'
    · rw [if_pos hγ, if_pos hγ, limExt_eq hl hβ ih hf hq n (hγ.trans hn)]
    · rw [if_neg hγ, if_neg hγ]
  rw [heq]
  exact (ih _ (cseq_lt hl hβ n)).coh β' hn _ (chain_spec hl hβ ih hf hq n).1

end Limit

theorem good_limit {α : Ordinal.{0}} (hl : IsSuccLimit α) (hc : (Set.Iio α).Countable)
    (ih : ∀ γ < α, Good γ) : Good α := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro g hg γ hγ
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_zero_out hl hβ hγ
  · rintro g hg γ δ hγδ hδ
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_mono hl hc hβ ih hf hq γ δ hγδ hδ
  · rintro β' hβ' g hg
    rw [L_limit hl] at hg
    obtain ⟨β, hβ, f, hf, q, hq, rfl⟩ := hg
    exact limExt_trunc hl hc hβ ih hf hq β' hβ'
  · have hsub : L α ⊆ ⋃ β ∈ Set.Iio α, ⋃ f ∈ L β, ⋃ q : ℚ, {limExt (prevOf α) α β f q} := by
      intro g hg
      rw [L_limit hl] at hg
      obtain ⟨β, hβ, f, hf, q, -, rfl⟩ := hg
      exact Set.mem_biUnion hβ (Set.mem_biUnion hf (Set.mem_iUnion.mpr ⟨q, rfl⟩))
    refine Set.Countable.mono hsub (hc.biUnion (fun β hβ => ?_))
    exact ((ih β hβ).ctble).biUnion
      (fun f _ => Set.countable_iUnion (fun q => Set.countable_singleton _))
  · rintro β hβ f hf Q ⟨r, hrQ, hr⟩
    refine ⟨limExt (prevOf α) α β f ((r + Q) / 2), ?_, ?_, ?_⟩
    · rw [L_limit hl]
      exact ⟨β, hβ, f, hf, (r + Q) / 2, ⟨r, by linarith, hr⟩, rfl⟩
    · exact limExt_agree hl hβ ih hf ⟨r, by linarith, hr⟩
    · refine ⟨(r + Q) / 2, by linarith, ?_⟩
      intro γ hγ
      exact le_of_lt (limExt_lt hl hc hβ ih hf ⟨r, by linarith, hr⟩ γ hγ)

theorem good (α : Ordinal.{0}) (hα : α < ω₁) : Good α := by
  induction α using Ordinal.lt_wf.induction with
  | _ α ih =>
    rcases eq_or_ne α 0 with rfl | h0
    · exact good_zero
    · by_cases hl : IsSuccPrelimit α
      · have hl' : IsSuccLimit α :=
          ⟨by rw [isMin_iff_eq_bot, Ordinal.bot_eq_zero]; exact h0, hl⟩
        exact good_limit hl' (Iio_countable hα) (fun γ hγ => ih γ hγ (hγ.trans hα))
      · have hp : Ordinal.pred α + 1 = α := by
          rw [← Order.succ_eq_add_one]
          exact Ordinal.succ_pred_eq_iff_not_isSuccPrelimit.mpr hl
        have hlt : Ordinal.pred α < α := Ordinal.pred_lt_iff_not_isSuccPrelimit.mpr hl
        have := good_succ (ih (Ordinal.pred α) hlt (hlt.trans hα))
        rwa [hp] at this

end Aronszajn

import RequestProject.Aronszajn

/-!
# The Aronszajn tree

From the levels `L α` constructed in `RequestProject.Aronszajn` we assemble the tree of
nodes and verify the defining properties of an Aronszajn tree.
-/

open Ordinal Cardinal Set Order
open scoped Classical

namespace Aronszajn

set_option autoImplicit false
set_option maxRecDepth 8000

/-- A node of the tree: a level `α < ω₁` together with an element of `L α`. -/
def Node : Type 1 := {p : Ordinal.{0} × Nd // p.1 < ω₁ ∧ p.2 ∈ L p.1}

/-- The height of a node. -/
def nht (x : Node) : Ordinal.{0} := x.1.1

/-- The function attached to a node. -/
def nfun (x : Node) : Nd := x.1.2

/-- The tree order: end-extension. -/
def nle (x y : Node) : Prop := nht x ≤ nht y ∧ ∀ γ < nht x, nfun x γ = nfun y γ

theorem nht_lt (x : Node) : nht x < ω₁ := x.2.1

theorem nfun_mem (x : Node) : nfun x ∈ L (nht x) := x.2.2

theorem nfun_zero_out (x : Node) {γ : Ordinal.{0}} (hγ : nht x ≤ γ) : nfun x γ = 0 :=
  (good (nht x) (nht_lt x)).zero_out _ (nfun_mem x) γ hγ

theorem nfun_mono (x : Node) {γ δ : Ordinal.{0}} (h : γ < δ) (hδ : δ < nht x) :
    nfun x γ < nfun x δ :=
  (good (nht x) (nht_lt x)).mono _ (nfun_mem x) γ δ h hδ

theorem node_ext {x y : Node} (h1 : nht x = nht y) (h2 : ∀ γ < nht x, nfun x γ = nfun y γ) :
    x = y := by
  refine Subtype.ext (Prod.ext h1 ?_)
  funext γ
  show nfun x γ = nfun y γ
  by_cases hγ : γ < nht x
  · exact h2 γ hγ
  · rw [nfun_zero_out x (not_lt.mp hγ), nfun_zero_out y (h1 ▸ not_lt.mp hγ)]

theorem nle_refl (x : Node) : nle x x := ⟨le_rfl, fun _ _ => rfl⟩

theorem nle_trans {x y z : Node} (h1 : nle x y) (h2 : nle y z) : nle x z :=
  ⟨h1.1.trans h2.1, fun γ hγ => (h1.2 γ hγ).trans (h2.2 γ (lt_of_lt_of_le hγ h1.1))⟩

theorem nle_antisymm {x y : Node} (h1 : nle x y) (h2 : nle y x) : x = y :=
  node_ext (le_antisymm h1.1 h2.1) h1.2

theorem nht_lt_of_nle {x y : Node} (h : nle x y) (hne : x ≠ y) : nht x < nht y := by
  rcases lt_or_eq_of_le h.1 with h' | h'
  · exact h'
  · exact absurd (node_ext h' h.2) hne

/-- Every level below `ω₁` contains a node. -/
theorem L_nonempty {β : Ordinal.{0}} (hβ : β < ω₁) : (L β).Nonempty := by
  rcases eq_or_ne β 0 with rfl | h0
  · exact ⟨fun _ => 0, by rw [L_zero]; rfl⟩
  · have hpos : (0 : Ordinal.{0}) < β := pos_iff_ne_zero.mpr h0
    obtain ⟨g, hg, -, -⟩ :=
      (good β hβ).ext 0 hpos (fun _ => 0) (by rw [L_zero]; rfl) 1 ⟨0, by norm_num, by simp⟩
    exact ⟨g, hg⟩

theorem levels_nonempty {β : Ordinal.{0}} (hβ : β < ω₁) : ∃ x : Node, nht x = β := by
  obtain ⟨f, hf⟩ := L_nonempty hβ
  exact ⟨⟨(β, f), hβ, hf⟩, rfl⟩

theorem levels_countable (β : Ordinal.{0}) : {x : Node | nht x = β}.Countable := by
  rcases lt_or_ge β ω₁ with hβ | hβ
  · have hmaps : Set.MapsTo nfun {x : Node | nht x = β} (L β) := by
      intro x hx
      have : nht x = β := hx
      rw [← this]
      exact nfun_mem x
    have hinj : Set.InjOn nfun {x : Node | nht x = β} := by
      intro x hx y hy hxy
      have hx' : nht x = β := hx
      have hy' : nht y = β := hy
      refine node_ext (hx'.trans hy'.symm) ?_
      intro γ _
      rw [show nfun x = nfun y from hxy]
    exact hmaps.countable_of_injOn hinj (good β hβ).ctble
  · have : {x : Node | nht x = β} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd (h ▸ nht_lt x) (not_lt.mpr hβ)
    rw [this]
    exact Set.countable_empty

/-- The tree property: the predecessors of a node of height `α` are indexed by the
ordinals below `α`. -/
theorem exists_unique_pred (x : Node) {β : Ordinal.{0}} (hβ : β < nht x) :
    ∃! y : Node, nle y x ∧ nht y = β := by
  have hβ1 : β < ω₁ := hβ.trans (nht_lt x)
  have hmem : trunc β (nfun x) ∈ L β := (good (nht x) (nht_lt x)).coh β hβ _ (nfun_mem x)
  refine ⟨⟨(β, trunc β (nfun x)), hβ1, hmem⟩, ⟨⟨le_of_lt hβ, ?_⟩, rfl⟩, ?_⟩
  · intro γ hγ
    have hγ' : γ < β := hγ
    show trunc β (nfun x) γ = nfun x γ
    rw [trunc, if_pos hγ']
  · rintro y ⟨hy, hy'⟩
    refine node_ext hy' ?_
    intro γ hγ
    rw [hy.2 γ hγ]
    show nfun x γ = trunc β (nfun x) γ
    rw [trunc, if_pos (hy' ▸ hγ)]

/-- Chains in the tree are countable: there is no uncountable branch. -/
theorem chain_countable (b : Set Node) (hb : IsChain nle b) : b.Countable := by
  -- the height map is injective on a chain
  have hinj : Set.InjOn nht b := by
    intro x hx y hy hxy
    rcases eq_or_ne x y with h | h
    · exact h
    · rcases hb hx hy h with h1 | h1
      · exact absurd hxy (ne_of_lt (nht_lt_of_nle h1 h))
      · exact absurd hxy.symm (ne_of_lt (nht_lt_of_nle h1 (Ne.symm h)))
  refine (Set.mapsTo_image nht b).countable_of_injOn hinj ?_
  -- the set of heights is countable
  set H : Set Ordinal.{0} := nht '' b with hH
  set H' : Set Ordinal.{0} := {a ∈ H | ∃ a' ∈ H, a < a'} with hH'
  have hsplit : H ⊆ H' ∪ (H \ H') := by
    intro a ha
    by_cases h : a ∈ H'
    · exact Or.inl h
    · exact Or.inr ⟨ha, h⟩
  refine Set.Countable.mono hsplit (Set.Countable.union ?_ ?_)
  · -- `H'` injects into `ℚ`
    classical
    set F : Ordinal.{0} → ℚ := fun a =>
      if h : ∃ y, y ∈ b ∧ a < nht y then nfun h.choose a else 0 with hF
    have hFspec : ∀ a ∈ H', ∃ y, y ∈ b ∧ a < nht y ∧ F a = nfun y a := by
      intro a ha
      have h : ∃ y, y ∈ b ∧ a < nht y := by
        obtain ⟨-, a', ⟨y, hy, rfl⟩, haa'⟩ := ha
        exact ⟨y, hy, haa'⟩
      exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
    have hmono : ∀ a ∈ H', ∀ a' ∈ H', a < a' → F a < F a' := by
      intro a ha a' ha' haa'
      obtain ⟨y, hy, hy1, hy2⟩ := hFspec a ha
      obtain ⟨z, hz, hz1, hz2⟩ := hFspec a' ha'
      -- pass to the larger of `y` and `z`
      have key : ∃ w ∈ b, a < nht w ∧ a' < nht w ∧ nfun y a = nfun w a ∧ nfun z a' = nfun w a' := by
        rcases eq_or_ne y z with rfl | hne
        · exact ⟨y, hy, hy1, hz1, rfl, rfl⟩
        · rcases hb hy hz hne with h1 | h1
          · exact ⟨z, hz, haa'.trans hz1, hz1, h1.2 a hy1, rfl⟩
          · exact ⟨y, hy, hy1, lt_of_lt_of_le hz1 h1.1, rfl, h1.2 a' hz1⟩
      obtain ⟨w, -, hw1, hw2, hw3, hw4⟩ := key
      rw [hy2, hz2, hw3, hw4]
      exact nfun_mono w haa' hw2
    have hinj' : Set.InjOn F H' := by
      intro a ha a' ha' hFa
      rcases lt_trichotomy a a' with h | h | h
      · exact absurd hFa (ne_of_lt (hmono a ha a' ha' h))
      · exact h
      · exact absurd hFa.symm (ne_of_lt (hmono a' ha' a ha h))
    exact (Set.mapsTo_univ F H').countable_of_injOn hinj' Set.countable_univ
  · -- at most one maximal height
    have : (H \ H').Subsingleton := by
      intro a ha a' ha'
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact ha.2 ⟨ha.1, a', ha'.1, h⟩
      · exact ha'.2 ⟨ha'.1, a, ha.1, h⟩
    exact this.countable

end Aronszajn

import Mathlib
import RequestProject.Aronszajn
import RequestProject.AronszajnTree

-- (Lean requires `import` lines to come first in a file; the header comment follows.)

/-!
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option pp.piBinderTypes true

set_option grind.warning false

open Ordinal

namespace Frontier

/-- **There exists an Aronszajn tree.**

We exhibit a type `T` with a partial order `le` and a height function `ht` such that:

* `le` is a partial order (reflexive, transitive, antisymmetric);
* every node has height `< ω₁`, and `le`-smaller nodes have strictly smaller height;
* for every node `x` and every `β < ht x` there is a *unique* predecessor of `x` of
  height `β` (so the predecessors of `x` are well-ordered with order type `ht x`,
  i.e. `T` is a tree and `ht` is its height function);
* every level `β < ω₁` is nonempty, so the tree has height exactly `ω₁`;
* every level is countable;
* every chain (in particular every branch) is countable, so there is no uncountable
  branch.
-/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (le : T → T → Prop) (ht : T → Ordinal.{0}),
      (∀ x, le x x) ∧
      (∀ x y z, le x y → le y z → le x z) ∧
      (∀ x y, le x y → le y x → x = y) ∧
      (∀ x, ht x < ω₁) ∧
      (∀ x y, le x y → x ≠ y → ht x < ht y) ∧
      (∀ x, ∀ β < ht x, ∃! y, le y x ∧ ht y = β) ∧
      (∀ β < ω₁, ∃ x, ht x = β) ∧
      (∀ β, {x | ht x = β}.Countable) ∧
      (∀ b : Set T, IsChain le b → b.Countable) := by
  refine ⟨Aronszajn.Node, Aronszajn.nle, Aronszajn.nht, Aronszajn.nle_refl,
    fun _ _ _ => Aronszajn.nle_trans, fun _ _ => Aronszajn.nle_antisymm, Aronszajn.nht_lt,
    fun _ _ => Aronszajn.nht_lt_of_nle, fun x _ hβ => Aronszajn.exists_unique_pred x hβ,
    fun _ hβ => Aronszajn.levels_nonempty hβ, Aronszajn.levels_countable,
    Aronszajn.chain_countable⟩

end Frontier

