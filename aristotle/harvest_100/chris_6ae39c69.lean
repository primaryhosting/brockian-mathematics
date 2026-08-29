import Mathlib
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Set Cardinal Ordinal
open scoped Ordinal Cardinal

namespace Frontier

/-! ## Countable ordinals -/

/-- The set of ordinals below `a` is countable exactly when `a < ω₁`. -/
theorem countable_Iio_iff (a : Ordinal.{0}) : (Set.Iio a).Countable ↔ a < ω₁ := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal,
    ← Cardinal.ord_aleph, Cardinal.lt_ord, Cardinal.lift_lt_aleph_one]

/-! ## Cofinal `ω`-sequences below a countable limit ordinal -/

/-- `c` is a sequence of ordinals below `l` which is cofinal in `l`. -/
def IsCofSeq (l : Ordinal.{0}) (c : ℕ → Ordinal.{0}) : Prop :=
  (∀ n, c n < l) ∧ ∀ ξ < l, ∃ n, ξ < c n

/-- Every countable limit ordinal has a cofinal `ω`-sequence. -/
theorem exists_cofSeq {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hlt : l < ω₁) :
    ∃ c, IsCofSeq l c := by
  have hc : (Set.Iio l).Countable := (countable_Iio_iff l).2 hlt
  have hne : (Set.Iio l).Nonempty := ⟨0, hl.bot_lt⟩
  obtain ⟨f, hf⟩ := hc.exists_eq_range hne
  refine ⟨fun n => Nat.rec 0 (fun m ih => Order.succ (max ih (f m))) n, ?_, ?_⟩
  · intro n
    induction n with
    | zero => exact hl.bot_lt
    | succ m ih =>
        have hfm : f m < l := by
          have : f m ∈ Set.Iio l := by rw [hf]; exact ⟨m, rfl⟩
          exact this
        exact hl.succ_lt (max_lt ih hfm)
  · intro ξ hξ
    have : ξ ∈ Set.range f := by rw [← hf]; exact hξ
    obtain ⟨n, rfl⟩ := this
    exact ⟨n + 1, lt_of_le_of_lt (le_max_right _ _) (Order.lt_succ_of_not_isMax (by simp))⟩

/-- A choice of cofinal `ω`-sequence below `l` (junk if none exists). -/
noncomputable def cofSeq (l : Ordinal.{0}) : ℕ → Ordinal.{0} :=
  if h : ∃ c, IsCofSeq l c then h.choose else fun _ => 0

theorem cofSeq_spec {l : Ordinal.{0}} (h : ∃ c, IsCofSeq l c) : IsCofSeq l (cofSeq l) := by
  rw [cofSeq, dif_pos h]; exact h.choose_spec

/-- The least index `n` with `ξ < cofSeq l n`. -/
noncomputable def blockIdx (l ξ : Ordinal.{0}) : ℕ :=
  if h : ∃ n, ξ < cofSeq l n then Nat.find h else 0

theorem lt_cofSeq_blockIdx {l ξ : Ordinal.{0}} (h : ∃ n, ξ < cofSeq l n) :
    ξ < cofSeq l (blockIdx l ξ) := by
  rw [blockIdx, dif_pos h]; exact Nat.find_spec h

theorem blockIdx_le {l ξ : Ordinal.{0}} {n : ℕ} (h : ξ < cofSeq l n) : blockIdx l ξ ≤ n := by
  have hex : ∃ n, ξ < cofSeq l n := ⟨n, h⟩
  rw [blockIdx, dif_pos hex]
  exact Nat.find_le h

/-! ## The coherent sequence -/

/-- The successor step. -/
noncomputable def succStep (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Ordinal.{0} → ℕ :=
  fun ξ => if ξ < a then f ξ else 0

/-- The limit step: patch together the previously constructed functions along a cofinal
`ω`-sequence, using `max` with the block index to keep the result finite-to-one. -/
noncomputable def limitStep (l : Ordinal.{0}) (P : Ordinal.{0} → Ordinal.{0} → ℕ) :
    Ordinal.{0} → ℕ :=
  fun ξ => if ξ < l then max (P (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) else 0

/-- `E a : Ordinal → ℕ` is (below `a`) a finite-to-one function, and the family `E` is
coherent: `E a` and `E b` agree on all but finitely many `ξ < b` whenever `b < a < ω₁`. -/
noncomputable def E : Ordinal.{0} → Ordinal.{0} → ℕ := fun a =>
  Ordinal.limitRecOn a (fun _ => 0) succStep
    (fun l _ prev => limitStep l (fun o => if h : o < l then prev o h else fun _ => 0))

theorem E_zero : E 0 = fun _ => 0 := by rw [E, Ordinal.limitRecOn_zero]

theorem E_succ (a : Ordinal.{0}) : E (Order.succ a) = succStep a (E a) := by
  rw [E, Ordinal.limitRecOn_succ]; rfl

theorem E_limit {l : Ordinal.{0}} (hl : Order.IsSuccLimit l) :
    E l = limitStep l (fun o => if _h : o < l then E o else fun _ => 0) := by
  rw [E, Ordinal.limitRecOn_limit _ _ _ _ hl]; rfl

theorem E_limit_apply {l ξ : Ordinal.{0}} (hl : Order.IsSuccLimit l) (hξ : ξ < l)
    (hc : cofSeq l (blockIdx l ξ) < l) :
    E l ξ = max (E (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) := by
  rw [E_limit hl, limitStep, if_pos hξ, dif_pos hc]

/-! ## The invariant -/

/-- The invariant maintained by the recursion: `E a` vanishes outside `Iio a`, it is
finite-to-one on `Iio a`, and it coheres with all earlier `E b`. -/
def Inv (a : Ordinal.{0}) : Prop :=
  (∀ ξ, a ≤ ξ → E a ξ = 0) ∧ (∀ k : ℕ, {ξ | ξ < a ∧ E a ξ = k}.Finite) ∧
    (∀ b < a, {ξ | ξ < b ∧ E a ξ ≠ E b ξ}.Finite)

theorem finite_lt_of_finToOne {a : Ordinal.{0}} {f : Ordinal.{0} → ℕ}
    (hf : ∀ k : ℕ, {ξ | ξ < a ∧ f ξ = k}.Finite) (m : ℕ) : {ξ | ξ < a ∧ f ξ < m}.Finite := by
  refine Set.Finite.subset ((Set.finite_Iio m).biUnion (fun k _ => hf k)) ?_
  rintro ξ ⟨h1, h2⟩
  exact Set.mem_biUnion h2 ⟨h1, rfl⟩

theorem finite_le_of_finToOne {a : Ordinal.{0}} {f : Ordinal.{0} → ℕ}
    (hf : ∀ k : ℕ, {ξ | ξ < a ∧ f ξ = k}.Finite) (m : ℕ) : {ξ | ξ < a ∧ f ξ ≤ m}.Finite := by
  refine Set.Finite.subset (finite_lt_of_finToOne hf (m + 1)) ?_
  rintro ξ ⟨h1, h2⟩
  exact ⟨h1, Nat.lt_succ_of_le h2⟩

/-- Coherence between two members of the family, in either order. -/
theorem coh_pair {x y : Ordinal.{0}} (hx : Inv x) (hy : Inv y) :
    {ξ | ξ < x ∧ ξ < y ∧ E x ξ ≠ E y ξ}.Finite := by
  rcases lt_trichotomy x y with h | h | h
  · refine Set.Finite.subset (hy.2.2 x h) ?_
    rintro ξ ⟨h1, _, h3⟩
    exact ⟨h1, fun hc => h3 hc.symm⟩
  · subst h
    convert Set.finite_empty
    ext ξ
    simp
  · refine Set.Finite.subset (hx.2.2 y h) ?_
    rintro ξ ⟨_, h2, h3⟩
    exact ⟨h2, h3⟩

theorem Inv_zero : Inv 0 := by
  refine ⟨fun ξ _ => by rw [E_zero], fun k => ?_, fun b hb => absurd hb (by simp)⟩
  convert Set.finite_empty
  ext ξ
  simp

theorem Inv_succ {a : Ordinal.{0}} (ha : Inv a) : Inv (Order.succ a) := by
  have key : ∀ ξ : Ordinal.{0}, ξ < a → E (Order.succ a) ξ = E a ξ := by
    intro ξ hξ
    rw [E_succ, succStep, if_pos hξ]
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    have : ¬ ξ < a := fun h => absurd (h.trans_le (Order.le_succ a)) (not_lt.2 hξ)
    rw [E_succ, succStep, if_neg this]
  · intro k
    refine Set.Finite.subset ((ha.2.1 k).union (Set.finite_singleton a)) ?_
    rintro ξ ⟨h1, h2⟩
    rcases lt_or_eq_of_le (Order.lt_succ_iff.1 h1) with h | h
    · exact Or.inl ⟨h, by rwa [key ξ h] at h2⟩
    · exact Or.inr h
  · intro b hb
    have hba : b ≤ a := Order.lt_succ_iff.1 hb
    rcases lt_or_eq_of_le hba with h | h
    · refine Set.Finite.subset (ha.2.2 b h) ?_
      rintro ξ ⟨h1, h2⟩
      exact ⟨h1, by rwa [key ξ (h1.trans h)] at h2⟩
    · subst h
      convert Set.finite_empty
      ext ξ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
      intro hξ
      exact key ξ hξ

theorem Inv_limit {l : Ordinal.{0}} (hl : Order.IsSuccLimit l)
    (hex : ∃ c, IsCofSeq l c) (ih : ∀ b < l, Inv b) : Inv l := by
  obtain ⟨hc1, hc2⟩ := cofSeq_spec hex
  have hidx : ∀ ξ, ξ < l → ξ < cofSeq l (blockIdx l ξ) := fun ξ hξ =>
    lt_cofSeq_blockIdx (hc2 ξ hξ)
  have hval : ∀ ξ, ξ < l → E l ξ = max (E (cofSeq l (blockIdx l ξ)) ξ) (blockIdx l ξ) :=
    fun ξ hξ => E_limit_apply hl hξ (hc1 _)
  refine ⟨?_, ?_, ?_⟩
  · intro ξ hξ
    rw [E_limit hl, limitStep, if_neg (not_lt.2 hξ)]
  · intro k
    refine Set.Finite.subset ((Set.finite_Iio (k + 1)).biUnion
      (fun m (_ : m ∈ Set.Iio (k + 1)) =>
        finite_le_of_finToOne (ih (cofSeq l m) (hc1 m)).2.1 k)) ?_
    rintro ξ ⟨h1, h2⟩
    rw [hval ξ h1] at h2
    exact Set.mem_biUnion (x := blockIdx l ξ) (Nat.lt_succ_of_le (h2 ▸ le_max_right _ _))
      ⟨hidx ξ h1, h2 ▸ le_max_left _ _⟩
  · intro b hb
    obtain ⟨N, hN⟩ := hc2 b hb
    have hfin1 : (⋃ m ∈ Set.Iio (N + 1),
        {ξ : Ordinal.{0} | ξ < cofSeq l m ∧ ξ < b ∧ E (cofSeq l m) ξ ≠ E b ξ}).Finite :=
      (Set.finite_Iio (N + 1)).biUnion
        (fun m _ => coh_pair (ih (cofSeq l m) (hc1 m)) (ih b hb))
    have hfin2 : {ξ : Ordinal.{0} | ξ < b ∧ E b ξ < N + 1}.Finite :=
      finite_lt_of_finToOne (ih b hb).2.1 (N + 1)
    refine Set.Finite.subset (hfin1.union hfin2) ?_
    rintro ξ ⟨h1, h2⟩
    have hξl : ξ < l := h1.trans hb
    have hbn : blockIdx l ξ ≤ N := blockIdx_le (h1.trans hN)
    rw [hval ξ hξl] at h2
    by_cases hcase : E (cofSeq l (blockIdx l ξ)) ξ = E b ξ
    · refine Or.inr ⟨h1, ?_⟩
      rw [hcase] at h2
      have hnle : ¬ (blockIdx l ξ ≤ E b ξ) := fun hle => h2 (max_eq_left hle)
      omega
    · exact Or.inl (Set.mem_biUnion (x := blockIdx l ξ)
        (Nat.lt_succ_of_le hbn) ⟨hidx ξ hξl, h1, hcase⟩)

/-- The invariant holds at every countable ordinal. -/
theorem Inv_of_lt_omega1 : ∀ a : Ordinal.{0}, a < ω₁ → Inv a := by
  intro a
  induction a using Ordinal.limitRecOn with
  | zero => exact fun _ => Inv_zero
  | succ a ih => exact fun ha => Inv_succ (ih (lt_of_le_of_lt (Order.le_succ a) ha))
  | limit l hl ih =>
      exact fun ha => Inv_limit hl (exists_cofSeq hl ha) (fun b hb => ih b hb (hb.trans ha))

end Frontier

