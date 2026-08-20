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

/-
The limit step of the transfinite construction: at a countable limit ordinal `a`
we build a nice partial injection with domain `a` coherent with all previous ones,
by an `ω`-recursion along a cofinal sequence, reserving one new value at each stage
so that the resulting function still omits infinitely many naturals.
-/
import RequestProject.Aronszajn.Step

open Ordinal Cardinal Set

namespace Aronszajn

theorem exists_limit_step {a : Ordinal.{0}} (ha : a < ω₁) (ha0 : 0 < a)
    (halim : ∀ b < a, b + 1 < a) {d : Ordinal.{0} → Ordinal.{0} → ℕ}
    (hd : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c) :
    ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b := by
  classical
  obtain ⟨seq, hseq0, hseqlt, hseqmono, hseqcof⟩ := exists_cofinal_seq ha ha0 halim
  set St := (Ordinal.{0} → ℕ) × Finset ℕ with hSt
  set Q : ℕ → St → Prop := fun n s =>
    Nice (seq n) s.1 ∧ (∀ b ≤ seq n, Coh s.1 (d b) b) ∧ s.2.card = n ∧
      (∀ x ∈ s.2, ∀ e < seq n, s.1 e ≠ x) with hQdef
  -- the initial stage
  have hs0 : Q 0 ((fun _ => 0 : Ordinal.{0} → ℕ), (∅ : Finset ℕ)) := by
    refine ⟨by rw [hseq0]; exact nice_zero, ?_, rfl, by simp⟩
    intro b hb
    rw [hseq0] at hb
    have : b = 0 := le_antisymm hb (by simp)
    subst this
    exact coh_of_eq fun e he => absurd he (by simp)
  -- the recursion step
  have hstep : ∀ (n : ℕ) (s : St), Q n s →
      ∃ s' : St, Q (n + 1) s' ∧ s.2 ⊆ s'.2 ∧ ∀ e < seq n, s'.1 e = s.1 e := by
    intro n s hs
    obtain ⟨hnice, hcohs, hcard, havoid⟩ := hs
    have hlt : seq n < seq (n + 1) := hseqmono (Nat.lt_succ_self n)
    -- a fresh reserved value
    obtain ⟨r, hr1, hr2⟩ := (hnice.2.2.diff s.2.finite_toSet).nonempty
    have hcoh1 : Coh s.1 (d (seq (n + 1))) (seq n) :=
      (hcohs (seq n) le_rfl).trans
        (((hd (seq (n + 1)) (hseqlt _)).2 (seq n) hlt).symm)
    have hS : ∀ e < seq n, s.1 e ∉ ((insert r s.2 : Finset ℕ) : Set ℕ) := by
      intro e he hmem
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hmem
      rcases hmem with h | h
      · exact hr1 e he h
      · exact havoid _ h e he rfl
    obtain ⟨f', hf'nice, hf'agree, hf'coh, hf'avoid⟩ :=
      exists_extend hlt.le hnice (hd (seq (n + 1)) (hseqlt _)).1 hcoh1
        (insert r s.2 : Finset ℕ).finite_toSet hS
    refine ⟨(f', insert r s.2), ⟨hf'nice, ?_, ?_, ?_⟩, Finset.subset_insert _ _, hf'agree⟩
    · intro b hb
      rcases lt_or_eq_of_le hb with hb' | rfl
      · exact (hf'coh.mono hb'.le).trans ((hd (seq (n + 1)) (hseqlt _)).2 b hb')
      · exact hf'coh
    · rw [Finset.card_insert_of_notMem hr2, hcard]
    · intro x hx e he
      have := hf'avoid e he
      simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at this
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact this.1
      · intro hEq
        have hEq' : f' e = x := hEq
        exact this.2 (by rw [hEq']; exact hx)
  choose! next hnextQ hnextsub hnextagree using hstep
  set F : ℕ → St := fun n => Nat.rec ((fun _ => 0 : Ordinal.{0} → ℕ), (∅ : Finset ℕ))
    (fun n s => next n s) n with hFdef
  have hQF : ∀ n, Q n (F n) := by
    intro n
    induction n with
    | zero => exact hs0
    | succ n ih => exact hnextQ n (F n) ih
  have hsub1 : ∀ n, (F n).2 ⊆ (F (n + 1)).2 := fun n => hnextsub n (F n) (hQF n)
  have hagree1 : ∀ n, ∀ e < seq n, (F (n + 1)).1 e = (F n).1 e :=
    fun n => hnextagree n (F n) (hQF n)
  have hsub : ∀ m n, m ≤ n → (F m).2 ⊆ (F n).2 := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact subset_rfl
    | succ n hmn ih => exact ih.trans (hsub1 n)
  have hagree : ∀ m n, m ≤ n → ∀ e < seq m, (F n).1 e = (F m).1 e := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro e _; rfl
    | succ n hmn ih =>
      intro e he
      have hlt : e < seq n := lt_of_lt_of_le he (hseqmono.monotone hmn)
      rw [hagree1 n e hlt, ih e he]
  -- the union of the stages
  set f : Ordinal.{0} → ℕ := fun e => if h : ∃ n, e < seq n then (F (Nat.find h)).1 e else 0
    with hfdef
  have hfval : ∀ n e, e < seq n → f e = (F n).1 e := by
    intro n e he
    have hex : ∃ m, e < seq m := ⟨n, he⟩
    rw [hfdef]
    simp only [dif_pos hex]
    have hm : e < seq (Nat.find hex) := Nat.find_spec hex
    have h1 : (F (max (Nat.find hex) n)).1 e = (F (Nat.find hex)).1 e :=
      hagree _ _ (le_max_left _ _) e hm
    have h2 : (F (max (Nat.find hex) n)).1 e = (F n).1 e :=
      hagree _ _ (le_max_right _ _) e he
    rw [← h1, h2]
  have hcof2 : ∀ e₁ < a, ∀ e₂ < a, ∃ n, e₁ < seq n ∧ e₂ < seq n := by
    intro e₁ h₁ e₂ h₂
    obtain ⟨n₁, hn₁⟩ := hseqcof e₁ h₁
    obtain ⟨n₂, hn₂⟩ := hseqcof e₂ h₂
    exact ⟨max n₁ n₂, lt_of_lt_of_le hn₁ (hseqmono.monotone (le_max_left _ _)),
      lt_of_lt_of_le hn₂ (hseqmono.monotone (le_max_right _ _))⟩
  refine ⟨f, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- injective below `a`
    intro e₁ h₁ e₂ h₂ hEq
    obtain ⟨n, hn₁, hn₂⟩ := hcof2 e₁ h₁ e₂ h₂
    refine (hQF n).1.1 e₁ hn₁ e₂ hn₂ ?_
    rw [← hfval n e₁ hn₁, ← hfval n e₂ hn₂]
    exact hEq
  · -- vanishes from `a` on
    intro e hae
    have : ¬ ∃ n, e < seq n := by
      rintro ⟨n, hn⟩
      exact absurd (lt_of_lt_of_le (hn.trans (hseqlt n)) hae) (lt_irrefl e)
    rw [hfdef]; simp only [dif_neg this]
  · -- omits infinitely many values
    have hWsub : ∀ n, ∀ x ∈ (F n).2, ∀ e < a, f e ≠ x := by
      intro n x hx e he
      obtain ⟨m, hm⟩ := hseqcof e he
      have hkm : e < seq (max m n) := lt_of_lt_of_le hm (hseqmono.monotone (le_max_left _ _))
      rw [hfval (max m n) e hkm]
      exact (hQF (max m n)).2.2.2 x (hsub n (max m n) (le_max_right _ _) hx) e hkm
    by_contra hfin
    rw [CoInf, Set.not_infinite] at hfin
    have hcard : ∀ n, n ≤ hfin.toFinset.card := by
      intro n
      rw [← (hQF n).2.2.1]
      apply Finset.card_le_card
      intro x hx
      rw [Set.Finite.mem_toFinset]
      exact fun e he => hWsub n x hx e he
    exact absurd (hcard (hfin.toFinset.card + 1)) (by omega)
  · -- coherent with all previous functions
    intro b hb
    obtain ⟨n, hn⟩ := hseqcof b hb
    refine Coh.trans (coh_of_eq ?_) ((hQF n).2.1 b hn.le)
    intro e he
    exact hfval n e (lt_trans he hn)

end Aronszajn

/-
The transfinite construction of a coherent sequence `E` of partial injections:
for every countable ordinal `a`, `E a` is injective below `a`, omits infinitely
many naturals, and agrees with `E b` below `b` up to finitely many exceptions,
for every `b < a`.
-/
import RequestProject.Aronszajn.Limit

open Ordinal Cardinal Set

namespace Aronszajn

/-- One step of the transfinite construction, all three cases at once. -/
theorem exists_step (a : Ordinal.{0}) (ha : a < ω₁) (d : Ordinal.{0} → Ordinal.{0} → ℕ)
    (hd : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c) :
    ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact ⟨fun _ => 0, nice_zero, fun b hb => absurd hb (by simp)⟩
  by_cases hsucc : ∃ b, a = b + 1
  · obtain ⟨b, rfl⟩ := hsucc
    have hb : b < b + 1 := Order.lt_add_one_iff.2 le_rfl
    obtain ⟨f, hfnice, hfagree⟩ := exists_succ_step (hd b hb).1
    refine ⟨f, hfnice, fun c hc => ?_⟩
    rw [Order.lt_add_one_iff] at hc
    have hagree : Coh f (d b) c := coh_of_eq fun e he => hfagree e (lt_of_lt_of_le he hc)
    rcases lt_or_eq_of_le hc with hc' | rfl
    · exact hagree.trans ((hd b hb).2 c hc')
    · exact hagree
  · have ha0' : 0 < a := lt_of_le_of_ne (by simp) (Ne.symm ha0)
    have halim : ∀ b < a, b + 1 < a := by
      intro b hb
      have h1 : b + 1 ≤ a := Order.add_one_le_iff.2 hb
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exact absurd ⟨b, h.symm⟩ hsucc
    exact exists_limit_step ha ha0' halim hd

open Classical in
/-- The choice of the next function in the transfinite construction. -/
noncomputable def stepFun (a : Ordinal.{0}) (d : Ordinal.{0} → Ordinal.{0} → ℕ) :
    Ordinal.{0} → ℕ :=
  if h : ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b then h.choose else fun _ => 0

theorem stepFun_spec {a : Ordinal.{0}} {d : Ordinal.{0} → Ordinal.{0} → ℕ}
    (h : ∃ f, Nice a f ∧ ∀ b < a, Coh f (d b) b) :
    Nice a (stepFun a d) ∧ ∀ b < a, Coh (stepFun a d) (d b) b := by
  classical
  rw [stepFun, dif_pos h]
  exact h.choose_spec

open Classical in
/-- The coherent sequence of partial injections. -/
noncomputable def E : Ordinal.{0} → Ordinal.{0} → ℕ :=
  (inferInstanceAs (IsWellFounded Ordinal.{0} (· < ·))).wf.fix
    (fun a IH => stepFun a (fun b => if h : b < a then IH b h else fun _ => 0))

open Classical in
theorem E_eq (a : Ordinal.{0}) :
    E a = stepFun a (fun b => if b < a then E b else fun _ => 0) := by
  classical
  rw [E, WellFounded.fix_eq]
  rfl

/-- The defining property of `E`. -/
theorem E_spec : ∀ a < ω₁, Nice a (E a) ∧ ∀ b < a, Coh (E a) (E b) b := by
  intro a
  induction a using Ordinal.induction with
  | _ a IH =>
    intro ha
    classical
    set d : Ordinal.{0} → Ordinal.{0} → ℕ := fun b => if b < a then E b else fun _ => 0 with hd
    have hdval : ∀ b < a, d b = E b := by intro b hb; rw [hd]; simp [hb]
    have hdgood : ∀ b < a, Nice b (d b) ∧ ∀ c < b, Coh (d b) (d c) c := by
      intro b hb
      rw [hdval b hb]
      refine ⟨(IH b hb (hb.trans ha)).1, fun c hc => ?_⟩
      rw [hdval c (hc.trans hb)]
      exact (IH b hb (hb.trans ha)).2 c hc
    have hex := exists_step a ha d hdgood
    have := stepFun_spec hex
    rw [← E_eq a] at this
    refine ⟨this.1, fun b hb => ?_⟩
    have h2 := this.2 b hb
    rwa [hdval b hb] at h2

end Aronszajn

/-
The Aronszajn tree built from the coherent sequence `E`: its nodes are the
functions which are injective below some countable ordinal `a`, vanish from `a`
on, and differ from `E a` in only finitely many places; the order is end-extension.
-/
import RequestProject.Aronszajn.Coherent

open Ordinal Cardinal Set

namespace Aronszajn

/-- The set of nodes of the tree. A node is a pair `(a, f)` where `a < ω₁`, `f` is
injective below `a`, vanishes from `a` on, and differs from `E a` finitely often. -/
def TreeSet : Set (Ordinal.{0} × (Ordinal.{0} → ℕ)) :=
  {p | p.1 < ω₁ ∧ InjBelow p.1 p.2 ∧ Norm p.1 p.2 ∧ Coh p.2 (E p.1) p.1}

/-- The type of nodes of the tree. -/
def TreeNode : Type 1 := ↥TreeSet

/-- The level of a node. -/
def tlvl (x : TreeNode) : Ordinal.{0} := x.1.1

/-- The tree order: end-extension. -/
def tle (x y : TreeNode) : Prop := tlvl x ≤ tlvl y ∧ ∀ e < tlvl x, x.1.2 e = y.1.2 e

theorem tlvl_lt_omega1 (x : TreeNode) : tlvl x < ω₁ := x.2.1

theorem injBelow_node (x : TreeNode) : InjBelow (tlvl x) x.1.2 := x.2.2.1

theorem norm_node (x : TreeNode) : Norm (tlvl x) x.1.2 := x.2.2.2.1

theorem coh_node (x : TreeNode) : Coh x.1.2 (E (tlvl x)) (tlvl x) := x.2.2.2.2

/-- Two nodes with the same level agreeing below it are equal. -/
theorem node_ext {x y : TreeNode} (hl : tlvl x = tlvl y)
    (hf : ∀ e < tlvl x, x.1.2 e = y.1.2 e) : x = y := by
  have hfun : x.1.2 = y.1.2 := by
    funext e
    rcases lt_or_ge e (tlvl x) with he | he
    · exact hf e he
    · rw [norm_node x e he, norm_node y e (hl ▸ he)]
  apply Subtype.ext
  exact Prod.ext hl hfun

theorem tle_refl (x : TreeNode) : tle x x := ⟨le_rfl, fun _ _ => rfl⟩

theorem tle_trans {x y z : TreeNode} (hxy : tle x y) (hyz : tle y z) : tle x z :=
  ⟨hxy.1.trans hyz.1, fun e he => by
    rw [hxy.2 e he, hyz.2 e (lt_of_lt_of_le he hxy.1)]⟩

theorem tle_antisymm {x y : TreeNode} (hxy : tle x y) (hyx : tle y x) : x = y :=
  node_ext (le_antisymm hxy.1 hyx.1) hxy.2

/-- Comparable nodes of the same level are equal. -/
theorem eq_of_tle_of_lvl_eq {x y : TreeNode} (hxy : tle x y) (hl : tlvl x = tlvl y) : x = y :=
  node_ext hl hxy.2

/-- Predecessors of a node are linearly ordered. -/
theorem tle_total_of_le {x y z : TreeNode} (hy : tle y x) (hz : tle z x) : tle y z ∨ tle z y := by
  rcases le_total (tlvl y) (tlvl z) with h | h
  · exact Or.inl ⟨h, fun e he => by rw [hy.2 e he, ← hz.2 e (lt_of_lt_of_le he h)]⟩
  · exact Or.inr ⟨h, fun e he => by rw [hz.2 e he, ← hy.2 e (lt_of_lt_of_le he h)]⟩

/-- The restriction of a node to a smaller level is again a node. -/
theorem restrict_mem {x : TreeNode} {b : Ordinal.{0}} (hb : b < tlvl x) :
    (b, fun e => if e < b then x.1.2 e else 0) ∈ TreeSet := by
  classical
  refine ⟨hb.trans (tlvl_lt_omega1 x), ?_, ?_, ?_⟩
  · intro e he f hf hef
    simp only [if_pos he, if_pos hf] at hef
    exact injBelow_node x e (he.trans hb) f (hf.trans hb) hef
  · intro e hbe
    simp [not_lt.2 hbe]
  · refine Coh.trans (g := x.1.2) (coh_of_eq ?_) ?_
    · intro e he; simp [he]
    · exact ((coh_node x).mono hb.le).trans
        ((E_spec (tlvl x) (tlvl_lt_omega1 x)).2 b hb)

theorem exists_unique_pred (x : TreeNode) {b : Ordinal.{0}} (hb : b < tlvl x) :
    ∃! y : TreeNode, tle y x ∧ tlvl y = b := by
  classical
  refine ⟨⟨_, restrict_mem hb⟩, ⟨⟨hb.le, ?_⟩, rfl⟩, ?_⟩
  · intro e he
    change (if e < b then x.1.2 e else 0) = x.1.2 e
    simp only [tlvl] at he
    simp [he]
  · rintro y ⟨hy, hylvl⟩
    refine node_ext (by rw [hylvl]; rfl) ?_
    intro e he
    rw [hy.2 e he]
    change x.1.2 e = if e < b then x.1.2 e else 0
    rw [hylvl] at he
    simp [he]

/-! ### Every level is countable -/

theorem countable_level (b : Ordinal.{0}) : {x : TreeNode | tlvl x = b}.Countable := by
  classical
  by_cases hb : b < ω₁
  · obtain ⟨j, hj⟩ := Set.countable_iff_exists_injOn.1 ((lt_omega1_iff_countable b).1 hb)
    set L : Set TreeNode := {x : TreeNode | tlvl x = b} with hL
    set phi : TreeNode → Set (ℕ × ℕ) :=
      fun x => {q | ∃ e < b, x.1.2 e ≠ E b e ∧ q = (j e, x.1.2 e)} with hphi
    have key : ∀ x ∈ L, ∀ y ∈ L, phi x = phi y → ∀ e < b, x.1.2 e ≠ E b e →
        x.1.2 e = y.1.2 e := by
      intro x _ y _ hxy e he hne
      have hmem : (j e, x.1.2 e) ∈ phi x := ⟨e, he, hne, rfl⟩
      rw [hxy] at hmem
      obtain ⟨e', he', -, hEq⟩ := hmem
      have h1 : j e = j e' := congrArg Prod.fst hEq
      have h2 : e = e' := hj he he' h1
      have h3 : x.1.2 e = y.1.2 e' := congrArg Prod.snd hEq
      rw [h3, h2]
    have hinj : Set.InjOn phi L := by
      intro x hx y hy hxy
      refine node_ext (by rw [hx, hy]) ?_
      intro e he
      rw [hx] at he
      by_cases h1 : x.1.2 e = E b e
      · by_cases h2 : y.1.2 e = E b e
        · rw [h1, h2]
        · exact (key y hy x hx hxy.symm e he h2).symm
      · exact key x hx y hy hxy e he h1
    refine Set.countable_of_injective_of_countable_image hinj ?_
    refine (Set.countable_setOf_finite_subset (Set.countable_univ (α := ℕ × ℕ))).mono ?_
    rintro s ⟨x, hx, rfl⟩
    refine ⟨?_, Set.subset_univ _⟩
    have hfin : {e : Ordinal.{0} | e < b ∧ x.1.2 e ≠ E b e}.Finite := by
      have := coh_node x
      rw [hx] at this
      exact this
    refine (hfin.image (fun e => (j e, x.1.2 e))).subset ?_
    rintro q ⟨e, he, hne, rfl⟩
    exact ⟨e, ⟨he, hne⟩, rfl⟩
  · have : {x : TreeNode | tlvl x = b} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hEq
      exact hb (hEq ▸ tlvl_lt_omega1 x)
    rw [this]
    exact Set.countable_empty

/-! ### Every level is nonempty -/

theorem exists_node_of_lt {b : Ordinal.{0}} (hb : b < ω₁) : ∃ x : TreeNode, tlvl x = b := by
  refine ⟨⟨(b, E b), hb, (E_spec b hb).1.1, (E_spec b hb).1.2.1, coh_refl _ _⟩, rfl⟩

/-! ### Every chain is countable -/

theorem countable_chain (C : Set TreeNode)
    (hC : ∀ x ∈ C, ∀ y ∈ C, tle x y ∨ tle y x) : C.Countable := by
  classical
  have hinjlvl : Set.InjOn tlvl C := by
    intro x hx y hy hl
    rcases hC x hx y hy with h | h
    · exact eq_of_tle_of_lvl_eq h hl
    · exact (eq_of_tle_of_lvl_eq h hl.symm).symm
  refine Set.countable_of_injective_of_countable_image hinjlvl ?_
  set L : Set Ordinal.{0} := tlvl '' C with hLdef
  set U : Set Ordinal.{0} := {e | ∃ x ∈ C, e < tlvl x} with hUdef
  -- the common extension of the chain
  set G : Ordinal.{0} → ℕ := fun e =>
    if h : ∃ x, x ∈ C ∧ e < tlvl x then (h.choose).1.2 e else 0 with hGdef
  have hGval : ∀ e, ∀ x ∈ C, e < tlvl x → G e = x.1.2 e := by
    intro e x hx he
    have hex : ∃ x, x ∈ C ∧ e < tlvl x := ⟨x, hx, he⟩
    rw [hGdef]
    simp only [dif_pos hex]
    obtain ⟨hy, hylt⟩ := hex.choose_spec
    rcases hC hex.choose hy x hx with h | h
    · exact h.2 e hylt
    · exact (h.2 e he).symm
  have hUcount : U.Countable := by
    have hinjG : Set.InjOn G U := by
      rintro e₁ ⟨x₁, hx₁, h₁⟩ e₂ ⟨x₂, hx₂, h₂⟩ hEq
      rcases hC x₁ hx₁ x₂ hx₂ with h | h
      · have h₁' : e₁ < tlvl x₂ := lt_of_lt_of_le h₁ h.1
        rw [hGval e₁ x₂ hx₂ h₁', hGval e₂ x₂ hx₂ h₂] at hEq
        exact injBelow_node x₂ e₁ h₁' e₂ h₂ hEq
      · have h₂' : e₂ < tlvl x₁ := lt_of_lt_of_le h₂ h.1
        rw [hGval e₁ x₁ hx₁ h₁, hGval e₂ x₁ hx₁ h₂'] at hEq
        exact injBelow_node x₁ e₁ h₁ e₂ h₂' hEq
    exact Set.countable_of_injective_of_countable_image hinjG (Set.to_countable _)
  have hsub : (L \ U).Subsingleton := by
    intro b hb c hc
    have hble : b ≤ c := by
      obtain ⟨x, hx, rfl⟩ := hb.1
      by_contra hlt
      exact hc.2 ⟨x, hx, lt_of_not_ge hlt⟩
    have hcle : c ≤ b := by
      obtain ⟨x, hx, rfl⟩ := hc.1
      by_contra hlt
      exact hb.2 ⟨x, hx, lt_of_not_ge hlt⟩
    exact le_antisymm hble hcle
  refine (hUcount.union hsub.countable).mono ?_
  intro b hb
  by_cases h : b ∈ U
  · exact Or.inl h
  · exact Or.inr ⟨hb, h⟩

end Aronszajn

/-
Basic definitions for the construction of an Aronszajn tree.

A "node" of the tree we build is a function `f : Ordinal → ℕ` which is injective
below some countable ordinal `a` and vanishes from `a` on.
-/
import Mathlib

open Ordinal Cardinal Set

namespace Aronszajn

/-- `f` vanishes from `a` on. -/
def Norm (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop := ∀ b, a ≤ b → f b = 0

/-- `f` is injective below `a`. -/
def InjBelow (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop :=
  ∀ b < a, ∀ c < a, f b = f c → b = c

/-- `f` misses infinitely many natural numbers below `a`. -/
def CoInf (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop := {n : ℕ | ∀ b < a, f b ≠ n}.Infinite

/-- `f` and `g` differ at only finitely many places below `a`. -/
def Coh (f g : Ordinal.{0} → ℕ) (a : Ordinal.{0}) : Prop := {b | b < a ∧ f b ≠ g b}.Finite

/-- A "good" partial injection with domain `a`. -/
def Nice (a : Ordinal.{0}) (f : Ordinal.{0} → ℕ) : Prop :=
  InjBelow a f ∧ Norm a f ∧ CoInf a f

/-! ### Basic lemmas about `Coh` -/

theorem coh_refl (f : Ordinal.{0} → ℕ) (a : Ordinal.{0}) : Coh f f a := by
  simp [Coh]

theorem Coh.symm {f g : Ordinal.{0} → ℕ} {a : Ordinal.{0}} (h : Coh f g a) : Coh g f a := by
  have : {b | b < a ∧ g b ≠ f b} = {b | b < a ∧ f b ≠ g b} := by
    ext b; exact and_congr_right fun _ => ⟨fun h' h'' => h' h''.symm, fun h' h'' => h' h''.symm⟩
  rw [Coh, this]; exact h

theorem Coh.trans {f g h : Ordinal.{0} → ℕ} {a : Ordinal.{0}}
    (h₁ : Coh f g a) (h₂ : Coh g h a) : Coh f h a := by
  apply Set.Finite.subset (h₁.union h₂)
  rintro b ⟨hb, hne⟩
  by_cases hfg : f b = g b
  · exact Or.inr ⟨hb, by rw [← hfg]; exact hne⟩
  · exact Or.inl ⟨hb, hfg⟩

theorem Coh.mono {f g : Ordinal.{0} → ℕ} {a a' : Ordinal.{0}} (h : Coh f g a) (haa : a' ≤ a) :
    Coh f g a' := by
  apply h.subset
  rintro b ⟨hb, hne⟩
  exact ⟨lt_of_lt_of_le hb haa, hne⟩

/-- If `f` and `g` agree below `a`, they are coherent at `a`. -/
theorem coh_of_eq {f g : Ordinal.{0} → ℕ} {a : Ordinal.{0}} (h : ∀ b < a, f b = g b) :
    Coh f g a := by
  have : {b | b < a ∧ f b ≠ g b} = ∅ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hb => h b hb
  simp [Coh, this]

/-! ### Countable ordinals -/

theorem lt_omega1_iff_countable (a : Ordinal.{0}) : a < ω₁ ↔ (Set.Iio a).Countable := by
  rw [← Cardinal.ord_aleph, Cardinal.lt_ord, ← Cardinal.succ_aleph0, Order.lt_succ_iff,
    ← Cardinal.le_aleph0_iff_set_countable, Ordinal.mk_Iio_ordinal, Cardinal.lift_le_aleph0]

theorem succ_lt_omega1 {a : Ordinal.{0}} (h : a < ω₁) : a + 1 < ω₁ :=
  (Cardinal.isSuccLimit_omega 1).succ_lt h

end Aronszajn

/-
The successor and limit steps of the transfinite construction of a coherent
sequence of partial injections.
-/
import RequestProject.Aronszajn.Extend

open Ordinal Cardinal Set

namespace Aronszajn

/-! ### The zero step -/

theorem nice_zero : Nice 0 (fun _ => 0) := by
  refine ⟨fun b hb => absurd hb (by simp), fun b _ => rfl, ?_⟩
  have : {n : ℕ | ∀ b < (0 : Ordinal.{0}), (0 : ℕ) ≠ n} = Set.univ := by
    ext n; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact fun b hb => absurd hb (by simp)
  rw [CoInf, this]
  exact Set.infinite_univ

/-! ### The successor step -/

theorem exists_succ_step {b : Ordinal.{0}} {h : Ordinal.{0} → ℕ} (hh : Nice b h) :
    ∃ f, Nice (b + 1) f ∧ ∀ e < b, f e = h e := by
  classical
  obtain ⟨hinj, hnorm, hcoinf⟩ := hh
  obtain ⟨r, hr⟩ := hcoinf.nonempty
  refine ⟨fun e => if e < b then h e else if e = b then r else 0, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he f hf hef
    rw [Order.lt_add_one_iff] at he hf
    rcases lt_or_eq_of_le he with he' | rfl
    · rcases lt_or_eq_of_le hf with hf' | rfl
      · simpa [he', hf'] using hinj e he' f hf' (by simpa [he', hf'] using hef)
      · simp only [he', if_true, lt_irrefl, if_false] at hef
        exact absurd hef (hr e he')
    · rcases lt_or_eq_of_le hf with hf' | rfl
      · simp only [hf', if_true, lt_irrefl, if_false] at hef
        exact absurd hef.symm (hr f hf')
      · rfl
  · intro e hbe
    have h1 : ¬ e < b := not_lt.2 (le_trans (le_of_lt (Order.lt_add_one_iff.2 le_rfl)) hbe)
    have h2 : e ≠ b := by
      intro hEq
      exact absurd (hEq ▸ hbe) (not_le.2 (Order.lt_add_one_iff.2 le_rfl))
    simp [h1, h2]
  · have hsub : ({n : ℕ | ∀ e < b, h e ≠ n} \ {r}) ⊆
        {n : ℕ | ∀ e < b + 1, (if e < b then h e else if e = b then r else 0) ≠ n} := by
      rintro n ⟨hn, hnr⟩ e he
      rw [Order.lt_add_one_iff] at he
      rcases lt_or_eq_of_le he with he' | rfl
      · simpa [he'] using hn e he'
      · simp only [lt_irrefl, if_false]
        intro hEq
        exact hnr (by simp [← hEq])
    exact Set.Infinite.mono hsub (hcoinf.diff (Set.finite_singleton r))
  · intro e he; simp [he]

/-! ### Cofinal sequences in countable limit ordinals -/

theorem exists_cofinal_seq {a : Ordinal.{0}} (ha : a < ω₁) (ha0 : 0 < a)
    (halim : ∀ b < a, b + 1 < a) :
    ∃ seq : ℕ → Ordinal.{0}, seq 0 = 0 ∧ (∀ n, seq n < a) ∧ StrictMono seq ∧
      ∀ b < a, ∃ n, b < seq n := by
  have hc : (Set.Iio a).Countable := (lt_omega1_iff_countable a).1 ha
  have hne : (Set.Iio a).Nonempty := ⟨0, ha0⟩
  obtain ⟨s, hs⟩ := hc.exists_surjective hne
  set seq : ℕ → Ordinal.{0} := fun n => Nat.rec (0 : Ordinal.{0})
    (fun n x => max (x + 1) ((s n : Ordinal.{0}) + 1)) n with hseq
  have hlt : ∀ n, seq n < a := by
    intro n
    induction n with
    | zero => exact ha0
    | succ n ih =>
      have h1 : seq n + 1 < a := halim _ ih
      have h2 : (s n : Ordinal.{0}) + 1 < a := halim _ (s n).2
      exact max_lt h1 h2
  have hmono : StrictMono seq := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Order.lt_add_one_iff.2 le_rfl) (le_max_left _ _)
  refine ⟨seq, rfl, hlt, hmono, ?_⟩
  intro b hb
  obtain ⟨n, hn⟩ := hs ⟨b, hb⟩
  refine ⟨n + 1, ?_⟩
  have : (s n : Ordinal.{0}) = b := by rw [hn]
  calc b < (s n : Ordinal.{0}) + 1 := by rw [this]; exact Order.lt_add_one_iff.2 le_rfl
    _ ≤ seq (n + 1) := le_max_right _ _

end Aronszajn

/-
The key "one step extension" lemma for the construction of a coherent sequence
of partial injections.
-/
import RequestProject.Aronszajn.Defs

open Ordinal Cardinal Set

namespace Aronszajn

/-- An infinite set of naturals contains the range of an injection. -/
theorem exists_inj_into {C : Set ℕ} (hC : C.Infinite) :
    ∃ nu : ℕ → ℕ, Function.Injective nu ∧ ∀ n, nu n ∈ C := by
  refine ⟨fun n => ((hC.natEmbedding _ n : C) : ℕ), ?_, fun n => (hC.natEmbedding _ n).2⟩
  intro x y hxy
  exact (hC.natEmbedding _).injective (Subtype.ext hxy)

/-- Preimages (below `c`) of finite sets under maps injective below `c` are finite. -/
theorem finite_preimage_of_injBelow {c : Ordinal.{0}} {k : Ordinal.{0} → ℕ}
    (hk : InjBelow c k) {W : Set ℕ} (hW : W.Finite) : {d | d < c ∧ k d ∈ W}.Finite := by
  apply Set.Finite.of_finite_image (f := k)
  · exact hW.subset (by rintro n ⟨d, ⟨_, hd⟩, rfl⟩; exact hd)
  · rintro d ⟨hd, -⟩ e ⟨he, -⟩ hde
    exact hk d hd e he hde

/-- **Extension lemma.** Given a nice `h` with domain `b`, a nice `k` with domain `c ≥ b`
coherent with `h` below `b`, and a finite set `S` of "reserved" values avoided by `h`,
there is a nice `h'` with domain `c` extending `h`, coherent with `k` below `c`, and
still avoiding `S`. -/
theorem exists_extend {b c : Ordinal.{0}} (hbc : b ≤ c) {h k : Ordinal.{0} → ℕ}
    (hh : Nice b h) (hk : Nice c k) (hcoh : Coh h k b) {S : Set ℕ} (hSfin : S.Finite)
    (hS : ∀ d < b, h d ∉ S) :
    ∃ h' : Ordinal.{0} → ℕ, Nice c h' ∧ (∀ d < b, h' d = h d) ∧ Coh h' k c ∧
      (∀ d < c, h' d ∉ S) := by
  classical
  obtain ⟨hinj, hnorm, hcoinf⟩ := hh
  obtain ⟨kinj, knorm, kcoinf⟩ := hk
  set F : Set Ordinal.{0} := {d | d < b ∧ h d ≠ k d} with hFdef
  have hFfin : F.Finite := hcoh
  set V : Set ℕ := (h '' F) ∪ S with hVdef
  have hVfin : V.Finite := (hFfin.image h).union hSfin
  set C : Set ℕ := {n | ∀ d < c, k d ≠ n} \ V with hCdef
  have hCinf : C.Infinite := kcoinf.diff hVfin
  obtain ⟨nu, hnuinj, hnuC⟩ := exists_inj_into hCinf
  set P : Set ℕ := (h '' Set.Iio b) ∪ S with hPdef
  -- the new function
  set h' : Ordinal.{0} → ℕ :=
    fun d => if d < b then h d else if d < c then (if k d ∈ P then nu (k d) else k d) else 0
    with hh'def
  -- `C` is disjoint from `P`
  have hCP : ∀ n ∈ C, n ∉ P := by
    rintro n ⟨hnk, hnV⟩ hnP
    rcases hnP with ⟨e, he, rfl⟩ | hnS
    · by_cases hef : h e = k e
      · exact hnk e (lt_of_lt_of_le he hbc) hef.symm
      · exact hnV (Or.inl ⟨e, ⟨he, hef⟩, rfl⟩)
    · exact hnV (Or.inr hnS)
  have hCkval : ∀ n ∈ C, ∀ d < c, k d ≠ n := fun n hn => hn.1
  -- values of `h'`
  have hlow : ∀ d < b, h' d = h d := by
    intro d hd; simp [hh'def, hd]
  have hlowP : ∀ d < b, h' d ∈ P := by
    intro d hd; rw [hlow d hd]; exact Or.inl ⟨d, hd, rfl⟩
  have hhigh : ∀ d, b ≤ d → d < c → (h' d = nu (k d) ∧ k d ∈ P) ∨ (h' d = k d ∧ k d ∉ P) := by
    intro d hbd hdc
    by_cases hkP : k d ∈ P
    · exact Or.inl ⟨by simp [hh'def, not_lt.2 hbd, hdc, hkP], hkP⟩
    · exact Or.inr ⟨by simp [hh'def, not_lt.2 hbd, hdc, hkP], hkP⟩
  have hhighnotP : ∀ d, b ≤ d → d < c → h' d ∉ P := by
    intro d hbd hdc
    rcases hhigh d hbd hdc with ⟨he, -⟩ | ⟨he, hkP⟩
    · rw [he]; exact hCP _ (hnuC _)
    · rw [he]; exact hkP
  -- `D`, the finite set of repaired positions
  set D : Set Ordinal.{0} := {d | d < c ∧ k d ∈ (h '' F) ∪ S} with hDdef
  have hDfin : D.Finite := finite_preimage_of_injBelow kinj hVfin
  have hDsub : ∀ d, b ≤ d → d < c → k d ∈ P → d ∈ D := by
    intro d hbd hdc hkP
    refine ⟨hdc, ?_⟩
    rcases hkP with ⟨e, he, hek⟩ | hnS
    · by_cases hef : h e = k e
      · exact absurd (kinj e (lt_of_lt_of_le he hbc) d hdc (by rw [hef] at hek; exact hek))
          (by intro hh2; exact absurd (hh2 ▸ he) (not_lt.2 hbd))
      · exact Or.inl ⟨e, ⟨he, hef⟩, hek⟩
    · exact Or.inr hnS
  refine ⟨h', ⟨?_, ?_, ?_⟩, hlow, ?_, ?_⟩
  · -- injectivity
    intro d hd e he hde
    rcases lt_or_ge d b with hdb | hdb
    · rcases lt_or_ge e b with heb | heb
      · exact hinj d hdb e heb (by rw [← hlow d hdb, ← hlow e heb]; exact hde)
      · exact absurd (hde ▸ hlowP d hdb) (hhighnotP e heb he)
    · rcases lt_or_ge e b with heb | heb
      · exact absurd (hde ▸ hlowP e heb) (by rw [← hde] at *; exact hhighnotP d hdb hd)
      · rcases hhigh d hdb hd with ⟨hd1, hd2⟩ | ⟨hd1, hd2⟩ <;>
          rcases hhigh e heb he with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · exact kinj d hd e he (hnuinj (by rw [← hd1, ← he1]; exact hde))
        · exact absurd (by rw [← he1, ← hde, hd1] : k e = nu (k d))
            (hCkval _ (hnuC (k d)) e he)
        · exact absurd (by rw [← hd1, hde, he1] : k d = nu (k e))
            (hCkval _ (hnuC (k e)) d hd)
        · exact kinj d hd e he (by rw [← hd1, ← he1]; exact hde)
  · -- normalization
    intro d hcd
    have : ¬ d < b := not_lt.2 (le_trans hbc hcd)
    simp [hh'def, this, not_lt.2 hcd]
  · -- coinfinite
    have hsub : ({n | ∀ d < c, k d ≠ n} \ (V ∪ nu '' (k '' D))) ⊆ {n | ∀ d < c, h' d ≠ n} := by
      rintro n ⟨hnk, hnV⟩ d hd hdn
      rcases lt_or_ge d b with hdb | hdb
      · rw [hlow d hdb] at hdn
        by_cases hef : h d = k d
        · exact hnk d hd (by rw [← hef]; exact hdn)
        · exact hnV (Or.inl (Or.inl ⟨d, ⟨hdb, hef⟩, hdn⟩))
      · rcases hhigh d hdb hd with ⟨hd1, hd2⟩ | ⟨hd1, -⟩
        · exact hnV (Or.inr ⟨k d, ⟨d, hDsub d hdb hd hd2, rfl⟩, by rw [← hd1]; exact hdn⟩)
        · exact hnk d hd (by rw [← hd1]; exact hdn)
    exact Set.Infinite.mono hsub
      (kcoinf.diff (hVfin.union ((hDfin.image k).image nu)))
  · -- coherence with `k`
    apply Set.Finite.subset (hFfin.union hDfin)
    rintro d ⟨hd, hne⟩
    rcases lt_or_ge d b with hdb | hdb
    · refine Or.inl ⟨hdb, ?_⟩
      rw [hlow d hdb] at hne; exact hne
    · rcases hhigh d hdb hd with ⟨-, hd2⟩ | ⟨hd1, -⟩
      · exact Or.inr (hDsub d hdb hd hd2)
      · exact absurd hd1 hne
  · -- still avoids `S`
    intro d hd
    rcases lt_or_ge d b with hdb | hdb
    · rw [hlow d hdb]; exact hS d hdb
    · exact fun hmem => hhighnotP d hdb hd (Or.inr hmem)

end Aronszajn

/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Aronszajn.Tree

open Ordinal Cardinal Set

namespace Frontier

/-- **An Aronszajn tree exists.**

There is a partial order `(T, le)` together with a level function `lvl : T → Ordinal`
such that:

* the predecessors of any node are linearly ordered by `le`, and `lvl` restricts to an
  order isomorphism from them onto the ordinals `< lvl x` (so `T` is a tree and `lvl x`
  is the order type of the set of predecessors of `x`);
* every node has level `< ω₁` and every ordinal `< ω₁` occurs as a level, i.e. the tree
  has height `ω₁`;
* every level of the tree is countable;
* every chain of `T` — in particular every branch — is countable.

The tree is constructed as the tree of finite modifications of a coherent sequence
`Aronszajn.E` of injections `a → ℕ` (`a < ω₁`), ordered by end-extension. -/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (le : T → T → Prop) (lvl : T → Ordinal.{0}),
      -- `le` is a partial order
      (∀ x, le x x) ∧
      (∀ x y z, le x y → le y z → le x z) ∧
      (∀ x y, le x y → le y x → x = y) ∧
      -- the predecessors of a node are linearly ordered
      (∀ x y z, le y x → le z x → le y z ∨ le z y) ∧
      -- `lvl` is an order isomorphism from the predecessors of `x` onto `Iio (lvl x)`
      (∀ x y, le y x → y ≠ x → lvl y < lvl x) ∧
      (∀ (x : T) (b : Ordinal.{0}), b < lvl x → ∃! y, le y x ∧ lvl y = b) ∧
      -- the tree has height `ω₁`
      (∀ x, lvl x < ω₁) ∧
      (∀ b < ω₁, ∃ x, lvl x = b) ∧
      -- all levels are countable
      (∀ b : Ordinal.{0}, {x | lvl x = b}.Countable) ∧
      -- all chains are countable
      (∀ C : Set T, (∀ x ∈ C, ∀ y ∈ C, le x y ∨ le y x) → C.Countable) := by
  refine ⟨Aronszajn.TreeNode, Aronszajn.tle, Aronszajn.tlvl, Aronszajn.tle_refl,
    fun _ _ _ => Aronszajn.tle_trans, fun _ _ => Aronszajn.tle_antisymm,
    fun _ _ _ => Aronszajn.tle_total_of_le, ?_, fun x b hb => Aronszajn.exists_unique_pred x hb,
    Aronszajn.tlvl_lt_omega1, fun b hb => Aronszajn.exists_node_of_lt hb,
    Aronszajn.countable_level, Aronszajn.countable_chain⟩
  intro x y hyx hne
  rcases lt_or_eq_of_le hyx.1 with h | h
  · exact h
  · exact absurd (Aronszajn.eq_of_tle_of_lvl_eq hyx h) hne

end Frontier

