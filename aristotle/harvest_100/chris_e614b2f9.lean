/-
# Aronszajn Tree Exists
Category: Frontier — Set Theory
Target: Frontier.Aronszajn_tree_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Ordinal Set Cardinal
open scoped Classical

namespace Frontier

/-- The first uncountable ordinal `ω₁`. -/
noncomputable def omega1 : Ordinal.{0} := (Cardinal.aleph 1).ord

/-! ### Basic facts about `ω₁` -/

theorem countable_Iio_of_lt {a : Ordinal} (h : a < omega1) : (Set.Iio a).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal, Cardinal.lift_lt_aleph_one]
  exact Cardinal.lt_ord.mp h

theorem lt_omega1_of_countable {a : Ordinal} (h : (Set.Iio a).Countable) : a < omega1 := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal,
    Cardinal.lift_lt_aleph_one] at h
  exact Cardinal.lt_ord.mpr h

theorem not_countable_Iio_omega1 : ¬ (Set.Iio omega1).Countable :=
  fun h => lt_irrefl _ (lt_omega1_of_countable h)

theorem iSup_lt_omega1 {f : ℕ → Ordinal} (h : ∀ n, f n < omega1) : iSup f < omega1 :=
  Ordinal.iSup_sequence_lt_omega_one f h

theorem omega1_pos : 0 < omega1 := by
  apply lt_omega1_of_countable
  simp

theorem succ_lt_omega1 {a : Ordinal} (h : a < omega1) : a + 1 < omega1 := by
  apply lt_omega1_of_countable
  have : Set.Iio (a + 1) ⊆ Set.Iio a ∪ {a} := by
    intro x hx
    have hx' : x ≤ a := by simpa [Ordinal.add_one_eq_succ, Order.lt_succ_iff] using hx
    rcases lt_or_eq_of_le hx' with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  exact Set.Countable.mono this ((countable_Iio_of_lt h).union (Set.countable_singleton a))

theorem ord_lt_add_one (b : Ordinal) : b < b + 1 := by
  rw [Ordinal.add_one_eq_succ]; exact Order.lt_succ b

/-! ### Cofinal `ω`-sequences in countable limit ordinals -/

/-- A sequence hitting every ordinal below `a`, provided `Set.Iio a` is countable. -/
noncomputable def enumIio (a : Ordinal) (n : ℕ) : Ordinal :=
  if h : ∃ g : ℕ → Ordinal, ∀ x < a, ∃ m, g m = x then
    (if h.choose n < a then h.choose n else 0)
  else 0

theorem enumIio_lt {a : Ordinal} (ha : 0 < a) (n : ℕ) : enumIio a n < a := by
  unfold enumIio
  split
  · split
    · assumption
    · exact ha
  · exact ha

theorem enumIio_surj {a : Ordinal} (hc : (Set.Iio a).Countable) {x : Ordinal} (hx : x < a) :
    ∃ n, enumIio a n = x := by
  obtain ⟨g, hg⟩ := hc.exists_eq_range ⟨x, hx⟩
  have hex : ∃ g : ℕ → Ordinal, ∀ y < a, ∃ m, g m = y := by
    refine ⟨g, fun y hy => ?_⟩
    have : y ∈ Set.range g := by rw [← hg]; exact hy
    exact this
  obtain ⟨m, hm⟩ := hex.choose_spec x hx
  refine ⟨m, ?_⟩
  unfold enumIio
  rw [dif_pos hex, if_pos (by rw [hm]; exact hx)]
  exact hm

/-- A strictly increasing sequence, cofinal in `a` when `a` is a countable limit ordinal. -/
noncomputable def cseq (a : Ordinal) : ℕ → Ordinal
  | 0 => 0
  | (n + 1) => max (cseq a n) (enumIio a n) + 1

theorem cseq_zero (a : Ordinal) : cseq a 0 = 0 := rfl

theorem cseq_succ (a : Ordinal) (n : ℕ) :
    cseq a (n + 1) = max (cseq a n) (enumIio a n) + 1 := rfl

theorem cseq_lt_succ (a : Ordinal) (n : ℕ) : cseq a n < cseq a (n + 1) := by
  rw [cseq_succ]
  exact lt_of_le_of_lt (le_max_left _ _) (ord_lt_add_one _)

theorem cseq_mono (a : Ordinal) : StrictMono (cseq a) := strictMono_nat_of_lt_succ (cseq_lt_succ a)

theorem cseq_lt_of_limit {a : Ordinal} (h0 : 0 < a) (hl : ∀ b < a, b + 1 < a) (n : ℕ) :
    cseq a n < a := by
  induction n with
  | zero => simpa [cseq_zero] using h0
  | succ n ih => rw [cseq_succ]; exact hl _ (max_lt ih (enumIio_lt h0 n))

theorem cseq_cofinal {a : Ordinal} (hc : (Set.Iio a).Countable) {x : Ordinal} (hx : x < a) :
    ∃ n, x < cseq a n := by
  obtain ⟨n, hn⟩ := enumIio_surj hc hx
  refine ⟨n + 1, ?_⟩
  rw [cseq_succ, ← hn]
  exact lt_of_le_of_lt (le_max_right _ _) (ord_lt_add_one _)

theorem limit_props {a : Ordinal} (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1) :
    0 < a ∧ ∀ b < a, b + 1 < a := by
  refine ⟨lt_of_le_of_ne (bot_le : (0 : Ordinal) ≤ a) (Ne.symm h0), fun b hb => ?_⟩
  have h1 : b + 1 ≤ a := by simpa [Ordinal.add_one_eq_succ] using Order.succ_le_of_lt hb
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd ⟨b, h.symm⟩ hs

/-! ### The coherent family `E` -/

/-- One step of the transfinite recursion producing the coherent family `E`. -/
noncomputable def Estep (a : Ordinal) (ih : ∀ b, b < a → Ordinal → ℕ) : Ordinal → ℕ :=
  if h0 : a = 0 then fun _ => 0
  else if hs : ∃ b, a = b + 1 then
    fun x => if x < hs.choose then
        ih hs.choose
          (lt_of_lt_of_eq (ord_lt_add_one hs.choose) hs.choose_spec.symm) x else 0
  else
    fun x =>
      if hx : ∃ n, x < cseq a n then
        (Nat.rec (motive := fun _ => Ordinal → ℕ) (fun _ => 0)
          (fun m fm y => if y < cseq a m then fm y
            else max (ih (cseq a (m + 1))
              (cseq_lt_of_limit (limit_props h0 hs).1 (limit_props h0 hs).2 (m + 1)) y) m)
          (Nat.find hx)) x
      else 0

/-- The coherent, finite-to-one family `E a : Iio a → ℕ` for `a < ω₁`. -/
noncomputable def E : Ordinal → Ordinal → ℕ := WellFounded.fix Ordinal.lt_wf Estep

theorem E_eq (a : Ordinal) : E a = Estep a (fun b _ => E b) := WellFounded.fix_eq _ _ _

theorem E_zero (x : Ordinal) : E 0 x = 0 := by
  rw [E_eq]; unfold Estep; rw [dif_pos rfl]

theorem add_one_ne_zero' (b : Ordinal) : b + 1 ≠ 0 :=
  ne_of_gt (lt_of_le_of_lt (bot_le : (0 : Ordinal) ≤ b) (ord_lt_add_one b))

theorem ord_add_one_inj {b c : Ordinal} (h : b + 1 = c + 1) : b = c := by
  rw [Ordinal.add_one_eq_succ, Ordinal.add_one_eq_succ] at h
  exact Order.succ_injective h

theorem E_succ (b x : Ordinal) : E (b + 1) x = if x < b then E b x else 0 := by
  have hs : ∃ c, b + 1 = c + 1 := ⟨b, rfl⟩
  have hc : hs.choose = b := (ord_add_one_inj hs.choose_spec).symm
  rw [E_eq]; unfold Estep
  rw [dif_neg (add_one_ne_zero' b), dif_pos hs]
  simp only [hc]

/-- The `ω`-approximation sequence used at limit stages of the recursion. -/
noncomputable def Eaux (a : Ordinal) : ℕ → Ordinal → ℕ
  | 0 => fun _ => 0
  | (n + 1) => fun x => if x < cseq a n then Eaux a n x else max (E (cseq a (n + 1)) x) n

theorem Eaux_succ (a : Ordinal) (n : ℕ) (x : Ordinal) :
    Eaux a (n + 1) x = if x < cseq a n then Eaux a n x else max (E (cseq a (n + 1)) x) n := rfl

theorem E_limit {a : Ordinal} (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1) (x : Ordinal) :
    E a x = if hx : ∃ n, x < cseq a n then Eaux a (Nat.find hx) x else 0 := by
  have key : ∀ (n : ℕ) (y : Ordinal),
      (Nat.rec (motive := fun _ => Ordinal → ℕ) (fun _ => 0)
        (fun m fm z => if z < cseq a m then fm z
          else max (E (cseq a (m + 1)) z) m) n : Ordinal → ℕ) y = Eaux a n y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [Eaux_succ]; simp only []; split <;> simp [ih]
  rw [E_eq]; unfold Estep
  rw [dif_neg h0, dif_neg hs]
  split
  · exact key _ _
  · rfl

/-! ### The two invariants -/

/-- `f` is finite-to-one below `a`. -/
def FinOne (f : Ordinal → ℕ) (a : Ordinal) : Prop := ∀ v : ℕ, {x | x < a ∧ f x = v}.Finite

/-- `f` and `g` agree below `a` outside a finite set. -/
def Coh (f g : Ordinal → ℕ) (a : Ordinal) : Prop := {x | x < a ∧ f x ≠ g x}.Finite

theorem FinOne.mono {f : Ordinal → ℕ} {a b : Ordinal} (h : FinOne f a) (hb : b ≤ a) :
    FinOne f b := fun v => (h v).subset (fun _ hx => ⟨lt_of_lt_of_le hx.1 hb, hx.2⟩)

theorem Coh.mono {f g : Ordinal → ℕ} {a b : Ordinal} (h : Coh f g a) (hb : b ≤ a) :
    Coh f g b := h.subset (fun _ hx => ⟨lt_of_lt_of_le hx.1 hb, hx.2⟩)

theorem Coh.symm {f g : Ordinal → ℕ} {a : Ordinal} (h : Coh f g a) : Coh g f a :=
  h.subset (fun _ hx => ⟨hx.1, Ne.symm hx.2⟩)

theorem FinOne.le_finite {f : Ordinal → ℕ} {a : Ordinal} (h : FinOne f a) (n : ℕ) :
    {x | x < a ∧ f x ≤ n}.Finite := by
  have hset : {x : Ordinal | x < a ∧ f x ≤ n} = ⋃ v ∈ Set.Iic n, {x | x < a ∧ f x = v} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Iic, exists_prop]
    constructor
    · rintro ⟨hx, hv⟩; exact ⟨f x, hv, hx, rfl⟩
    · rintro ⟨v, hv, hx, rfl⟩; exact ⟨hx, hv⟩
  rw [hset]
  exact Set.Finite.biUnion (Set.finite_Iic n) (fun v _ => h v)

theorem finOne_zero (f : Ordinal → ℕ) : FinOne f 0 := by
  intro v
  have : {x : Ordinal | x < 0 ∧ f x = v} = ∅ := by
    ext x; simp
  rw [this]; exact Set.finite_empty

theorem coh_zero (f g : Ordinal → ℕ) : Coh f g 0 :=
  Set.Finite.subset Set.finite_empty (fun x hx => absurd hx.1 (by simp))

/-! ### The limit stage -/

section LimitStage

variable {a : Ordinal} (ha : a < omega1) (h0 : a ≠ 0) (hs : ¬ ∃ b, a = b + 1)
  (IH : ∀ b < a, FinOne (E b) b ∧ ∀ c < b, Coh (E b) (E c) c)

include h0 hs in
theorem cseq_lt_self (n : ℕ) : cseq a n < a :=
  cseq_lt_of_limit (limit_props h0 hs).1 (limit_props h0 hs).2 n

theorem Eaux_stable {m n : ℕ} (hmn : m ≤ n) {x : Ordinal} (hx : x < cseq a m) :
    Eaux a n x = Eaux a m x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [Eaux_succ, if_pos (lt_of_lt_of_le hx ((cseq_mono a).monotone hmn)), ih]

include h0 hs in
theorem E_eq_Eaux {n : ℕ} {x : Ordinal} (hx : x < cseq a n) : E a x = Eaux a n x := by
  have hex : ∃ k, x < cseq a k := ⟨n, hx⟩
  rw [E_limit h0 hs x, dif_pos hex]
  exact (Eaux_stable (Nat.find_le hx) (Nat.find_spec hex)).symm

include h0 hs IH in
theorem Eaux_finOne (n : ℕ) : FinOne (Eaux a n) (cseq a n) := by
  induction n with
  | zero => rw [cseq_zero]; exact finOne_zero _
  | succ n ih =>
    intro v
    have hlt : cseq a (n + 1) < a := cseq_lt_self h0 hs (n + 1)
    obtain ⟨hfo, -⟩ := IH _ hlt
    refine Set.Finite.subset (((ih v).union (hfo v)).union (hfo.le_finite n)) ?_
    rintro x ⟨hx, hv⟩
    rw [Eaux_succ] at hv
    by_cases hxn : x < cseq a n
    · rw [if_pos hxn] at hv
      exact Or.inl (Or.inl ⟨hxn, hv⟩)
    · rw [if_neg hxn] at hv
      rcases Nat.lt_or_ge (E (cseq a (n + 1)) x) n with hlt' | hge
      · exact Or.inr ⟨hx, le_of_lt hlt'⟩
      · exact Or.inl (Or.inr ⟨hx, by rwa [max_eq_left hge] at hv⟩)

include h0 hs IH in
theorem Eaux_coh (n : ℕ) : Coh (Eaux a n) (E (cseq a n)) (cseq a n) := by
  induction n with
  | zero => rw [cseq_zero]; exact coh_zero _ _
  | succ n ih =>
    have hlt : cseq a (n + 1) < a := cseq_lt_self h0 hs (n + 1)
    obtain ⟨hfo, hcoh⟩ := IH _ hlt
    have h2 : Coh (E (cseq a (n + 1))) (E (cseq a n)) (cseq a n) :=
      hcoh _ (cseq_mono a (Nat.lt_succ_self n))
    refine Set.Finite.subset ((ih.union h2.symm).union (hfo.le_finite n)) ?_
    rintro x ⟨hx, hv⟩
    rw [Eaux_succ] at hv
    by_cases hxn : x < cseq a n
    · rw [if_pos hxn] at hv
      by_cases hEq : Eaux a n x = E (cseq a n) x
      · exact Or.inl (Or.inr ⟨hxn, by rw [← hEq]; exact hv⟩)
      · exact Or.inl (Or.inl ⟨hxn, hEq⟩)
    · rw [if_neg hxn] at hv
      refine Or.inr ⟨hx, ?_⟩
      by_contra hcon
      exact hv (max_eq_left (le_of_lt (not_le.mp hcon)))

include ha h0 hs IH in
theorem E_limit_finOne : FinOne (E a) a := by
  have hc : (Set.Iio a).Countable := countable_Iio_of_lt ha
  intro v
  refine Set.Finite.subset (Eaux_finOne h0 hs IH (v + 1) v) ?_
  rintro x ⟨hx, hv⟩
  obtain ⟨n, hn⟩ := cseq_cofinal hc hx
  have hex : ∃ k, x < cseq a k := ⟨n, hn⟩
  have hNspec : x < cseq a (Nat.find hex) := Nat.find_spec hex
  have hNpos : Nat.find hex ≠ 0 := by
    intro h
    rw [h, cseq_zero] at hNspec
    exact absurd hNspec (by simp)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 :=
    ⟨Nat.find hex - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hNpos)).symm⟩
  have hmin : ¬ (x < cseq a k) := Nat.find_min hex (by omega)
  have hNspec' : x < cseq a (k + 1) := hk ▸ hNspec
  have hval : E a x = max (E (cseq a (k + 1)) x) k := by
    rw [E_eq_Eaux h0 hs hNspec', Eaux_succ, if_neg hmin]
  have hkv : k ≤ v := by rw [← hv, hval]; exact le_max_right _ _
  have hxlt : x < cseq a (v + 1) :=
    lt_of_lt_of_le hNspec' ((cseq_mono a).monotone (Nat.succ_le_succ hkv))
  exact ⟨hxlt, by rw [← E_eq_Eaux h0 hs hxlt]; exact hv⟩

include ha h0 hs IH in
theorem E_limit_coh (b : Ordinal) (hb : b < a) : Coh (E a) (E b) b := by
  have hc : (Set.Iio a).Countable := countable_Iio_of_lt ha
  obtain ⟨n, hn⟩ := cseq_cofinal hc hb
  obtain ⟨-, hcoh⟩ := IH _ (cseq_lt_self h0 hs n)
  refine Set.Finite.subset (((Eaux_coh h0 hs IH n).union (hcoh b hn))) ?_
  rintro x ⟨hx, hv⟩
  have hxn : x < cseq a n := lt_trans hx hn
  rw [E_eq_Eaux h0 hs hxn] at hv
  by_cases hEq : Eaux a n x = E (cseq a n) x
  · exact Or.inr ⟨hx, by rw [← hEq]; exact hv⟩
  · exact Or.inl ⟨hxn, hEq⟩

end LimitStage

/-! ### The specification of `E` -/

theorem E_spec : ∀ a : Ordinal, a < omega1 → FinOne (E a) a ∧ ∀ b < a, Coh (E a) (E b) b := by
  intro a
  induction a using Ordinal.induction with
  | h a IH =>
    intro ha
    rcases eq_or_ne a 0 with rfl | h0
    · refine ⟨?_, ?_⟩
      · exact finOne_zero _
      · intro b hb; exact absurd hb (by simp)
    by_cases hsucc : ∃ b, a = b + 1
    · obtain ⟨b, rfl⟩ := hsucc
      have hb : b < b + 1 := ord_lt_add_one b
      obtain ⟨hfo, hcoh⟩ := IH b hb (lt_trans hb ha)
      constructor
      · intro v
        refine Set.Finite.subset ((hfo v).union (Set.finite_singleton b)) ?_
        rintro x ⟨hx, hv⟩
        rcases lt_or_eq_of_le (show x ≤ b by
          simpa [Ordinal.add_one_eq_succ, Order.lt_succ_iff] using hx) with h | h
        · refine Or.inl ⟨h, ?_⟩
          rwa [E_succ, if_pos h] at hv
        · exact Or.inr h
      · intro c hc
        have hcb : c ≤ b := by
          simpa [Ordinal.add_one_eq_succ, Order.lt_succ_iff] using hc
        rcases lt_or_eq_of_le hcb with hcb' | rfl
        · refine Set.Finite.subset (hcoh c hcb') ?_
          rintro x ⟨hx, hv⟩
          refine ⟨hx, ?_⟩
          rwa [E_succ, if_pos (lt_trans hx hcb')] at hv
        · refine Set.Finite.subset Set.finite_empty ?_
          rintro x ⟨hx, hv⟩
          exact absurd (by rw [E_succ, if_pos hx] : E (c + 1) x = E c x) hv
    · have IH' : ∀ b < a, FinOne (E b) b ∧ ∀ c < b, Coh (E b) (E c) c :=
        fun b hb => IH b hb (lt_trans hb ha)
      exact ⟨E_limit_finOne ha h0 hsucc IH', fun b hb => E_limit_coh ha h0 hsucc IH' b hb⟩

/-! ### The tree of finite modifications of the coherent family -/

/-- A node of the tree: a countable ordinal `lvl` together with a function on `Iio lvl`
(extended by `0`) which differs from `E lvl` at only finitely many places. -/
structure Node where
  /-- the level of the node -/
  lvl : Ordinal
  /-- the function attached to the node -/
  f : Ordinal → ℕ
  lvl_lt : lvl < omega1
  diff_fin : Coh f (E lvl) lvl
  zero_out : ∀ x, lvl ≤ x → f x = 0

theorem Node.ext' : ∀ {p q : Node}, p.lvl = q.lvl → (∀ x, p.f x = q.f x) → p = q
  | ⟨l, f, _, _, _⟩, ⟨l', f', _, _, _⟩, h1, h2 => by
      simp only at h1
      subst h1
      simp only [Node.mk.injEq, true_and]
      exact funext h2

instance : PartialOrder Node where
  le p q := p.lvl ≤ q.lvl ∧ ∀ x < p.lvl, p.f x = q.f x
  le_refl p := ⟨le_rfl, fun _ _ => rfl⟩
  le_trans p q r h1 h2 :=
    ⟨h1.1.trans h2.1, fun x hx => (h1.2 x hx).trans (h2.2 x (lt_of_lt_of_le hx h1.1))⟩
  le_antisymm p q h1 h2 := by
    have hl : p.lvl = q.lvl := le_antisymm h1.1 h2.1
    refine Node.ext' hl (fun x => ?_)
    by_cases hx : x < p.lvl
    · exact h1.2 x hx
    · rw [p.zero_out x (not_lt.mp hx), q.zero_out x (by rw [← hl]; exact not_lt.mp hx)]

theorem Node.le_def {p q : Node} : p ≤ q ↔ p.lvl ≤ q.lvl ∧ ∀ x < p.lvl, p.f x = q.f x := Iff.rfl

theorem Node.eq_of_le_of_lvl_eq {p q : Node} (h : p ≤ q) (hl : p.lvl = q.lvl) : p = q := by
  refine Node.ext' hl (fun x => ?_)
  by_cases hx : x < p.lvl
  · exact h.2 x hx
  · rw [p.zero_out x (not_lt.mp hx), q.zero_out x (by rw [← hl]; exact not_lt.mp hx)]

theorem Node.lvl_lt_of_lt {p q : Node} (h : p < q) : p.lvl < q.lvl := by
  rcases lt_iff_le_and_ne.mp h with ⟨hle, hne⟩
  rcases lt_or_eq_of_le hle.1 with h' | h'
  · exact h'
  · exact absurd (Node.eq_of_le_of_lvl_eq hle h') hne

theorem Node.le_of_le_of_le {p q r : Node} (hp : p ≤ r) (hq : q ≤ r) (h : p.lvl ≤ q.lvl) :
    p ≤ q :=
  ⟨h, fun x hx => (hp.2 x hx).trans (hq.2 x (lt_of_lt_of_le hx h)).symm⟩

theorem Node.finOne (p : Node) : FinOne p.f p.lvl := by
  intro v
  obtain ⟨hfo, -⟩ := E_spec p.lvl p.lvl_lt
  refine Set.Finite.subset ((hfo v).union p.diff_fin) ?_
  rintro x ⟨hx, hv⟩
  by_cases he : p.f x = E p.lvl x
  · exact Or.inl ⟨hx, by rw [← he]; exact hv⟩
  · exact Or.inr ⟨hx, he⟩

/-- The restriction of a node to a smaller level: the predecessor at that level. -/
noncomputable def Node.restr (p : Node) (b : Ordinal) (hb : b < p.lvl) : Node where
  lvl := b
  f := fun x => if x < b then p.f x else 0
  lvl_lt := lt_trans hb p.lvl_lt
  diff_fin := by
    obtain ⟨-, hcoh⟩ := E_spec p.lvl p.lvl_lt
    refine Set.Finite.subset ((p.diff_fin.union (hcoh b hb))) ?_
    rintro x ⟨hx, hv⟩
    simp only [if_pos hx] at hv
    by_cases he : p.f x = E p.lvl x
    · exact Or.inr ⟨hx, by rw [← he]; exact hv⟩
    · exact Or.inl ⟨lt_trans hx hb, he⟩
  zero_out := fun x hx => if_neg (not_lt.mpr hx)

theorem Node.restr_lt (p : Node) (b : Ordinal) (hb : b < p.lvl) : p.restr b hb < p := by
  refine lt_of_le_of_ne ⟨le_of_lt hb, fun x hx => if_pos hx⟩ (fun hcon => ?_)
  exact absurd (congrArg Node.lvl hcon) (ne_of_lt hb)

/-- The canonical node at level `b`, given by `E b` itself. -/
noncomputable def Node.base (b : Ordinal) (hb : b < omega1) : Node where
  lvl := b
  f := fun x => if x < b then E b x else 0
  lvl_lt := hb
  diff_fin := by
    refine Set.Finite.subset Set.finite_empty ?_
    rintro x ⟨hx, hv⟩
    simp only [if_pos hx] at hv
    exact absurd rfl hv
  zero_out := fun x hx => if_neg (not_lt.mpr hx)

@[simp] theorem Node.base_lvl (b : Ordinal) (hb : b < omega1) : (Node.base b hb).lvl = b := rfl

/-! ### Countability of levels -/

theorem Node.levels_countable (b : Ordinal) : {p : Node | p.lvl = b}.Countable := by
  by_cases hb : b < omega1
  · have hS : ((Set.Iio b) ×ˢ (Set.univ : Set ℕ)).Countable :=
      (countable_Iio_of_lt hb).prod Set.countable_univ
    refine Set.countable_of_injective_of_countable_image
      (f := fun p : Node => (fun x => (x, p.f x)) '' {x | x < b ∧ p.f x ≠ E b x}) ?_ ?_
    · rintro p hp q hq hpq
      have hpq' : (fun x => (x, p.f x)) '' {x | x < b ∧ p.f x ≠ E b x} =
          (fun x => (x, q.f x)) '' {x | x < b ∧ q.f x ≠ E b x} := hpq
      have hlp : p.lvl = b := hp
      have hlq : q.lvl = b := hq
      refine Node.ext' (hlp.trans hlq.symm) (fun x => ?_)
      by_cases hx : x < b
      · by_cases hpe : p.f x = E b x
        · by_cases hqe : q.f x = E b x
          · rw [hpe, hqe]
          · exfalso
            have hmem : (x, q.f x) ∈
                (fun x => (x, q.f x)) '' {x | x < b ∧ q.f x ≠ E b x} := ⟨x, ⟨hx, hqe⟩, rfl⟩
            rw [← hpq'] at hmem
            obtain ⟨y, ⟨hy, hyne⟩, hyeq⟩ := hmem
            have : y = x := congrArg Prod.fst hyeq
            subst this
            exact hyne hpe
        · have hmem : (x, p.f x) ∈
              (fun x => (x, p.f x)) '' {x | x < b ∧ p.f x ≠ E b x} := ⟨x, ⟨hx, hpe⟩, rfl⟩
          rw [hpq'] at hmem
          obtain ⟨y, ⟨hy, hyne⟩, hyeq⟩ := hmem
          have hyx : y = x := congrArg Prod.fst hyeq
          subst hyx
          exact (congrArg Prod.snd hyeq).symm
      · rw [p.zero_out x (by rw [hlp]; exact not_lt.mp hx),
          q.zero_out x (by rw [hlq]; exact not_lt.mp hx)]
    · refine Set.Countable.mono ?_ (Set.countable_setOf_finite_subset hS)
      rintro t ⟨p, hp, rfl⟩
      have hlp : p.lvl = b := hp
      constructor
      · refine Set.Finite.image _ ?_
        have := p.diff_fin
        rw [hlp] at this
        exact this
      · rintro z ⟨y, ⟨hy, -⟩, rfl⟩
        exact ⟨hy, Set.mem_univ _⟩
  · have hempty : {p : Node | p.lvl = b} = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hb (h ▸ p.lvl_lt)
    rw [hempty]
    exact Set.countable_empty

/-! ### No uncountable chain -/

theorem Node.chains_countable (C : Set Node) (hC : IsChain (· ≤ ·) C) : C.Countable := by
  by_contra hunc
  have hunb : ∀ b < omega1, ∃ p ∈ C, b < p.lvl := by
    intro b hb
    by_contra hcon
    push_neg at hcon
    apply hunc
    refine Set.countable_of_injective_of_countable_image (f := Node.lvl) ?_ ?_
    · intro p hp q hq h
      by_contra hne
      rcases hC hp hq hne with hle | hle
      · exact absurd h (ne_of_lt (Node.lvl_lt_of_lt (lt_of_le_of_ne hle hne)))
      · exact absurd h.symm (ne_of_lt (Node.lvl_lt_of_lt (lt_of_le_of_ne hle (Ne.symm hne))))
    · refine Set.Countable.mono ?_ (countable_Iio_of_lt (succ_lt_omega1 hb))
      rintro y ⟨p, hp, rfl⟩
      exact lt_of_le_of_lt (hcon p hp) (ord_lt_add_one b)
  set F : Ordinal → ℕ := fun x => if h : ∃ p, p ∈ C ∧ x < p.lvl then h.choose.f x else 0 with hF
  have hFval : ∀ p ∈ C, ∀ x < p.lvl, F x = p.f x := by
    intro p hp x hx
    have hex : ∃ p, p ∈ C ∧ x < p.lvl := ⟨p, hp, hx⟩
    rw [hF]
    simp only [dif_pos hex]
    obtain ⟨hqC, hqx⟩ := hex.choose_spec
    by_cases hpq : hex.choose = p
    · rw [hpq]
    · rcases hC hqC hp hpq with hle | hle
      · exact hle.2 x hqx
      · exact (hle.2 x hx).symm
  have hFfin : ∀ b < omega1, ∀ v : ℕ, {x | x < b ∧ F x = v}.Finite := by
    intro b hb v
    obtain ⟨p, hp, hbp⟩ := hunb b hb
    refine Set.Finite.subset (p.finOne v) ?_
    rintro x ⟨hx, hv⟩
    have hxp : x < p.lvl := lt_trans hx hbp
    exact ⟨hxp, by rw [← hFval p hp x hxp]; exact hv⟩
  have hfib : ∀ v : ℕ, {x | x < omega1 ∧ F x = v}.Finite := by
    intro v
    by_contra hinf
    rw [Set.not_finite] at hinf
    have e : ℕ ↪ {x : Ordinal // x ∈ {x | x < omega1 ∧ F x = v}} :=
      Set.Infinite.natEmbedding _ hinf
    set s : ℕ → Ordinal := fun n => (e n : Ordinal) with hs
    have hsinj : Function.Injective s := by
      intro m n hmn
      exact e.injective (Subtype.ext hmn)
    have hslt : ∀ n, s n < omega1 := fun n => (e n).2.1
    have hsup : iSup s < omega1 := iSup_lt_omega1 hslt
    have hb : iSup s + 1 < omega1 := succ_lt_omega1 hsup
    have hsub : Set.range s ⊆ {x | x < iSup s + 1 ∧ F x = v} := by
      rintro y ⟨n, rfl⟩
      exact ⟨lt_of_le_of_lt (Ordinal.le_iSup s n) (ord_lt_add_one _), (e n).2.2⟩
    exact (Set.infinite_range_of_injective hsinj).mono hsub (hFfin _ hb v)
  have hcount : (Set.Iio omega1).Countable := by
    refine Set.Countable.mono ?_ (Set.countable_iUnion (fun v : ℕ => (hfib v).countable))
    intro x hx
    exact Set.mem_iUnion.mpr ⟨F x, hx, rfl⟩
  exact not_countable_Iio_omega1 hcount

/-! ### The main theorem -/

/-- `lvl` exhibits the partially ordered set `T` as an *Aronszajn tree*: the predecessors of
any node `x` form a chain containing exactly one node at each level below `lvl x` (so `lvl x`
is the height of `x`, see `IsAronszajnTree.bijOn_pred`), every level below `ω₁` is nonempty
(so the tree has height `ω₁`), every level is countable, and there is no uncountable chain
(in particular, no uncountable branch). -/
structure IsAronszajnTree (T : Type*) [PartialOrder T] (lvl : T → Ordinal) : Prop where
  /-- every node has countable level -/
  lvl_lt_omega1 : ∀ x, lvl x < omega1
  /-- the level function is strictly monotone -/
  lvl_strictMono : ∀ ⦃x y : T⦄, x < y → lvl x < lvl y
  /-- the predecessors of a node form a chain -/
  pred_chain : ∀ x : T, IsChain (· ≤ ·) {y | y < x}
  /-- a node has exactly one predecessor at each smaller level -/
  pred_unique : ∀ x : T, ∀ b < lvl x, ∃! y : T, y < x ∧ lvl y = b
  /-- the tree has height `ω₁` -/
  levels_nonempty : ∀ b < omega1, ∃ x : T, lvl x = b
  /-- all levels are countable -/
  levels_countable : ∀ b : Ordinal, {x : T | lvl x = b}.Countable
  /-- there is no uncountable chain -/
  chains_countable : ∀ C : Set T, IsChain (· ≤ ·) C → C.Countable

/-- In an Aronszajn tree the level function restricts to a bijection from the set of
predecessors of a node `x` onto `Set.Iio (lvl x)`; together with strict monotonicity of `lvl`
this says that the predecessors of `x` are order isomorphic to the ordinal `lvl x`. -/
theorem IsAronszajnTree.bijOn_pred {T : Type*} [PartialOrder T] {lvl : T → Ordinal}
    (h : IsAronszajnTree T lvl) (x : T) : Set.BijOn lvl {y | y < x} (Set.Iio (lvl x)) := by
  refine ⟨fun y hy => h.lvl_strictMono hy, ?_, ?_⟩
  · intro y hy z hz hyz
    obtain ⟨w, -, hw⟩ := h.pred_unique x (lvl y) (h.lvl_strictMono hy)
    rw [hw y ⟨hy, rfl⟩, hw z ⟨hz, hyz.symm⟩]
  · intro b hb
    obtain ⟨y, ⟨hy, hyl⟩, -⟩ := h.pred_unique x b hb
    exact ⟨y, hy, hyl⟩

/-- **There exists an Aronszajn tree**: a tree of height `ω₁` all of whose levels are
countable and which has no uncountable branch (indeed no uncountable chain). -/
theorem Aronszajn_tree_exists :
    ∃ (T : Type 1) (inst : PartialOrder T) (lvl : T → Ordinal.{0}),
      @IsAronszajnTree T inst lvl := by
  refine ⟨Node, inferInstance, Node.lvl, ?_⟩
  refine
    { lvl_lt_omega1 := fun p => p.lvl_lt
      lvl_strictMono := fun p q h => Node.lvl_lt_of_lt h
      pred_chain := ?_
      pred_unique := ?_
      levels_nonempty := ?_
      levels_countable := Node.levels_countable
      chains_countable := Node.chains_countable }
  · intro p q hq r hr hne
    rcases le_total q.lvl r.lvl with h | h
    · exact Or.inl (Node.le_of_le_of_le (le_of_lt hq) (le_of_lt hr) h)
    · exact Or.inr (Node.le_of_le_of_le (le_of_lt hr) (le_of_lt hq) h)
  · intro p b hb
    refine ⟨p.restr b hb, ⟨p.restr_lt b hb, rfl⟩, ?_⟩
    rintro q ⟨hq, hql⟩
    refine Node.ext' hql (fun x => ?_)
    by_cases hx : x < b
    · have hxq : x < q.lvl := by rw [hql]; exact hx
      rw [(le_of_lt hq).2 x hxq]
      show p.f x = (if x < b then p.f x else 0)
      rw [if_pos hx]
    · rw [q.zero_out x (by rw [hql]; exact not_lt.mp hx)]
      show (0 : ℕ) = (if x < b then p.f x else 0)
      rw [if_neg hx]
  · intro b hb
    exact ⟨Node.base b hb, rfl⟩

end Frontier

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

