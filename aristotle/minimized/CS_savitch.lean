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

import RequestProject.Savitch.Machine

/-!
# Reduction to single-target reachability

`CS.addSink M` adds one new configuration (the *sink*) to `M`, with an edge from every
accepting configuration of `M` to the sink and no outgoing edge from the sink.  Then `M`
accepts iff the sink is reachable from the start configuration of `addSink M`, so that
deciding acceptance becomes deciding reachability between two *fixed* configurations.
-/

namespace CS

namespace Machine

/-- Add a sink configuration reachable exactly from the accepting configurations. -/

def Reaches (M : Machine) (a b : Fin M.N) : Prop :=
  Relation.ReflTransGen (fun x y => M.step x y = true) a b

/-- A machine accepts if some accepting configuration is reachable from the start. -/

theorem Reaches.refl (M : Machine) (a : Fin M.N) : M.Reaches a a := Relation.ReflTransGen.refl

theorem Reaches.tail {M : Machine} {a b c : Fin M.N} (h : M.Reaches a b)
    (hs : M.step b c = true) : M.Reaches a c := Relation.ReflTransGen.tail h hs

/-! ### Building a machine from an arbitrary finite state space -/

/-- The deterministic machine on a finite state space `S` given by the transition
function `f`, initial state `init` and accepting states `acc`. -/

def midFrom {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (i : ℕ) : Bool :=
  if h : i < n then (R a ⟨i, h⟩ && R ⟨i, h⟩ b) || midFrom R a b (i + 1) else false
termination_by n - i

theorem midFrom_of_lt {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) {i : ℕ} (h : i < n) :
    midFrom R a b i = ((R a ⟨i, h⟩ && R ⟨i, h⟩ b) || midFrom R a b (i + 1)) := by
  rw [midFrom]
  simp [h]

theorem midFrom_of_ge {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) {i : ℕ} (h : ¬ i < n) :
    midFrom R a b i = false := by
  rw [midFrom]
  simp [h]

theorem midFrom_eq_true_iff_aux {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (j : ℕ) :
    ∀ i, n ≤ i + j →
      (midFrom R a b i = true ↔ ∃ m : Fin n, i ≤ m.val ∧ R a m = true ∧ R m b = true) := by
  induction j with
  | zero =>
      intro i hi
      rw [midFrom_of_ge R a b (by omega)]
      simp only [false_iff, Bool.false_eq_true, not_exists]
      rintro m ⟨hm, -, -⟩
      omega
  | succ j ih =>
      intro i hi
      by_cases h : i < n
      · rw [midFrom_of_lt R a b h, Bool.or_eq_true_iff, ih (i + 1) (by omega)]
        constructor
        · rintro (hb | ⟨m, hm, h1, h2⟩)
          · exact ⟨⟨i, h⟩, le_rfl, (Bool.and_eq_true_iff.1 hb).1, (Bool.and_eq_true_iff.1 hb).2⟩
          · exact ⟨m, by omega, h1, h2⟩
        · rintro ⟨m, hm, h1, h2⟩
          rcases Nat.eq_or_lt_of_le hm with hm' | hm'
          · refine Or.inl ?_
            have : (⟨i, h⟩ : Fin n) = m := Fin.ext hm'
            rw [this]
            simp [h1, h2]
          · exact Or.inr ⟨m, by omega, h1, h2⟩
      · rw [midFrom_of_ge R a b h]
        simp only [false_iff, Bool.false_eq_true, not_exists]
        rintro m ⟨hm, -, -⟩
        omega

theorem midFrom_eq_true_iff {n : ℕ} (R : Fin n → Fin n → Bool) (a b : Fin n) (i : ℕ) :
    midFrom R a b i = true ↔ ∃ m : Fin n, i ≤ m.val ∧ R a m = true ∧ R m b = true :=
  midFrom_eq_true_iff_aux R a b n i (by omega)

/-! ### The Savitch recursion -/

/-- The Savitch recursion: `Reach M k a b` is true iff `b` can be reached from `a` in at
most `2 ^ k` steps. -/

def Reach (M : Machine) : ℕ → Fin M.N → Fin M.N → Bool
  | 0, a, b => decide (a = b) || M.step a b
  | (k + 1), a, b => midFrom (Reach M k) a b 0

theorem Reach_zero (a b : Fin M.N) : Reach M 0 a b = (decide (a = b) || M.step a b) := rfl

theorem Reach_succ_iff (k : ℕ) (a b : Fin M.N) :
    Reach M (k + 1) a b = true ↔ ∃ m, Reach M k a m = true ∧ Reach M k m b = true := by
  show midFrom (Reach M k) a b 0 = true ↔ _
  rw [midFrom_eq_true_iff]
  constructor
  · rintro ⟨m, -, h1, h2⟩; exact ⟨m, h1, h2⟩
  · rintro ⟨m, h1, h2⟩; exact ⟨m, Nat.zero_le _, h1, h2⟩

theorem Reach_sound {k : ℕ} {a b : Fin M.N} (h : Reach M k a b = true) : M.Reaches a b := by
  induction k generalizing a b with
  | zero =>
      rw [Reach_zero] at h
      rcases Bool.or_eq_true_iff.1 h with h | h
      · exact (of_decide_eq_true h) ▸ Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h
  | succ k ih =>
      obtain ⟨m, h1, h2⟩ := (Reach_succ_iff k a b).1 h
      exact (ih h1).trans (ih h2)

/-! ### Walks -/

/-- `W M n a b` : there is a walk of at most `n` steps from `a` to `b`. -/

def W (M : Machine) : ℕ → Fin M.N → Fin M.N → Bool
  | 0, a, b => decide (a = b)
  | (n + 1), a, b => decide (a = b) || decide (∃ c, M.step a c = true ∧ W M n c b = true)

theorem W_zero (a b : Fin M.N) : W M 0 a b = decide (a = b) := rfl

theorem W_succ_iff (n : ℕ) (a b : Fin M.N) :
    W M (n + 1) a b = true ↔ a = b ∨ ∃ c, M.step a c = true ∧ W M n c b = true := by
  show (decide (a = b) || decide (∃ c, M.step a c = true ∧ W M n c b = true)) = true ↔ _
  simp

theorem W_refl (n : ℕ) (a : Fin M.N) : W M n a a = true := by
  cases n with
  | zero => simp [W_zero]
  | succ n => exact (W_succ_iff n a a).2 (Or.inl rfl)

theorem W_mono {n : ℕ} {a b : Fin M.N} (h : W M n a b = true) : W M (n + 1) a b = true := by
  induction n generalizing a with
  | zero =>
      rw [W_zero] at h
      exact (W_succ_iff 0 a b).2 (Or.inl (of_decide_eq_true h))
  | succ n ih =>
      rcases (W_succ_iff n a b).1 h with h | ⟨c, hc, hw⟩
      · exact (W_succ_iff (n + 1) a b).2 (Or.inl h)
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨c, hc, ih hw⟩)

theorem W_le {n m : ℕ} {a b : Fin M.N} (hnm : n ≤ m) (h : W M n a b = true) :
    W M m a b = true := by
  induction m with
  | zero =>
      have : n = 0 := by omega
      exact this ▸ h
  | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact W_mono (ih (by omega))
      · have : n = m + 1 := by omega
        exact this ▸ h

theorem W_split {p q : ℕ} {a b : Fin M.N} (h : W M (p + q) a b = true) :
    ∃ c, W M p a c = true ∧ W M q c b = true := by
  induction p generalizing a with
  | zero => exact ⟨a, W_refl 0 a, by simpa using h⟩
  | succ p ih =>
      have h' : W M ((p + q) + 1) a b = true := by
        have : p + 1 + q = (p + q) + 1 := by omega
        rwa [this] at h
      rcases (W_succ_iff (p + q) a b).1 h' with rfl | ⟨c, hc, hw⟩
      · exact ⟨a, W_refl _ a, W_refl _ a⟩
      · obtain ⟨d, hd1, hd2⟩ := ih hw
        exact ⟨d, (W_succ_iff p a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

theorem W_snoc {n : ℕ} {a c b : Fin M.N} (h : W M n a c = true) (hs : M.step c b = true) :
    W M (n + 1) a b = true := by
  induction n generalizing a with
  | zero =>
      rw [W_zero] at h
      have : a = c := of_decide_eq_true h
      subst this
      exact (W_succ_iff 0 a b).2 (Or.inr ⟨b, hs, W_refl 0 b⟩)
  | succ n ih =>
      rcases (W_succ_iff n a c).1 h with rfl | ⟨d, hd, hw⟩
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨b, hs, W_refl _ b⟩)
      · exact (W_succ_iff (n + 1) a b).2 (Or.inr ⟨d, hd, ih hw⟩)

theorem W_unsnoc {n : ℕ} {a b : Fin M.N} (h : W M (n + 1) a b = true) :
    W M n a b = true ∨ ∃ c, W M n a c = true ∧ M.step c b = true := by
  induction n generalizing a with
  | zero =>
      rcases (W_succ_iff 0 a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl 0 a)
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        exact Or.inr ⟨a, W_refl 0 a, hc⟩
  | succ n ih =>
      rcases (W_succ_iff (n + 1) a b).1 h with rfl | ⟨c, hc, hw⟩
      · exact Or.inl (W_refl _ a)
      · rcases ih hw with hw' | ⟨d, hd1, hd2⟩
        · exact Or.inl ((W_succ_iff n a b).2 (Or.inr ⟨c, hc, hw'⟩))
        · exact Or.inr ⟨d, (W_succ_iff n a d).2 (Or.inr ⟨c, hc, hd1⟩), hd2⟩

theorem reaches_iff_exists_W {a b : Fin M.N} : M.Reaches a b ↔ ∃ n, W M n a b = true := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, W_refl 0 a⟩
    | tail h hs ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, W_snoc hn hs⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero =>
        rw [W_zero] at hn
        exact (of_decide_eq_true hn) ▸ Relation.ReflTransGen.refl
    | succ n ih =>
        rcases (W_succ_iff n a b).1 hn with rfl | ⟨c, hc, hw⟩
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.head hc (ih hw)

/-- A walk of length at most `2 ^ k` is found by the Savitch recursion at level `k`. -/

theorem Reach_of_W {k n : ℕ} {a b : Fin M.N} (hn : n ≤ 2 ^ k) (h : W M n a b = true) :
    Reach M k a b = true := by
  induction k generalizing n a b with
  | zero =>
      have h1 : W M 1 a b = true := W_le (by simpa using hn) h
      rcases (W_succ_iff 0 a b).1 h1 with rfl | ⟨c, hc, hw⟩
      · simp [Reach_zero]
      · rw [W_zero] at hw
        have : c = b := of_decide_eq_true hw
        subst this
        simp [Reach_zero, hc]
  | succ k ih =>
      have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      have h' : W M (2 ^ k + 2 ^ k) a b = true := W_le (by omega) h
      obtain ⟨c, h1, h2⟩ := W_split h'
      exact (Reach_succ_iff k a b).2 ⟨c, ih le_rfl h1, ih le_rfl h2⟩

/-! ### Reachable sets and stabilisation -/

/-- The set of configurations reachable from `a` in at most `i` steps. -/

def Rset (M : Machine) (a : Fin M.N) (i : ℕ) : Finset (Fin M.N) :=
  Finset.univ.filter (fun b => W M i a b = true)

theorem mem_Rset {a b : Fin M.N} {i : ℕ} : b ∈ Rset M a i ↔ W M i a b = true := by
  simp [Rset]

theorem Rset_subset_succ (a : Fin M.N) (i : ℕ) : Rset M a i ⊆ Rset M a (i + 1) := by
  intro b hb
  exact mem_Rset.2 (W_mono (mem_Rset.1 hb))

theorem Rset_mono {a : Fin M.N} {i j : ℕ} (hij : i ≤ j) : Rset M a i ⊆ Rset M a j := by
  intro b hb
  exact mem_Rset.2 (W_le hij (mem_Rset.1 hb))

theorem Rset_fix_succ {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    Rset M a (i + 2) = Rset M a (i + 1) := by
  apply Finset.Subset.antisymm _ (Rset_subset_succ a (i + 1))
  intro b hb
  rcases W_unsnoc (mem_Rset.1 hb) with hw | ⟨c, hc1, hc2⟩
  · exact mem_Rset.2 hw
  · have hc : c ∈ Rset M a i := h ▸ mem_Rset.2 hc1
    exact mem_Rset.2 (W_snoc (mem_Rset.1 hc) hc2)

theorem Rset_fix_step {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    ∀ t, Rset M a (i + t + 1) = Rset M a (i + t) := by
  intro t
  induction t with
  | zero => simpa using h
  | succ t ih =>
      have := Rset_fix_succ (a := a) (i := i + t) ih
      have e1 : i + (t + 1) + 1 = i + t + 2 := by omega
      have e2 : i + (t + 1) = i + t + 1 := by omega
      rw [e1, e2]
      exact this

theorem Rset_fix {a : Fin M.N} {i : ℕ} (h : Rset M a (i + 1) = Rset M a i) :
    ∀ j, i ≤ j → Rset M a j = Rset M a i := by
  have key : ∀ t, Rset M a (i + t) = Rset M a i := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        have e : i + (t + 1) = i + t + 1 := by omega
        rw [e, Rset_fix_step h t, ih]
  intro j hj
  obtain ⟨t, rfl⟩ : ∃ t, j = i + t := ⟨j - i, by omega⟩
  exact key t

theorem Rset_card_grow {a : Fin M.N} (i : ℕ) (h : ∀ j < i, Rset M a (j + 1) ≠ Rset M a j) :
    i + 1 ≤ (Rset M a i).card := by
  induction i with
  | zero =>
      have : a ∈ Rset M a 0 := mem_Rset.2 (W_refl 0 a)
      exact Finset.card_pos.2 ⟨a, this⟩
  | succ i ih =>
      have hi : i + 1 ≤ (Rset M a i).card := ih (fun j hj => h j (by omega))
      have hne : Rset M a (i + 1) ≠ Rset M a i := h i (by omega)
      have hss : Rset M a i ⊂ Rset M a (i + 1) :=
        ⟨Rset_subset_succ a i, fun hcon => hne (Finset.Subset.antisymm hcon (Rset_subset_succ a i))⟩
      have := Finset.card_lt_card hss
      omega

theorem Rset_subset_card {a : Fin M.N} (n : ℕ) : Rset M a n ⊆ Rset M a M.N := by
  by_cases h : ∃ i < M.N, Rset M a (i + 1) = Rset M a i
  · obtain ⟨i, hi, hfix⟩ := h
    rcases Nat.lt_or_ge n M.N with hn | hn
    · exact Rset_mono (by omega)
    · have h1 : Rset M a n = Rset M a i := Rset_fix hfix n (by omega)
      have h2 : Rset M a M.N = Rset M a i := Rset_fix hfix M.N (by omega)
      rw [h1, h2]
  · push_neg at h
    have := Rset_card_grow (M := M) (a := a) M.N (fun j hj => h j hj)
    have hle : (Rset M a M.N).card ≤ M.N := by
      simpa using Finset.card_le_univ (Rset M a M.N)
    omega

/-- **Reachability is decided by the Savitch recursion**, provided `2 ^ K` is at least the
number of configurations. -/

theorem Reach_eq_true_iff_reaches {K : ℕ} (hK : M.N ≤ 2 ^ K) (a b : Fin M.N) :
    Reach M K a b = true ↔ M.Reaches a b := by
  constructor
  · exact Reach_sound
  · intro h
    obtain ⟨n, hn⟩ := reaches_iff_exists_W.1 h
    have hb : b ∈ Rset M a M.N := Rset_subset_card n (mem_Rset.2 hn)
    exact Reach_of_W hK (mem_Rset.1 hb)

end CS
