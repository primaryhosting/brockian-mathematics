import Mathlib

/-!
# Antimirov partial derivatives and finiteness of left quotients

This file develops Antimirov's partial derivatives of a regular expression, and uses them to
show that a language described by a regular expression has only finitely many left quotients.
Combined with the Myhill–Nerode theorem this gives the "regular expression → DFA" direction of
Kleene's theorem.
-/

namespace CS

open RegularExpression

variable {α : Type*}

/-- The language of a set of regular expressions: the union of the languages they describe. -/
def langSet (S : Set (RegularExpression α)) : Language α :=
  {w | ∃ p ∈ S, w ∈ p.matches'}

/-- The language of a list of regular expressions. -/
def langList (l : List (RegularExpression α)) : Language α := langSet {p | p ∈ l}

@[simp]
theorem mem_langList {l : List (RegularExpression α)} {w : List α} :
    w ∈ langList l ↔ ∃ p ∈ l, w ∈ p.matches' := Iff.rfl

@[simp]
theorem langList_nil : langList ([] : List (RegularExpression α)) = 0 := by
  ext w; simp

@[simp]
theorem langList_singleton (p : RegularExpression α) : langList [p] = p.matches' := by
  ext w; simp

theorem langList_append (l₁ l₂ : List (RegularExpression α)) :
    langList (l₁ ++ l₂) = langList l₁ + langList l₂ := by
  ext w
  simp only [mem_langList, List.mem_append, Language.mem_add]
  constructor
  · rintro ⟨p, hp | hp, hw⟩
    · exact Or.inl ⟨p, hp, hw⟩
    · exact Or.inr ⟨p, hp, hw⟩
  · rintro (⟨p, hp, hw⟩ | ⟨p, hp, hw⟩)
    · exact ⟨p, Or.inl hp, hw⟩
    · exact ⟨p, Or.inr hp, hw⟩

theorem langList_map_mul (l : List (RegularExpression α)) (Q : RegularExpression α) :
    langList (l.map (· * Q)) = langList l * Q.matches' := by
  ext w
  simp only [mem_langList, List.mem_map, Language.mem_mul]
  constructor
  · rintro ⟨p, ⟨p', hp', rfl⟩, u, hu, v, hv, rfl⟩
    exact ⟨u, ⟨p', hp', hu⟩, v, hv, rfl⟩
  · rintro ⟨u, ⟨p', hp', hu⟩, v, hv, rfl⟩
    exact ⟨p' * Q, ⟨p', hp', rfl⟩, u, hu, v, hv, rfl⟩

/-- The (finite) Antimirov set of a regular expression: a list containing every regular
expression reachable by iterated partial derivatives. -/
def pdset : RegularExpression α → List (RegularExpression α)
  | 0 => []
  | 1 => []
  | char _ => [1]
  | P + Q => pdset P ++ pdset Q
  | P * Q => (pdset P).map (· * Q) ++ pdset Q
  | RegularExpression.star P => (pdset P).map (· * RegularExpression.star P)

@[simp] theorem pdset_zero : pdset (0 : RegularExpression α) = [] := rfl
@[simp] theorem pdset_one : pdset (1 : RegularExpression α) = [] := rfl
@[simp] theorem pdset_char (b : α) : pdset (char b) = [1] := rfl
@[simp] theorem pdset_add (P Q : RegularExpression α) : pdset (P + Q) = pdset P ++ pdset Q := rfl
@[simp] theorem pdset_mul (P Q : RegularExpression α) :
    pdset (P * Q) = (pdset P).map (· * Q) ++ pdset Q := rfl
@[simp] theorem pdset_star (P : RegularExpression α) :
    pdset P.star = (pdset P).map (· * P.star) := rfl

section DecidableEq

variable [DecidableEq α]

/-- Antimirov's partial derivative: a list of regular expressions whose union describes the
left quotient by a single letter. -/
def pderiv : RegularExpression α → α → List (RegularExpression α)
  | 0, _ => []
  | 1, _ => []
  | char b, a => if b = a then [1] else []
  | P + Q, a => pderiv P a ++ pderiv Q a
  | P * Q, a => (pderiv P a).map (· * Q) ++ (if P.matchEpsilon then pderiv Q a else [])
  | RegularExpression.star P, a => (pderiv P a).map (· * RegularExpression.star P)

@[simp] theorem pderiv_zero (a : α) : pderiv 0 a = [] := rfl
@[simp] theorem pderiv_one (a : α) : pderiv 1 a = [] := rfl
theorem pderiv_char (b a : α) : pderiv (char b) a = if b = a then [1] else [] := rfl
@[simp] theorem pderiv_add (P Q : RegularExpression α) (a : α) :
    pderiv (P + Q) a = pderiv P a ++ pderiv Q a := rfl
@[simp] theorem pderiv_mul (P Q : RegularExpression α) (a : α) :
    pderiv (P * Q) a =
      (pderiv P a).map (· * Q) ++ (if P.matchEpsilon then pderiv Q a else []) := rfl
@[simp] theorem pderiv_star (P : RegularExpression α) (a : α) :
    pderiv P.star a = (pderiv P a).map (· * P.star) := rfl

/-- Extension of `pderiv` to lists of regular expressions. -/
def pderivList (l : List (RegularExpression α)) (a : α) : List (RegularExpression α) :=
  l.flatMap (fun p => pderiv p a)

/-- Iterated partial derivative along a word. -/
def pderivs (l : List (RegularExpression α)) : List α → List (RegularExpression α)
  | [] => l
  | a :: w => pderivs (pderivList l a) w

/-- Semantics of the Brzozowski derivative, in terms of `matches'`. -/
theorem mem_matches'_deriv (P : RegularExpression α) (a : α) (w : List α) :
    w ∈ (P.deriv a).matches' ↔ a :: w ∈ P.matches' := by
  rw [← rmatch_iff_matches', ← rmatch_iff_matches']
  rfl

theorem deriv_mul_eq (P Q : RegularExpression α) (a : α) :
    (P * Q).deriv a =
      if P.matchEpsilon then P.deriv a * Q + Q.deriv a else P.deriv a * Q := rfl

/-- Antimirov's partial derivatives compute the same language as Brzozowski's derivative. -/
theorem langList_pderiv (P : RegularExpression α) (a : α) :
    langList (pderiv P a) = (P.deriv a).matches' := by
  induction P with
  | zero => rw [zero_def]; simp
  | epsilon => rw [one_def]; simp
  | char b =>
    rw [pderiv_char]
    by_cases h : b = a
    · subst h
      rw [if_pos rfl, RegularExpression.deriv_char_self, langList_singleton]
    · rw [if_neg h, RegularExpression.deriv_char_of_ne h, langList_nil]
      rfl
  | plus P Q ihP ihQ =>
    rw [plus_def, pderiv_add, langList_append, ihP, ihQ, RegularExpression.deriv_add]
    simp
  | comp P Q ihP ihQ =>
    rw [comp_def, pderiv_mul, langList_append, langList_map_mul, ihP]
    by_cases h : P.matchEpsilon
    · rw [if_pos h, ihQ, deriv_mul_eq, if_pos h]
      simp
    · rw [if_neg h, deriv_mul_eq, if_neg h]
      simp
  | star P ihP =>
    rw [pderiv_star, langList_map_mul, ihP, RegularExpression.deriv_star]
    simp

theorem langList_pderivList (l : List (RegularExpression α)) (a : α) :
    langList (pderivList l a) = (langList l).leftQuotient [a] := by
  ext w
  simp only [pderivList, mem_langList, List.mem_flatMap, Language.mem_leftQuotient,
    List.singleton_append]
  constructor
  · rintro ⟨q, ⟨p, hp, hq⟩, hw⟩
    refine ⟨p, hp, (mem_matches'_deriv p a w).1 ?_⟩
    rw [← langList_pderiv]
    exact ⟨q, hq, hw⟩
  · rintro ⟨p, hp, hw⟩
    have : w ∈ langList (pderiv p a) := by
      rw [langList_pderiv]; exact (mem_matches'_deriv p a w).2 hw
    obtain ⟨q, hq, hw'⟩ := this
    exact ⟨q, ⟨p, hp, hq⟩, hw'⟩

theorem langList_pderivs (l : List (RegularExpression α)) (w : List α) :
    langList (pderivs l w) = (langList l).leftQuotient w := by
  induction w generalizing l with
  | nil => simp [pderivs]
  | cons a w ih =>
    rw [pderivs, ih, langList_pderivList, ← Language.leftQuotient_append]
    rfl

theorem pderiv_mem_pdset {P : RegularExpression α} {a : α} {q : RegularExpression α}
    (h : q ∈ pderiv P a) : q ∈ pdset P := by
  induction P generalizing q with
  | zero => rw [zero_def, pderiv_zero] at h; simp at h
  | epsilon => rw [one_def, pderiv_one] at h; simp at h
  | char b =>
    rw [pderiv_char] at h
    by_cases hb : b = a
    · rw [if_pos hb] at h
      simpa [pdset_char] using h
    · rw [if_neg hb] at h; simp at h
  | plus P Q ihP ihQ =>
    rw [plus_def, pderiv_add, List.mem_append] at h
    rw [plus_def, pdset_add, List.mem_append]
    rcases h with h | h
    · exact Or.inl (ihP h)
    · exact Or.inr (ihQ h)
  | comp P Q ihP ihQ =>
    rw [comp_def, pderiv_mul, List.mem_append] at h
    rw [comp_def, pdset_mul, List.mem_append]
    rcases h with h | h
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
      exact Or.inl (List.mem_map.2 ⟨p, ihP hp, rfl⟩)
    · split_ifs at h with hc
      · exact Or.inr (ihQ h)
      · simp at h
  | star P ihP =>
    rw [pderiv_star] at h
    rw [pdset_star]
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 h
    exact List.mem_map.2 ⟨p, ihP hp, rfl⟩

/-- The Antimirov set is closed under partial derivatives. -/
theorem pdset_closed {P : RegularExpression α} :
    ∀ {p : RegularExpression α}, p ∈ pdset P → ∀ {a : α} {q : RegularExpression α},
      q ∈ pderiv p a → q ∈ pdset P := by
  induction P with
  | zero => intro p hp; rw [zero_def, pdset_zero] at hp; simp at hp
  | epsilon => intro p hp; rw [one_def, pdset_one] at hp; simp at hp
  | char b =>
    intro p hp a q hq
    rw [pdset_char, List.mem_singleton] at hp
    subst hp
    rw [pderiv_one] at hq
    simp at hq
  | plus P Q ihP ihQ =>
    intro p hp a q hq
    rw [plus_def, pdset_add, List.mem_append] at hp
    rw [plus_def, pdset_add, List.mem_append]
    rcases hp with hp | hp
    · exact Or.inl (ihP hp hq)
    · exact Or.inr (ihQ hp hq)
  | comp P Q ihP ihQ =>
    intro p hp a q hq
    rw [comp_def, pdset_mul, List.mem_append] at hp
    rw [comp_def, pdset_mul, List.mem_append]
    rcases hp with hp | hp
    · obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
      rw [pderiv_mul, List.mem_append] at hq
      rcases hq with hq | hq
      · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact Or.inl (List.mem_map.2 ⟨q', ihP hp' hq', rfl⟩)
      · split_ifs at hq with hc
        · exact Or.inr (pderiv_mem_pdset hq)
        · simp at hq
    · exact Or.inr (ihQ hp hq)
  | star P ihP =>
    intro p hp a q hq
    rw [pdset_star] at hp
    rw [pdset_star]
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    rw [pderiv_mul, List.mem_append] at hq
    rcases hq with hq | hq
    · obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
      exact List.mem_map.2 ⟨q', ihP hp' hq', rfl⟩
    · split_ifs at hq with hc
      · rw [pderiv_star] at hq
        obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
        exact List.mem_map.2 ⟨q', pderiv_mem_pdset hq', rfl⟩
      · simp at hq

theorem pderivs_subset (r : RegularExpression α) (w : List α) {l : List (RegularExpression α)}
    (hl : ∀ p ∈ l, p ∈ r :: pdset r) : ∀ q ∈ pderivs l w, q ∈ r :: pdset r := by
  induction w generalizing l with
  | nil => simpa [pderivs] using hl
  | cons a w ih =>
    rw [pderivs]
    refine ih ?_
    intro q hq
    obtain ⟨p, hp, hq⟩ := List.mem_flatMap.1 hq
    rcases List.mem_cons.1 (hl p hp) with h | h
    · subst h
      exact List.mem_cons_of_mem _ (pderiv_mem_pdset hq)
    · exact List.mem_cons_of_mem _ (pdset_closed h hq)

/-- A language described by a regular expression has finitely many left quotients. -/
theorem finite_range_leftQuotient_matches' (r : RegularExpression α) :
    (Set.range (Language.leftQuotient r.matches')).Finite := by
  have hbase : ({p | p ∈ r :: pdset r} : Set (RegularExpression α)).Finite :=
    (r :: pdset r).finite_toSet
  have hsub : Set.range (Language.leftQuotient r.matches') ⊆
      langSet '' {S | S ⊆ {p | p ∈ r :: pdset r}} := by
    rintro L ⟨w, rfl⟩
    refine ⟨{p | p ∈ pderivs [r] w}, ?_, ?_⟩
    · intro p hp
      exact pderivs_subset r w (by simp) p hp
    · have h1 : langList [r] = r.matches' := by
        ext x; simp
      rw [show langSet {p | p ∈ pderivs [r] w} = langList (pderivs [r] w) from rfl,
        langList_pderivs, h1]
  exact Set.Finite.subset (Set.Finite.image _ hbase.finite_subsets) hsub

end DecidableEq

/-- **Kleene, one direction**: a language described by a regular expression is regular. -/
theorem isRegular_of_regex {r : RegularExpression α} {L : Language α} (h : r.matches' = L) :
    L.IsRegular := by
  classical
  exact Language.IsRegular.of_finite_range_leftQuotient
    (h ▸ finite_range_leftQuotient_matches' r)

end CS

import Mathlib

/-!
# Kleene's algorithm: from a DFA to a regular expression

Given a DFA over a finite alphabet, we construct (the language of) a regular expression
describing the accepted language, by the classical dynamic-programming argument over the
set of allowed intermediate states.
-/

namespace CS

open Language Computability

variable {α : Type} {σ : Type} {ι : Type}

/-- A language is *described by a regular expression*. -/
def IsRegexLang (L : Language α) : Prop := ∃ r : RegularExpression α, r.matches' = L

namespace IsRegexLang

protected theorem zero : IsRegexLang (0 : Language α) := ⟨0, rfl⟩

protected theorem one : IsRegexLang (1 : Language α) := ⟨1, rfl⟩

protected theorem char (a : α) : IsRegexLang ({[a]} : Language α) :=
  ⟨RegularExpression.char a, rfl⟩

protected theorem add {L₁ L₂ : Language α} (h₁ : IsRegexLang L₁) (h₂ : IsRegexLang L₂) :
    IsRegexLang (L₁ + L₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ + r₂, rfl⟩

protected theorem mul {L₁ L₂ : Language α} (h₁ : IsRegexLang L₁) (h₂ : IsRegexLang L₂) :
    IsRegexLang (L₁ * L₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ * r₂, rfl⟩

protected theorem kstar {L : Language α} (h : IsRegexLang L) : IsRegexLang L∗ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r.star, rfl⟩

protected theorem congr {L₁ L₂ : Language α} (h : IsRegexLang L₁) (e : L₁ = L₂) :
    IsRegexLang L₂ := e ▸ h

protected theorem sum (s : Finset ι) (f : ι → Language α) (h : ∀ i ∈ s, IsRegexLang (f i)) :
    IsRegexLang (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRegexLang.zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end IsRegexLang

theorem mem_finset_sum (s : Finset ι) (f : ι → Language α) (w : List α) :
    w ∈ ∑ i ∈ s, f i ↔ ∃ i ∈ s, w ∈ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Language.mem_add, ih]
    simp

namespace DFAPath

variable (M : DFA α σ)

/-- `pathLang M S i j` is the set of words taking state `i` to state `j` in `M`, all of whose
proper nonempty prefixes end in a state belonging to `S`. -/
def pathLang (S : Finset σ) (i j : σ) : Language α :=
  {w | M.evalFrom i w = j ∧ ∀ u v : List α, u ++ v = w → u ≠ [] → v ≠ [] → M.evalFrom i u ∈ S}

theorem mem_pathLang {S : Finset σ} {i j : σ} {w : List α} :
    w ∈ pathLang M S i j ↔
      M.evalFrom i w = j ∧ ∀ u v : List α, u ++ v = w → u ≠ [] → v ≠ [] → M.evalFrom i u ∈ S :=
  Iff.rfl

theorem nil_mem_pathLang (S : Finset σ) (i : σ) : [] ∈ pathLang M S i i := by
  refine ⟨rfl, ?_⟩
  intro u v huv hu hv
  exact absurd (List.append_eq_nil_iff.1 huv).1 hu

theorem pathLang_mono {S T : Finset σ} (h : S ⊆ T) (i j : σ) :
    pathLang M S i j ≤ pathLang M T i j := by
  rintro w ⟨hw, hint⟩
  exact ⟨hw, fun u v huv hu hv => h (hint u v huv hu hv)⟩

/-- Concatenating two paths through an allowed intermediate state `k`. -/
theorem pathLang_splice {T : Finset σ} {i j k : σ} (hk : k ∈ T) :
    pathLang M T i k * pathLang M T k j ≤ pathLang M T i j := by
  rintro w hw
  rw [Language.mem_mul] at hw
  obtain ⟨u, ⟨hu, hui⟩, v, ⟨hv, hvi⟩, rfl⟩ := hw
  refine ⟨by rw [M.evalFrom_of_append, hu, hv], ?_⟩
  intro p q hpq hp hq
  rcases List.append_eq_append_iff.1 hpq with ⟨t, hut, hqt⟩ | ⟨t, hpt, hvt⟩
  · rcases eq_or_ne t [] with rfl | ht
    · rw [List.append_nil] at hut
      subst hut
      rw [hu]
      exact hk
    · exact hui p t hut.symm hp ht
  · subst hpt
    rw [M.evalFrom_of_append, hu]
    rcases eq_or_ne t [] with rfl | ht
    · simpa using hk
    · exact hvi t q hvt.symm ht hq

theorem kstar_le_pathLang {T : Finset σ} {k : σ} (hk : k ∈ T) {L : Language α}
    (hL : L ≤ pathLang M T k k) : L∗ ≤ pathLang M T k k := by
  rintro w hw
  rw [Language.mem_kstar] at hw
  obtain ⟨ls, rfl, hls⟩ := hw
  induction ls with
  | nil => simpa using nil_mem_pathLang M T k
  | cons x xs ih =>
    have hx : x ∈ pathLang M T k k := hL (hls x (by simp))
    have hxs : xs.flatten ∈ pathLang M T k k := ih fun y hy => hls y (by simp [hy])
    have : x ++ xs.flatten ∈ pathLang M T k k :=
      pathLang_splice M hk ⟨x, hx, xs.flatten, hxs, rfl⟩
    simpa using this

theorem cons_mem_kstar {L : Language α} {x y : List α} (hx : x ∈ L) (hy : y ∈ L∗) :
    x ++ y ∈ L∗ := by
  rw [Language.mem_kstar] at hy ⊢
  obtain ⟨ls, rfl, hls⟩ := hy
  refine ⟨x :: ls, by simp, ?_⟩
  intro z hz
  rcases List.mem_cons.1 hz with rfl | hz
  · exact hx
  · exact hls z hz

/-- Kleene's recursion: adding a new allowed intermediate state `k`. -/
theorem pathLang_insert [DecidableEq σ] (S : Finset σ) (i j k : σ) :
    pathLang M (insert k S) i j =
      pathLang M S i j + pathLang M S i k * ((pathLang M S k k)∗ * pathLang M S k j) := by
  classical
  apply le_antisymm
  · have key : ∀ n : ℕ, ∀ w : List α, w.length ≤ n → ∀ i : σ,
        w ∈ pathLang M (insert k S) i j →
        w ∈ pathLang M S i j + pathLang M S i k * ((pathLang M S k k)∗ * pathLang M S k j) := by
      intro n
      induction n with
      | zero =>
        intro w hlen i hw
        have hw0 : w = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
        subst hw0
        rw [Language.mem_add]
        exact Or.inl ⟨hw.1, fun u v huv hu _ => absurd (List.append_eq_nil_iff.1 huv).1 hu⟩
      | succ n ih =>
        intro w hlen i hw
        rw [Language.mem_add]
        by_cases hcase : ∀ u v : List α, u ++ v = w → u ≠ [] → v ≠ [] → M.evalFrom i u ∈ S
        · exact Or.inl ⟨hw.1, hcase⟩
        · right
          push_neg at hcase
          obtain ⟨u₀, v₀, huv₀, hu₀, hv₀, hnot⟩ := hcase
          have hu₀pos : 0 < u₀.length := by
            cases u₀ with
            | nil => exact absurd rfl hu₀
            | cons _ _ => simp
          have hv₀pos : 0 < v₀.length := by
            cases v₀ with
            | nil => exact absurd rfl hv₀
            | cons _ _ => simp
          have hlensum : u₀.length + v₀.length = w.length := by
            rw [← huv₀]; simp
          have hex : ∃ m : ℕ, 0 < m ∧ m < w.length ∧ M.evalFrom i (w.take m) = k := by
            refine ⟨u₀.length, hu₀pos, by omega, ?_⟩
            have htake : w.take u₀.length = u₀ := by rw [← huv₀]; simp
            rw [htake]
            rcases Finset.mem_insert.1 (hw.2 u₀ v₀ huv₀ hu₀ hv₀) with h | h
            · exact h
            · exact absurd h hnot
          obtain ⟨hm0, hmlt, hmk⟩ := Nat.find_spec hex
          set m := Nat.find hex with hmdef
          obtain ⟨u, huu⟩ : ∃ u, w.take m = u := ⟨_, rfl⟩
          obtain ⟨v, hvv⟩ : ∃ v, w.drop m = v := ⟨_, rfl⟩
          have huv : u ++ v = w := by rw [← huu, ← hvv]; exact List.take_append_drop m w
          have hulen : u.length = m := by
            rw [← huu, List.length_take]; omega
          have hvlen : v.length = w.length - m := by rw [← hvv]; simp
          have hune : u ≠ [] := by
            intro h
            rw [h] at hulen
            simp at hulen
            omega
          have hvne : v ≠ [] := by
            intro h
            rw [h] at hvlen
            simp at hvlen
            omega
          rw [huu] at hmk
          have hu_path : u ∈ pathLang M S i k := by
            refine ⟨hmk, ?_⟩
            intro p q hpq hp hq
            have hqpos : 0 < q.length := by
              cases q with
              | nil => exact absurd rfl hq
              | cons _ _ => simp
            have hsum : p.length + q.length = m := by
              have := congrArg List.length hpq
              simp only [List.length_append] at this
              omega
            have hplt : p.length < m := by omega
            have hpre : p <+: w := ⟨q ++ v, by rw [← huv, ← hpq]; simp⟩
            have hptake : w.take p.length = p := (List.prefix_iff_eq_take.1 hpre).symm
            have hpin : M.evalFrom i p ∈ insert k S := by
              refine hw.2 p (q ++ v) (by rw [← huv, ← hpq]; simp) hp ?_
              simp [hvne]
            rcases Finset.mem_insert.1 hpin with h | h
            · exfalso
              refine Nat.find_min hex hplt ⟨?_, ?_, ?_⟩
              · cases p with
                | nil => exact absurd rfl hp
                | cons _ _ => simp
              · omega
              · rw [hptake]; exact h
            · exact h
          have hv_path : v ∈ pathLang M (insert k S) k j := by
            refine ⟨?_, ?_⟩
            · have h1 := hw.1
              rw [← huv, M.evalFrom_of_append, hmk] at h1
              exact h1
            · intro p q hpq hp hq
              have h2 : M.evalFrom i (u ++ p) ∈ insert k S :=
                hw.2 (u ++ p) q (by rw [← huv, ← hpq]; simp) (by simp [hune]) hq
              rwa [M.evalFrom_of_append, hmk] at h2
          have hvlen' : v.length ≤ n := by omega
          have hv' := ih v hvlen' k hv_path
          have hv2 : v ∈ (pathLang M S k k)∗ * pathLang M S k j := by
            rw [Language.mem_add] at hv'
            rcases hv' with h | h
            · exact ⟨[], Language.nil_mem_kstar _, v, h, by simp⟩
            · obtain ⟨a, ha, rest, hrest, hav⟩ := h
              obtain ⟨b, hb, c, hc, hbc⟩ := hrest
              refine ⟨a ++ b, cons_mem_kstar ha hb, c, hc, ?_⟩
              rw [← hav, ← hbc]; simp
          exact ⟨u, hu_path, v, hv2, huv⟩
    intro w hw
    exact key w.length w le_rfl i hw
  · rintro w hw
    rw [Language.mem_add] at hw
    have hk : k ∈ insert k S := Finset.mem_insert_self k S
    rcases hw with h | h
    · exact pathLang_mono M (Finset.subset_insert k S) i j h
    · obtain ⟨u, hu, rest, hrest, rfl⟩ := h
      obtain ⟨s, hs, t, ht, rfl⟩ := hrest
      have hu' : u ∈ pathLang M (insert k S) i k :=
        pathLang_mono M (Finset.subset_insert k S) i k hu
      have hs' : s ∈ pathLang M (insert k S) k k :=
        kstar_le_pathLang M hk (pathLang_mono M (Finset.subset_insert k S) k k) hs
      have ht' : t ∈ pathLang M (insert k S) k j :=
        pathLang_mono M (Finset.subset_insert k S) k j ht
      have hst : s ++ t ∈ pathLang M (insert k S) k j :=
        pathLang_splice M hk ⟨s, hs', t, ht', rfl⟩
      exact pathLang_splice M hk ⟨u, hu', s ++ t, hst, rfl⟩

theorem pathLang_empty [Fintype α] [DecidableEq σ] (i j : σ) :
    pathLang M ∅ i j =
      (if i = j then 1 else 0) +
        ∑ a ∈ Finset.univ.filter (fun a : α => M.step i a = j), ({[a]} : Language α) := by
  ext w
  rw [Language.mem_add, mem_finset_sum]
  constructor
  · rintro ⟨hw, hint⟩
    match w with
    | [] =>
      left
      simp only [DFA.evalFrom_nil] at hw
      rw [if_pos hw]
      rfl
    | [a] =>
      right
      exact ⟨a, by simpa using hw, rfl⟩
    | a :: b :: t =>
      exact absurd (hint [a] (b :: t) rfl (by simp) (by simp)) (by simp)
  · rintro (h | ⟨a, ha, rfl⟩)
    · by_cases hij : i = j
      · rw [if_pos hij] at h
        rw [Language.mem_one] at h
        subst h
        subst hij
        exact nil_mem_pathLang M ∅ i
      · rw [if_neg hij] at h
        exact absurd h (by simp)
    · simp only [Finset.mem_filter] at ha
      refine ⟨by simpa using ha.2, ?_⟩
      intro u v huv hu hv
      exfalso
      have hlen : u.length + v.length = 1 := by
        rw [← List.length_append, huv]; simp
      have hu1 : 0 < u.length := by
        cases u with
        | nil => exact absurd rfl hu
        | cons _ _ => simp
      have hv1 : 0 < v.length := by
        cases v with
        | nil => exact absurd rfl hv
        | cons _ _ => simp
      omega

theorem isRegexLang_pathLang [Fintype α] [DecidableEq σ] (S : Finset σ) (i j : σ) :
    IsRegexLang (pathLang M S i j) := by
  induction S using Finset.induction generalizing i j with
  | empty =>
    rw [pathLang_empty]
    refine IsRegexLang.add ?_ (IsRegexLang.sum _ _ fun a _ => IsRegexLang.char a)
    by_cases h : i = j
    · rw [if_pos h]; exact IsRegexLang.one
    · rw [if_neg h]; exact IsRegexLang.zero
  | insert k S hk ih =>
    rw [pathLang_insert]
    exact (ih i j).add ((ih i k).mul (((ih k k).kstar).mul (ih k j)))

theorem accepts_eq_sum [Fintype σ] [DecidablePred (· ∈ M.accept)] :
    M.accepts = ∑ j ∈ Finset.univ.filter (fun j => j ∈ M.accept),
      pathLang M Finset.univ M.start j := by
  ext w
  rw [mem_finset_sum]
  constructor
  · intro hw
    refine ⟨M.eval w, ?_, rfl, fun u v _ _ _ => Finset.mem_univ _⟩
    simpa using (DFA.mem_accepts M).1 hw
  · rintro ⟨j, hj, hwj, -⟩
    simp only [Finset.mem_filter] at hj
    rw [DFA.mem_accepts M]
    have hev : M.eval w = j := hwj
    rw [hev]
    exact hj.2

end DFAPath

/-- **Kleene, other direction**: a regular language is described by a regular expression. -/
theorem regex_of_isRegular [Fintype α] {L : Language α} (h : L.IsRegular) : IsRegexLang L := by
  classical
  obtain ⟨σ, _, M, rfl⟩ := h
  rw [DFAPath.accepts_eq_sum M]
  exact IsRegexLang.sum _ _ fun j _ => DFAPath.isRegexLang_pathLang M _ _ _

end CS

import Mathlib
import RequestProject.Antimirov
import RequestProject.KleeneAlgorithm
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


namespace CS

/--
**Kleene's theorem** (over a finite alphabet): a language is described by a regular expression
if and only if it is regular, i.e. accepted by a deterministic finite automaton with finitely
many states (`Language.IsRegular`).
-/
theorem kleene_regex_dfa {α : Type} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔ L.IsRegular := by
  constructor
  · rintro ⟨r, hr⟩
    exact isRegular_of_regex hr
  · intro h
    exact regex_of_isRegular h

end CS

namespace CS

/-- Sanity check: the singleton language `{[true]}` over `Bool` is regular. -/
example : Language.IsRegular ({[true]} : Language Bool) :=
  (kleene_regex_dfa _).1 ⟨RegularExpression.char true, rfl⟩

/-- Sanity check: every regular language over a finite alphabet is matched by some
regular expression. -/
example (M : DFA Bool (Fin 3)) : ∃ r : RegularExpression Bool, r.matches' = M.accepts :=
  (kleene_regex_dfa _).2 ⟨Fin 3, inferInstance, M, rfl⟩

end CS

