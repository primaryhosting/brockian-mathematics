import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Kleene's theorem: over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states.
-/

open Language Computability

namespace CS

variable {α : Type*}

@[simp] theorem mem_singleton_language {y z : List α} : y ∈ ({z} : Language α) ↔ y = z := Iff.rfl

@[simp] theorem mem_sup_language {A B : Language α} {y : List α} :
    y ∈ A ⊔ B ↔ y ∈ A ∨ y ∈ B := Iff.rfl

@[simp] theorem mem_add_language {A B : Language α} {y : List α} :
    y ∈ A + B ↔ y ∈ A ∨ y ∈ B := Iff.rfl

@[simp] theorem mem_setOf_language {p : List α → Prop} {y : List α} :
    y ∈ ({x | p x} : Language α) ↔ p y := Iff.rfl

@[simp] theorem mem_sSup_language {S : Set (Language α)} {y : List α} :
    y ∈ sSup S ↔ ∃ L ∈ S, y ∈ L := Iff.rfl

/-! ## Part 1: the language of a regular expression is accepted by a DFA -/

section RegexToDFA

/-- A language all of whose left quotients lie in a fixed finite set of languages is regular. -/
theorem isRegular_of_leftQuotient_mem {L : Language α} {S : Set (Language α)}
    (hS : S.Finite) (h : ∀ x, L.leftQuotient x ∈ S) : L.IsRegular :=
  Language.IsRegular.of_finite_range_leftQuotient
    (hS.subset (by rintro _ ⟨x, rfl⟩; exact h x))

theorem isRegular_zero : (0 : Language α).IsRegular := by
  refine isRegular_of_leftQuotient_mem (S := {0}) (Set.finite_singleton _) fun x => ?_
  simp only [Set.mem_singleton_iff]
  ext y
  simp

theorem isRegular_one : (1 : Language α).IsRegular := by
  refine isRegular_of_leftQuotient_mem (S := {0, 1}) (Set.toFinite _) fun x => ?_
  match x with
  | [] => right; simp
  | a :: x =>
    left
    ext y
    simp

theorem isRegular_singleton_char (a : α) : ({[a]} : Language α).IsRegular := by
  refine isRegular_of_leftQuotient_mem (S := {0, 1, {[a]}}) (Set.toFinite _) fun x => ?_
  match x with
  | [] =>
    right; right
    ext y
    simp
  | b :: x =>
    by_cases hb : b = a
    · subst hb
      match x with
      | [] =>
        right; left
        ext y
        simp
      | c :: x =>
        left
        ext y
        simp
    · left
      ext y
      simp [hb]

/-- Left quotients of a concatenation. -/
theorem leftQuotient_mul (A B : Language α) (x : List α) :
    (A * B).leftQuotient x =
      (A.leftQuotient x) * B ⊔ sSup ((fun v => B.leftQuotient v) '' {v | ∃ u ∈ A, u ++ v = x}) := by
  ext y
  simp only [Language.mem_leftQuotient, Language.mem_mul, Set.mem_image, Set.mem_setOf_eq,
    mem_sup_language, mem_sSup_language]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · -- x = a ++ c, b = c ++ y
      right
      refine ⟨B.leftQuotient c, ⟨c, ⟨a, ha, hc1.symm⟩, rfl⟩, ?_⟩
      show c ++ y ∈ B
      exact hc2 ▸ hb
    · -- a = x ++ c, y = c ++ b
      left
      refine ⟨c, ?_, b, hb, hc2.symm⟩
      show x ++ c ∈ A
      exact hc1 ▸ ha
  · rintro (⟨c, hc, b, hb, rfl⟩ | ⟨L, ⟨v, ⟨u, hu, huv⟩, rfl⟩, hy⟩)
    · refine ⟨x ++ c, hc, b, hb, by simp⟩
    · refine ⟨u, hu, v ++ y, hy, ?_⟩
      rw [← huv]
      simp

theorem isRegular_mul {A B : Language α} (hA : A.IsRegular) (hB : B.IsRegular) :
    (A * B).IsRegular := by
  have hA' := hA.finite_range_leftQuotient
  have hB' := hB.finite_range_leftQuotient
  refine isRegular_of_leftQuotient_mem
    (S := (fun p : Language α × Set (Language α) => p.1 * B ⊔ sSup p.2) ''
      ((Set.range A.leftQuotient) ×ˢ {T | T ⊆ Set.range B.leftQuotient}))
    (Set.Finite.image _ (hA'.prod hB'.finite_subsets)) fun x => ?_
  refine ⟨(A.leftQuotient x, (fun v => B.leftQuotient v) '' {v | ∃ u ∈ A, u ++ v = x}),
    ⟨⟨x, rfl⟩, ?_⟩, (leftQuotient_mul A B x).symm⟩
  rintro _ ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

theorem cons_mem_kstar {A : Language α} {w c : List α} (hw : w ∈ A) (hc : c ∈ A∗) :
    w ++ c ∈ A∗ := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hc
  refine Language.mem_kstar.mpr ⟨w :: L, by simp, ?_⟩
  intro z hz
  rcases List.mem_cons.mp hz with rfl | hz
  · exact hw
  · exact hL z hz

theorem append_mem_kstar {A : Language α} {u v : List α} (hu : u ∈ A∗) (hv : v ∈ A∗) :
    u ++ v ∈ A∗ := by
  obtain ⟨L₁, rfl, hL₁⟩ := Language.mem_kstar.mp hu
  obtain ⟨L₂, rfl, hL₂⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨L₁ ++ L₂, by simp, ?_⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hL₁ z hz
  · exact hL₂ z hz

/-- Splitting a word of `A∗` at the position separating a prefix `x` from a suffix `y`. -/
theorem kstar_split {A : Language α} :
    ∀ (S : List (List α)) (x y : List α), (∀ w ∈ S, w ∈ A) → S.flatten = x ++ y →
      (x ∈ A∗ ∧ y ∈ A∗) ∨ ∃ v, (∃ u ∈ A∗, u ++ v = x) ∧ y ∈ (A.leftQuotient v) * A∗ := by
  intro S
  induction S with
  | nil =>
    intro x y _ h
    simp only [List.flatten_nil] at h
    obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm
    exact Or.inl ⟨Language.nil_mem_kstar _, Language.nil_mem_kstar _⟩
  | cons w ws ih =>
    intro x y hmem h
    rw [List.flatten_cons] at h
    have hw : w ∈ A := hmem w List.mem_cons_self
    have hws : ∀ z ∈ ws, z ∈ A := fun z hz => hmem z (List.mem_cons_of_mem _ hz)
    rcases List.append_eq_append_iff.mp h with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · rcases ih c y hws hc2 with ⟨hc, hy⟩ | ⟨v, ⟨u, hu, huv⟩, hy⟩
      · exact Or.inl ⟨hc1 ▸ cons_mem_kstar hw hc, hy⟩
      · refine Or.inr ⟨v, ⟨w ++ u, cons_mem_kstar hw hu, ?_⟩, hy⟩
        rw [hc1, ← huv, List.append_assoc]
    · refine Or.inr ⟨x, ⟨[], Language.nil_mem_kstar _, by simp⟩, ?_⟩
      refine Language.mem_mul.mpr ⟨c, ?_, ws.flatten, Language.join_mem_kstar hws, hc2.symm⟩
      show x ++ c ∈ A
      exact hc1 ▸ hw

/-- Left quotients of a Kleene star. -/
theorem leftQuotient_kstar (A : Language α) (x : List α) [Decidable (x ∈ A∗)] :
    (A∗).leftQuotient x =
      sSup ((fun v => A.leftQuotient v) '' {v | ∃ u ∈ A∗, u ++ v = x}) * A∗ ⊔
        (if x ∈ A∗ then A∗ else 0) := by
  ext y
  simp only [Language.mem_leftQuotient, mem_sup_language]
  constructor
  · intro hxy
    obtain ⟨S, hS, hSA⟩ := Language.mem_kstar.mp hxy
    rcases kstar_split S x y hSA hS.symm with ⟨hx, hy⟩ | ⟨v, ⟨u, hu, huv⟩, hy⟩
    · right
      rw [if_pos hx]
      exact hy
    · left
      obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp hy
      exact Language.mem_mul.mpr
        ⟨c, mem_sSup_language.mpr ⟨_, ⟨v, ⟨u, hu, huv⟩, rfl⟩, hc⟩, d, hd, rfl⟩
  · rintro (h | h)
    · obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨L, ⟨v, ⟨u, hu, huv⟩, rfl⟩, hcv⟩ := mem_sSup_language.mp hc
      have hvc : v ++ c ∈ A := hcv
      have : x ++ (c ++ d) = u ++ ((v ++ c) ++ d) := by
        rw [← huv]; simp
      rw [this]
      exact append_mem_kstar hu (cons_mem_kstar hvc hd)
    · by_cases hx : x ∈ A∗
      · rw [if_pos hx] at h
        exact append_mem_kstar hx h
      · rw [if_neg hx] at h
        exact absurd h (Language.notMem_zero y)

theorem isRegular_kstar {A : Language α} (hA : A.IsRegular) : (A∗).IsRegular := by
  classical
  have hA' := hA.finite_range_leftQuotient
  refine isRegular_of_leftQuotient_mem
    (S := (fun p : Set (Language α) × Language α => sSup p.1 * A∗ ⊔ p.2) ''
      ({T | T ⊆ Set.range A.leftQuotient} ×ˢ ({0, A∗} : Set (Language α))))
    (Set.Finite.image _ (hA'.finite_subsets.prod (Set.toFinite _))) fun x => ?_
  refine ⟨((fun v => A.leftQuotient v) '' {v | ∃ u ∈ A∗, u ++ v = x},
    if x ∈ A∗ then A∗ else 0), ⟨?_, ?_⟩, (leftQuotient_kstar A x).symm⟩
  · rintro _ ⟨v, -, rfl⟩
    exact ⟨v, rfl⟩
  · by_cases hx : x ∈ A∗ <;> simp [hx]

theorem isRegular_matches' (r : RegularExpression α) : r.matches'.IsRegular := by
  induction r with
  | zero => simpa using isRegular_zero
  | epsilon => simpa using isRegular_one
  | char a => simpa using isRegular_singleton_char a
  | plus P Q hP hQ => simpa using Language.IsRegular.add hP hQ
  | comp P Q hP hQ => simpa using isRegular_mul hP hQ
  | star P hP => simpa using isRegular_kstar hP

end RegexToDFA

/-! ## Part 2: the language of a DFA over a finite alphabet is given by a regular expression -/

section DFAToRegex

variable {σ : Type*}

/-- `PathIn M l s t x` says that reading `x` from state `s` ends in state `t`, and that every
intermediate state visited on the way (excluding the endpoints `s` and `t`) lies in `l`. -/
def PathIn (M : DFA α σ) (l : List σ) : σ → σ → List α → Prop
  | s, t, [] => s = t
  | s, t, (a :: x) => (M.step s a = t ∧ x = []) ∨ (M.step s a ∈ l ∧ PathIn M l (M.step s a) t x)

/-- The language of words labelling a path from `s` to `t` with intermediate states in `l`. -/
def pathLang (M : DFA α σ) (l : List σ) (s t : σ) : Language α := {x | PathIn M l s t x}

variable (M : DFA α σ)

@[simp] theorem pathIn_nil_word (l : List σ) (s t : σ) : PathIn M l s t [] ↔ s = t := Iff.rfl

@[simp] theorem pathIn_cons_word (l : List σ) (s t : σ) (a : α) (x : List α) :
    PathIn M l s t (a :: x) ↔
      (M.step s a = t ∧ x = []) ∨ (M.step s a ∈ l ∧ PathIn M l (M.step s a) t x) := Iff.rfl

@[simp] theorem mem_pathLang {l : List σ} {s t : σ} {x : List α} :
    x ∈ pathLang M l s t ↔ PathIn M l s t x := Iff.rfl

theorem pathIn_mono {l l' : List σ} (hl : ∀ q ∈ l, q ∈ l') :
    ∀ (x : List α) (s t : σ), PathIn M l s t x → PathIn M l' s t x := by
  intro x
  induction x with
  | nil => intro s t h; exact h
  | cons a x ih =>
    rintro s t (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨hl _ h1, ih _ _ h2⟩

theorem pathIn_all {l : List σ} (hl : ∀ q : σ, q ∈ l) (x : List α) (s t : σ) :
    PathIn M l s t x ↔ M.evalFrom s x = t := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih =>
    rw [pathIn_cons_word, DFA.evalFrom_cons, ← ih (M.step s a)]
    constructor
    · rintro (⟨h1, rfl⟩ | ⟨-, h2⟩)
      · exact h1
      · exact h2
    · intro h
      exact Or.inr ⟨hl _, h⟩

theorem pathIn_append {l : List σ} {u : σ} (hu : u ∈ l) :
    ∀ (x : List α) (s : σ) (y : List α) (t : σ),
      PathIn M l s u x → PathIn M l u t y → PathIn M l s t (x ++ y) := by
  intro x
  induction x with
  | nil =>
    intro s y t hx hy
    obtain rfl : s = u := hx
    simpa using hy
  | cons a x ih =>
    rintro s y t (⟨h1, rfl⟩ | ⟨h1, h2⟩) hy
    · refine Or.inr ⟨h1 ▸ hu, ?_⟩
      simpa [h1] using hy
    · exact Or.inr ⟨h1, ih _ y t h2 hy⟩

theorem pathIn_of_kstar {l : List σ} {q : σ} (hq : q ∈ l) {x : List α}
    (hx : x ∈ (pathLang M l q q)∗) : PathIn M l q q x := by
  obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hx
  clear hx
  induction L with
  | nil => simp
  | cons w ws ih =>
    rw [List.flatten_cons]
    exact pathIn_append M hq w q ws.flatten q (hL w List.mem_cons_self)
      (ih fun z hz => hL z (List.mem_cons_of_mem _ hz))

/-- Splitting a path off at its first visit to `q`. -/
theorem pathIn_split {l : List σ} {q : σ} :
    ∀ (x : List α) (s t : σ), PathIn M (q :: l) s t x →
      PathIn M l s t x ∨
        ∃ y z, x = y ++ z ∧ y ≠ [] ∧ PathIn M l s q y ∧ PathIn M (q :: l) q t z := by
  intro x
  induction x with
  | nil => intro s t h; exact Or.inl h
  | cons a x ih =>
    rintro s t (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · by_cases hq : M.step s a = q
      · refine Or.inr ⟨[a], x, rfl, by simp, ?_, ?_⟩
        · exact Or.inl ⟨hq, rfl⟩
        · rw [hq] at h2
          exact h2
      · have hml : M.step s a ∈ l := by
          rcases List.mem_cons.mp h1 with h | h
          · exact absurd h hq
          · exact h
        rcases ih (M.step s a) t h2 with h | ⟨y, z, rfl, hy, hyq, hz⟩
        · exact Or.inl (Or.inr ⟨hml, h⟩)
        · exact Or.inr ⟨a :: y, z, rfl, by simp, Or.inr ⟨hml, hyq⟩, hz⟩

private theorem pathIn_from_head_aux {l : List σ} {q : σ} :
    ∀ (n : ℕ) (x : List α) (t : σ), x.length ≤ n → PathIn M (q :: l) q t x →
      x ∈ (pathLang M l q q)∗ * pathLang M l q t := by
  intro n
  induction n with
  | zero =>
    intro x t hlen hx
    obtain rfl : x = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, [], hx, rfl⟩
  | succ n ih =>
    intro x t hlen hx
    rcases pathIn_split M x q t hx with h | ⟨y, z, rfl, hy, hyq, hz⟩
    · exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, x, h, rfl⟩
    · have hzlen : z.length ≤ n := by
        have hy' : 1 ≤ y.length := by
          cases y with
          | nil => exact absurd rfl hy
          | cons _ _ => simp
        have : y.length + z.length ≤ n + 1 := by simpa using hlen
        omega
      obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp (ih z t hzlen hz)
      refine Language.mem_mul.mpr ⟨y ++ c, cons_mem_kstar hyq hc, d, hd, ?_⟩
      simp

theorem pathIn_from_head {l : List σ} {q t : σ} {x : List α} (hx : PathIn M (q :: l) q t x) :
    x ∈ (pathLang M l q q)∗ * pathLang M l q t :=
  pathIn_from_head_aux M x.length x t le_rfl hx

/-- The state elimination step of Kleene's algorithm. -/
theorem pathLang_cons (l : List σ) (q s t : σ) :
    pathLang M (q :: l) s t =
      pathLang M l s t + pathLang M l s q * (pathLang M l q q)∗ * pathLang M l q t := by
  have hq : q ∈ q :: l := List.mem_cons_self
  have hsub : ∀ p ∈ l, p ∈ q :: l := fun p hp => List.mem_cons_of_mem _ hp
  ext x
  rw [Language.mem_add]
  simp only [mem_pathLang]
  constructor
  · intro h
    rcases pathIn_split M x s t h with h | ⟨y, z, rfl, -, hyq, hz⟩
    · exact Or.inl h
    · right
      obtain ⟨c, hc, d, hd, rfl⟩ := Language.mem_mul.mp (pathIn_from_head M hz)
      exact Language.mem_mul.mpr ⟨y ++ c, Language.mem_mul.mpr ⟨y, hyq, c, hc, rfl⟩, d, hd, by simp⟩
  · rintro (h | h)
    · exact pathIn_mono M hsub x s t h
    · obtain ⟨e, he, d, hd, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨y, hy, c, hc, rfl⟩ := Language.mem_mul.mp he
      have h1 : PathIn M (q :: l) s q y := pathIn_mono M hsub y s q hy
      have h2 : PathIn M (q :: l) q q c := by
        obtain ⟨L, rfl, hL⟩ := Language.mem_kstar.mp hc
        refine pathIn_of_kstar M hq (Language.join_mem_kstar fun z hz => ?_)
        exact pathIn_mono M hsub z q q (hL z hz)
      have h3 : PathIn M (q :: l) q t d := pathIn_mono M hsub d q t hd
      exact pathIn_append M hq (y ++ c) s d t (pathIn_append M hq y s c q h1 h2) h3

/-! ### Building the regular expression -/

/-- A regular expression matching exactly the one-letter words `[a]` for `a ∈ l`. -/
def letterRegex (l : List α) : RegularExpression α :=
  l.foldr (fun a r => RegularExpression.char a + r) 0

theorem mem_matches'_letterRegex (l : List α) (x : List α) :
    x ∈ (letterRegex l).matches' ↔ ∃ a ∈ l, x = [a] := by
  induction l with
  | nil =>
    rw [letterRegex, List.foldr_nil, RegularExpression.matches'_zero]
    simp
  | cons a l ih =>
    have hcons : letterRegex (a :: l) = RegularExpression.char a + letterRegex l := rfl
    rw [hcons, RegularExpression.matches'_add, RegularExpression.matches'_char,
      mem_add_language, ih]
    simp

/-- A finite union of regular expressions indexed by a list. -/
def unionRegex (f : σ → RegularExpression α) (l : List σ) : RegularExpression α :=
  l.foldr (fun q r => f q + r) 0

theorem mem_matches'_unionRegex (f : σ → RegularExpression α) (l : List σ) (x : List α) :
    x ∈ (unionRegex f l).matches' ↔ ∃ q ∈ l, x ∈ (f q).matches' := by
  induction l with
  | nil =>
    rw [unionRegex, List.foldr_nil, RegularExpression.matches'_zero]
    simp
  | cons q l ih =>
    have hcons : unionRegex f (q :: l) = f q + unionRegex f l := rfl
    rw [hcons, RegularExpression.matches'_add, mem_add_language, ih]
    simp

variable [Fintype α] [DecidableEq σ]

/-- The regular expression for paths with no intermediate states. -/
noncomputable def baseRegex (s t : σ) : RegularExpression α :=
  (if s = t then 1 else 0) +
    letterRegex ((Finset.univ.filter (fun a : α => M.step s a = t)).toList)

theorem matches'_baseRegex (s t : σ) : (baseRegex M s t).matches' = pathLang M [] s t := by
  ext x
  have hif : ((if s = t then 1 else 0 : RegularExpression α)).matches' =
      if s = t then (1 : Language α) else 0 := by
    by_cases hst : s = t <;> simp [hst]
  rw [baseRegex, RegularExpression.matches'_add, mem_add_language, hif,
    mem_matches'_letterRegex]
  simp only [mem_pathLang, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · by_cases hst : s = t
      · rw [if_pos hst] at h
        obtain rfl : x = [] := h
        exact hst
      · rw [if_neg hst] at h
        exact absurd h (Language.notMem_zero x)
    · exact Or.inl ⟨ha, rfl⟩
  · intro h
    match x with
    | [] =>
      left
      obtain rfl : s = t := h
      simp
    | b :: y =>
      rcases h with ⟨h1, rfl⟩ | ⟨h1, -⟩
      · exact Or.inr ⟨b, h1, rfl⟩
      · exact absurd h1 (by simp)

/-- Kleene's algorithm: the regular expression for paths from `s` to `t` whose intermediate
states all lie in `l`. -/
noncomputable def pathRegex : List σ → σ → σ → RegularExpression α
  | [], s, t => baseRegex M s t
  | q :: qs, s, t =>
      pathRegex qs s t + pathRegex qs s q * (pathRegex qs q q).star * pathRegex qs q t

theorem matches'_pathRegex : ∀ (l : List σ) (s t : σ),
    (pathRegex M l s t).matches' = pathLang M l s t := by
  intro l
  induction l with
  | nil =>
    intro s t
    rw [pathRegex, matches'_baseRegex]
  | cons q qs ih =>
    intro s t
    rw [pathRegex, RegularExpression.matches'_add, RegularExpression.matches'_mul,
      RegularExpression.matches'_mul, RegularExpression.matches'_star, ih, ih, ih, ih,
      pathLang_cons]

/-- Every DFA over a finite alphabet with finitely many states has its language described by a
regular expression. -/
theorem exists_regex_of_dfa [Fintype σ] :
    ∃ r : RegularExpression α, r.matches' = M.accepts := by
  classical
  have hall : ∀ q : σ, q ∈ (Finset.univ : Finset σ).toList := fun q =>
    Finset.mem_toList.mpr (Finset.mem_univ q)
  refine ⟨unionRegex (fun t => pathRegex M (Finset.univ : Finset σ).toList M.start t)
      ((Finset.univ.filter (fun t : σ => t ∈ M.accept)).toList), ?_⟩
  ext x
  rw [mem_matches'_unionRegex]
  simp only [matches'_pathRegex, mem_pathLang, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hp⟩
    have hx : M.evalFrom M.start x = t := (pathIn_all M hall x M.start t).mp hp
    show M.eval x ∈ M.accept
    rw [DFA.eval, hx]
    exact ht
  · intro hx
    have hx' : M.eval x ∈ M.accept := hx
    exact ⟨M.eval x, hx', (pathIn_all M hall x M.start (M.eval x)).mpr rfl⟩

end DFAToRegex

/-- **Kleene's theorem.** Over a finite alphabet, a language is denoted by a regular expression
if and only if it is accepted by a deterministic finite automaton with finitely many states. -/
theorem kleene_regex_dfa {α : Type} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔
      ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), M.accepts = L := by
  classical
  constructor
  · rintro ⟨r, rfl⟩
    exact isRegular_matches' r
  · rintro ⟨σ, _, M, rfl⟩
    exact exists_regex_of_dfa M

/-- Restatement of Kleene's theorem using Mathlib's `Language.IsRegular`. -/
theorem kleene_regex_isRegular {α : Type} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔ L.IsRegular :=
  kleene_regex_dfa L

end CS

#print axioms CS.kleene_regex_dfa
#print axioms CS.kleene_regex_isRegular

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

