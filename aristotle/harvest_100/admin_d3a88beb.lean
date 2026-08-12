import Mathlib

/-!
# From DFAs to regular expressions

This file implements Kleene's algorithm: given a DFA with finitely many states over a finite
alphabet, we construct a regular expression matching exactly the language it accepts.

The construction proceeds by recursion on a list `l` of "allowed intermediate states":
`kleeneRegex M l p q` matches exactly the words labelling a path from `p` to `q` all of whose
intermediate states belong to `l`.
-/

universe u v

open scoped Computability

namespace CS

variable {α : Type u} {σ : Type v}

/-! ### Paths with restricted intermediate states -/

/-- `PathVia M S p q w` means that reading `w` takes the DFA `M` from state `p` to state `q`,
in such a way that every *intermediate* state (i.e. every state visited strictly between the
start and the end of the run) lies in `S`. -/
inductive PathVia (M : DFA α σ) (S : Set σ) : σ → σ → List α → Prop
  | nil (p : σ) : PathVia M S p p []
  | cons {p q : σ} (a : α) {w : List α} (h : PathVia M S (M.step p a) q w)
      (hm : w ≠ [] → M.step p a ∈ S) : PathVia M S p q (a :: w)

/-- The language of words labelling paths from `p` to `q` with intermediate states in `S`. -/
def pathLang (M : DFA α σ) (S : Set σ) (p q : σ) : Language α := {w | PathVia M S p q w}

theorem mem_pathLang {M : DFA α σ} {S : Set σ} {p q : σ} {w : List α} :
    w ∈ pathLang M S p q ↔ PathVia M S p q w := Iff.rfl

theorem PathVia.nil_iff {M : DFA α σ} {S : Set σ} {p q : σ} :
    PathVia M S p q [] ↔ p = q := by
  constructor
  · intro h; cases h; rfl
  · rintro rfl; exact PathVia.nil p

theorem PathVia.evalFrom {M : DFA α σ} {S : Set σ} {p q : σ} {w : List α}
    (h : PathVia M S p q w) : M.evalFrom p w = q := by
  induction h with
  | nil p => rfl
  | cons a _ _ ih => simpa using ih

theorem pathVia_univ {M : DFA α σ} {p q : σ} {w : List α} (h : M.evalFrom p w = q) :
    PathVia M Set.univ p q w := by
  induction w generalizing p with
  | nil => simpa [PathVia.nil_iff] using h
  | cons a w ih =>
      refine PathVia.cons a (ih (by simpa using h)) (fun _ => Set.mem_univ _)

theorem PathVia.mono {M : DFA α σ} {S T : Set σ} (hST : S ⊆ T) {p q : σ} {w : List α}
    (h : PathVia M S p q w) : PathVia M T p q w := by
  induction h with
  | nil p => exact PathVia.nil p
  | cons a _ hm ih => exact PathVia.cons a ih (fun hw => hST (hm hw))

theorem PathVia.append {M : DFA α σ} {S : Set σ} {p r q : σ} {w₁ w₂ : List α}
    (h₁ : PathVia M S p r w₁) : r ∈ S → PathVia M S r q w₂ → PathVia M S p q (w₁ ++ w₂) := by
  induction h₁ with
  | nil p => intro _ h₂; simpa using h₂
  | cons a h hm ih =>
      rename_i w
      intro hr h₂
      refine PathVia.cons a (ih hr h₂) ?_
      intro _
      rcases eq_or_ne w [] with rfl | hw
      · rw [PathVia.nil_iff.mp h]
        exact hr
      · exact hm hw

/-! ### The key decomposition lemma -/

theorem PathVia.split_first {M : DFA α σ} {S : Set σ} {s : σ} {p q : σ} {w : List α}
    (h : PathVia M (insert s S) p q w) :
    PathVia M S p q w ∨ ∃ w₁ w₂, w = w₁ ++ w₂ ∧ w₁ ≠ [] ∧ PathVia M S p s w₁ ∧
      PathVia M (insert s S) s q w₂ := by
  induction h with
  | nil p => exact Or.inl (PathVia.nil p)
  | cons a h hm ih =>
      rename_i p q w
      rcases eq_or_ne w [] with rfl | hw
      · exact Or.inl (PathVia.cons a (PathVia.nil_iff.mpr (PathVia.nil_iff.mp h)) (by simp))
      · rcases Set.mem_insert_iff.mp (hm hw) with hst | hst
        · refine Or.inr ⟨[a], w, by simp, by simp, ?_, hst ▸ h⟩
          exact PathVia.cons a (PathVia.nil_iff.mpr hst) (by simp)
        · rcases ih with hih | ⟨w₁, w₂, rfl, hw₁, hp, hq⟩
          · exact Or.inl (PathVia.cons a hih (fun _ => hst))
          · refine Or.inr ⟨a :: w₁, w₂, by simp, by simp, ?_, hq⟩
            exact PathVia.cons a hp (fun _ => hst)

theorem PathVia.of_mem_kstar {M : DFA α σ} {S : Set σ} {s : σ} {u : List α}
    (hu : u ∈ (pathLang M S s s)∗) : PathVia M (insert s S) s s u := by
  rw [Language.mem_kstar] at hu
  obtain ⟨L, rfl, hL⟩ := hu
  induction L with
  | nil => exact PathVia.nil s
  | cons w L ih =>
      have hw : PathVia M S s s w := hL w (by simp)
      have hrest : PathVia M (insert s S) s s L.flatten :=
        ih (fun z hz => hL z (by simp [hz]))
      simpa using PathVia.append (hw.mono (Set.subset_insert s S)) (Set.mem_insert s S) hrest

theorem mem_kstar_mul_of_pathVia {M : DFA α σ} {S : Set σ} {s q : σ} :
    ∀ (w : List α), PathVia M (insert s S) s q w →
      w ∈ (pathLang M S s s)∗ * pathLang M S s q := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | _ n ih =>
    intro h
    subst hn
    rcases PathVia.split_first h with hl | ⟨w₁, w₂, rfl, hw₁, hp, hq⟩
    · exact Language.append_mem_mul (Language.nil_mem_kstar _) hl
    · have hlt : w₂.length < (w₁ ++ w₂).length := by
        have : 0 < w₁.length := List.length_pos_iff.mpr hw₁
        simp only [List.length_append]
        omega
      obtain ⟨u, hu, v, hv, rfl⟩ :=
        Language.mem_mul.mp (ih w₂.length hlt w₂ rfl hq)
      refine ⟨w₁ ++ u, ?_, v, hv, by simp⟩
      rw [Language.mem_kstar] at hu ⊢
      obtain ⟨L, rfl, hL⟩ := hu
      refine ⟨w₁ :: L, by simp, ?_⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hp
      · exact hL z hz

/-- Kleene's decomposition: paths that may additionally pass through `s` are obtained from
paths avoiding `s` by splitting at the first and last visits to `s`. -/
theorem pathLang_insert (M : DFA α σ) (S : Set σ) (s p q : σ) :
    pathLang M (insert s S) p q =
      pathLang M S p q + pathLang M S p s * (pathLang M S s s)∗ * pathLang M S s q := by
  ext w
  rw [Language.mem_add]
  constructor
  · intro h
    rcases PathVia.split_first (mem_pathLang.mp h) with hl | ⟨w₁, w₂, rfl, _, hp, hq⟩
    · exact Or.inl hl
    · right
      obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp (mem_kstar_mul_of_pathVia w₂ hq)
      rw [mul_assoc]
      exact Language.append_mem_mul hp (Language.append_mem_mul hu hv)
  · rintro (h | h)
    · exact (mem_pathLang.mp h).mono (Set.subset_insert s S)
    · rw [mul_assoc] at h
      obtain ⟨w₁, h₁, x, hx, rfl⟩ := Language.mem_mul.mp h
      obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hx
      have h₁' : PathVia M (insert s S) p s w₁ :=
        (mem_pathLang.mp h₁).mono (Set.subset_insert s S)
      have hu' : PathVia M (insert s S) s s u := PathVia.of_mem_kstar hu
      have hv' : PathVia M (insert s S) s q v :=
        (mem_pathLang.mp hv).mono (Set.subset_insert s S)
      exact h₁'.append (Set.mem_insert s S) (hu'.append (Set.mem_insert s S) hv')

theorem mem_pathLang_empty {M : DFA α σ} {p q : σ} {w : List α} :
    PathVia M ∅ p q w ↔ (w = [] ∧ p = q) ∨ ∃ a, w = [a] ∧ M.step p a = q := by
  constructor
  · intro h
    cases h with
    | nil p => exact Or.inl ⟨rfl, rfl⟩
    | cons a h hm =>
        rename_i w
        rcases eq_or_ne w [] with rfl | hw
        · exact Or.inr ⟨a, rfl, PathVia.nil_iff.mp h⟩
        · exact absurd (hm hw) (Set.notMem_empty _)
  · rintro (⟨rfl, rfl⟩ | ⟨a, rfl, ha⟩)
    · exact PathVia.nil p
    · exact PathVia.cons a (PathVia.nil_iff.mpr ha) (by simp)

/-! ### Sums of regular expressions -/

/-- The sum of a list of regular expressions. -/
def sumRegex : List (RegularExpression α) → RegularExpression α :=
  List.foldr (· + ·) 0

@[simp] theorem sumRegex_nil : sumRegex ([] : List (RegularExpression α)) = 0 := rfl

@[simp] theorem sumRegex_cons (r : RegularExpression α) (l : List (RegularExpression α)) :
    sumRegex (r :: l) = r + sumRegex l := rfl

theorem mem_matches'_sumRegex {l : List (RegularExpression α)} {w : List α} :
    w ∈ (sumRegex l).matches' ↔ ∃ r ∈ l, w ∈ r.matches' := by
  induction l with
  | nil => simp [RegularExpression.matches'_zero, Language.notMem_zero]
  | cons r l ih =>
      rw [sumRegex_cons, RegularExpression.matches'_add, Language.mem_add, ih]
      constructor
      · rintro (h | ⟨t, ht, h⟩)
        · exact ⟨r, by simp, h⟩
        · exact ⟨t, by simp [ht], h⟩
      · rintro ⟨t, ht, h⟩
        rcases List.mem_cons.mp ht with rfl | ht
        · exact Or.inl h
        · exact Or.inr ⟨t, ht, h⟩

/-! ### Kleene's algorithm -/

variable [Fintype α] [DecidableEq σ]

/-- The regular expression matching all single letters taking `p` to `q`. -/
noncomputable def stepRegex (M : DFA α σ) (p q : σ) : RegularExpression α :=
  sumRegex ((Finset.univ : Finset α).toList.map
    (fun a => if M.step p a = q then RegularExpression.char a else 0))

theorem matches'_stepRegex (M : DFA α σ) (p q : σ) :
    (stepRegex M p q).matches' = {w : List α | ∃ a, w = [a] ∧ M.step p a = q} := by
  ext w
  rw [stepRegex, mem_matches'_sumRegex]
  constructor
  · rintro ⟨r, hr, hw⟩
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hr
    by_cases h : M.step p a = q
    · rw [if_pos h, RegularExpression.matches'_char] at hw
      exact ⟨a, Set.mem_singleton_iff.mp hw, h⟩
    · rw [if_neg h, RegularExpression.matches'_zero] at hw
      exact absurd hw (Language.notMem_zero _)
  · rintro ⟨a, rfl, ha⟩
    refine ⟨if M.step p a = q then RegularExpression.char a else 0,
      List.mem_map.mpr ⟨a, by simp, rfl⟩, ?_⟩
    rw [if_pos ha, RegularExpression.matches'_char]
    rfl

/-- Kleene's algorithm: `kleeneRegex M l p q` matches the words taking `M` from `p` to `q`
with all intermediate states in `l`. -/
noncomputable def kleeneRegex (M : DFA α σ) : List σ → σ → σ → RegularExpression α
  | [], p, q => (if p = q then 1 else 0) + stepRegex M p q
  | s :: l, p, q =>
      kleeneRegex M l p q +
        kleeneRegex M l p s * (kleeneRegex M l s s).star * kleeneRegex M l s q

theorem matches'_kleeneRegex (M : DFA α σ) :
    ∀ (l : List σ) (p q : σ), (kleeneRegex M l p q).matches' = pathLang M {x | x ∈ l} p q := by
  intro l
  induction l with
  | nil =>
      intro p q
      have hset : {x : σ | x ∈ ([] : List σ)} = (∅ : Set σ) := by ext x; simp
      rw [hset, kleeneRegex, RegularExpression.matches'_add, matches'_stepRegex]
      ext w
      rw [Language.mem_add, mem_pathLang, mem_pathLang_empty]
      constructor
      · rintro (h | h)
        · by_cases hpq : p = q
          · subst hpq
            rw [if_pos rfl] at h
            exact Or.inl ⟨Language.mem_one w |>.mp h, rfl⟩
          · rw [if_neg hpq] at h
            exact absurd h (Language.notMem_zero _)
        · exact Or.inr h
      · rintro (⟨rfl, rfl⟩ | h)
        · exact Or.inl (by rw [if_pos rfl]; exact Language.nil_mem_one)
        · exact Or.inr h
  | cons s l ih =>
      intro p q
      have hset : {x : σ | x ∈ s :: l} = insert s {x : σ | x ∈ l} := by
        ext x; simp [Set.mem_insert_iff]
      rw [kleeneRegex, RegularExpression.matches'_add, RegularExpression.matches'_mul,
        RegularExpression.matches'_mul, RegularExpression.matches'_star, ih, ih, ih, ih, hset,
        pathLang_insert]

/-- Every language accepted by a DFA with finitely many states over a finite alphabet is
matched by a regular expression. -/
theorem exists_regularExpression_of_dfa [Fintype σ] (M : DFA α σ) :
    ∃ R : RegularExpression α, R.matches' = M.accepts := by
  classical
  refine ⟨sumRegex ((Finset.univ : Finset σ).toList.map
    (fun q => if q ∈ M.accept then kleeneRegex M (Finset.univ : Finset σ).toList M.start q
      else 0)), ?_⟩
  have huniv : {x : σ | x ∈ (Finset.univ : Finset σ).toList} = (Set.univ : Set σ) := by
    ext x; simp
  ext w
  rw [mem_matches'_sumRegex, DFA.mem_accepts, DFA.eval]
  constructor
  · rintro ⟨r, hr, hw⟩
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hr
    by_cases hq : q ∈ M.accept
    · rw [if_pos hq, matches'_kleeneRegex, huniv] at hw
      rw [(mem_pathLang.mp hw).evalFrom]
      exact hq
    · rw [if_neg hq, RegularExpression.matches'_zero] at hw
      exact absurd hw (Language.notMem_zero _)
  · intro hw
    refine ⟨if M.evalFrom M.start w ∈ M.accept then
      kleeneRegex M (Finset.univ : Finset σ).toList M.start (M.evalFrom M.start w) else 0,
      List.mem_map.mpr ⟨M.evalFrom M.start w, by simp, rfl⟩, ?_⟩
    rw [if_pos hw, matches'_kleeneRegex, huniv]
    exact pathVia_univ rfl

end CS

import Mathlib

/-!
# Finite derivative families and regularity

This file develops an "Antimirov style" argument showing that every language matched by a
regular expression is regular (i.e. accepted by a DFA): we exhibit, for each regular expression,
a finite family of languages containing its language and closed under taking left quotients by
single letters.  Combined with the Myhill–Nerode theorem in Mathlib this gives regularity.
-/

universe u

open scoped Computability

attribute [local instance] Classical.propDecidable

namespace CS

variable {α : Type u}

/-! ### Basic facts about suprema of families of languages -/

theorem mem_sSup_language {B : Set (Language α)} {y : List α} : y ∈ sSup B ↔ ∃ L ∈ B, y ∈ L := by
  constructor
  · rintro ⟨L, hL, hy⟩; exact ⟨L, hL, hy⟩
  · rintro ⟨L, hL, hy⟩; exact ⟨L, hL, hy⟩

theorem sSup_empty_language : sSup (∅ : Set (Language α)) = 0 := by
  ext y
  exact iff_of_false (fun h => by simpa using h) (Language.notMem_zero _)

theorem sSup_union_language (B C : Set (Language α)) : sSup (B ∪ C) = sSup B + sSup C := by
  ext y
  rw [mem_sSup_language, Language.mem_add, mem_sSup_language, mem_sSup_language]
  constructor
  · rintro ⟨L, (hL | hL), hy⟩
    exacts [Or.inl ⟨L, hL, hy⟩, Or.inr ⟨L, hL, hy⟩]
  · rintro (⟨L, hL, hy⟩ | ⟨L, hL, hy⟩)
    exacts [⟨L, Or.inl hL, hy⟩, ⟨L, Or.inr hL, hy⟩]

theorem sSup_mul_language (B : Set (Language α)) (M : Language α) :
    sSup B * M = sSup ((fun L : Language α => L * M) '' B) := by
  ext y
  rw [Language.mem_mul, mem_sSup_language]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨L, hL, hu⟩ := mem_sSup_language.mp hu
    exact ⟨L * M, ⟨L, hL, rfl⟩, Language.append_mem_mul hu hv⟩
  · rintro ⟨_, ⟨L, hL, rfl⟩, hy⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Language.mem_mul.mp hy
    exact ⟨u, mem_sSup_language.mpr ⟨L, hL, hu⟩, v, hv, rfl⟩

/-! ### Single-letter left quotients -/

theorem leftQuotient_zero (a : α) : (0 : Language α).leftQuotient [a] = 0 := by
  ext y
  rw [Language.mem_leftQuotient]
  exact iff_of_false (Language.notMem_zero _) (Language.notMem_zero _)

theorem leftQuotient_one (a : α) : (1 : Language α).leftQuotient [a] = 0 := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_one]
  exact iff_of_false (by simp) (Language.notMem_zero _)

theorem leftQuotient_singleton (a c : α) :
    ({[c]} : Language α).leftQuotient [a] = if a = c then 1 else 0 := by
  ext y
  rw [Language.mem_leftQuotient]
  by_cases h : a = c
  · subst h
    rw [if_pos rfl, Language.mem_one]
    constructor
    · intro hy
      have : a :: y = [a] := Set.mem_singleton_iff.mp hy
      simpa using this
    · rintro rfl
      rfl
  · rw [if_neg h]
    refine iff_of_false ?_ (Language.notMem_zero _)
    intro hy
    have : a :: y = [c] := Set.mem_singleton_iff.mp hy
    exact h (by simpa using congrArg (fun l => l.head?) this)

theorem leftQuotient_add (A B : Language α) (a : α) :
    (A + B).leftQuotient [a] = A.leftQuotient [a] + B.leftQuotient [a] := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_add, Language.mem_add,
    Language.mem_leftQuotient, Language.mem_leftQuotient]

theorem leftQuotient_sSup (B : Set (Language α)) (a : α) :
    (sSup B).leftQuotient [a] = sSup ((fun L : Language α => L.leftQuotient [a]) '' B) := by
  ext y
  rw [Language.mem_leftQuotient, mem_sSup_language, mem_sSup_language]
  constructor
  · rintro ⟨L, hL, hy⟩
    exact ⟨L.leftQuotient [a], ⟨L, hL, rfl⟩, by rw [Language.mem_leftQuotient]; exact hy⟩
  · rintro ⟨_, ⟨L, hL, rfl⟩, hy⟩
    rw [Language.mem_leftQuotient] at hy
    exact ⟨L, hL, hy⟩

theorem leftQuotient_mul (A B : Language α) (a : α) :
    (A * B).leftQuotient [a] =
      A.leftQuotient [a] * B + (if [] ∈ A then B.leftQuotient [a] else 0) := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_add, Language.mem_mul, Language.mem_mul]
  constructor
  · rintro ⟨u, hu, v, hv, huv⟩
    cases u with
    | nil =>
        simp only [List.nil_append] at huv
        subst huv
        right
        rw [if_pos hu, Language.mem_leftQuotient]
        exact hv
    | cons b u =>
        rw [List.cons_append] at huv
        obtain ⟨rfl, rfl⟩ : b = a ∧ u ++ v = y := by simpa using huv
        exact Or.inl ⟨u, by rw [Language.mem_leftQuotient]; exact hu, v, hv, rfl⟩
  · rintro (⟨u, hu, v, hv, rfl⟩ | h)
    · rw [Language.mem_leftQuotient] at hu
      exact ⟨a :: u, hu, v, hv, by simp⟩
    · by_cases hA : [] ∈ A
      · rw [if_pos hA, Language.mem_leftQuotient] at h
        exact ⟨[], hA, a :: y, h, by simp⟩
      · rw [if_neg hA] at h
        exact absurd h (Language.notMem_zero _)

theorem leftQuotient_kstar (A : Language α) (a : α) :
    (A∗).leftQuotient [a] = A.leftQuotient [a] * A∗ := by
  ext y
  rw [Language.mem_leftQuotient, Language.mem_mul]
  constructor
  · intro h
    rw [Language.kstar_def_nonempty] at h
    obtain ⟨L, hL, hmem⟩ := h
    cases L with
    | nil => simp at hL
    | cons w L =>
        obtain ⟨hw, hwne⟩ := hmem w (by simp)
        cases w with
        | nil => exact absurd rfl hwne
        | cons b w =>
            simp only [List.flatten_cons, List.cons_append] at hL
            obtain ⟨rfl, hy⟩ : b = a ∧ w ++ L.flatten = y := by simpa using hL.symm
            refine ⟨w, by rw [Language.mem_leftQuotient]; exact hw, L.flatten, ?_, hy⟩
            exact Language.join_mem_kstar (fun z hz => (hmem z (by simp [hz])).1)
  · rintro ⟨u, hu, v, hv, rfl⟩
    rw [Language.mem_leftQuotient] at hu
    rw [Language.mem_kstar] at hv ⊢
    obtain ⟨L, rfl, hL⟩ := hv
    refine ⟨(a :: u) :: L, by simp, ?_⟩
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hu
    · exact hL z hz

/-! ### Finite derivative families -/

/-- A family `F` of languages is *derivative closed* if it is closed under taking the left
quotient by a single letter. -/
def DerivClosed (F : Set (Language α)) : Prop :=
  ∀ L ∈ F, ∀ a : α, L.leftQuotient [a] ∈ F

/-- A language *has a finite derivative family* if it belongs to some finite derivative-closed
family of languages. -/
def HasFinDeriv (L : Language α) : Prop :=
  ∃ F : Set (Language α), F.Finite ∧ DerivClosed F ∧ L ∈ F

theorem leftQuotient_mem_of_derivClosed {F : Set (Language α)} (hc : DerivClosed F) :
    ∀ (x : List α) (L : Language α), L ∈ F → L.leftQuotient x ∈ F := by
  intro x
  induction x with
  | nil => intro L hL; simpa using hL
  | cons a x ih =>
      intro L hL
      have hx : L.leftQuotient (a :: x) = (L.leftQuotient [a]).leftQuotient x := by
        rw [← Language.leftQuotient_append]
        rfl
      rw [hx]
      exact ih _ (hc L hL a)

/-- A language lying in a finite derivative-closed family is regular. -/
theorem isRegular_of_hasFinDeriv {L : Language α} (h : HasFinDeriv L) : L.IsRegular := by
  obtain ⟨F, hFin, hc, hL⟩ := h
  apply Language.IsRegular.of_finite_range_leftQuotient
  apply hFin.subset
  rintro _ ⟨x, rfl⟩
  exact leftQuotient_mem_of_derivClosed hc x L hL

theorem hasFinDeriv_zero : HasFinDeriv (0 : Language α) := by
  refine ⟨{0}, Set.finite_singleton _, ?_, rfl⟩
  rintro L hL a
  rw [Set.mem_singleton_iff] at hL
  subst hL
  rw [leftQuotient_zero]
  rfl

theorem hasFinDeriv_one : HasFinDeriv (1 : Language α) := by
  refine ⟨{1, 0}, (Set.finite_singleton _).insert _, ?_, by simp⟩
  rintro L hL a
  rcases hL with rfl | hL
  · rw [leftQuotient_one]; simp
  · rw [Set.mem_singleton_iff] at hL
    subst hL
    rw [leftQuotient_zero]
    simp

theorem hasFinDeriv_singleton (c : α) : HasFinDeriv ({[c]} : Language α) := by
  refine ⟨{({[c]} : Language α), 1, 0}, ((Set.finite_singleton _).insert _).insert _, ?_, by simp⟩
  rintro L hL a
  rcases hL with rfl | rfl | hL
  · rw [leftQuotient_singleton]
    split <;> simp
  · rw [leftQuotient_one]; simp
  · rw [Set.mem_singleton_iff] at hL
    subst hL
    rw [leftQuotient_zero]
    simp

theorem hasFinDeriv_add {A B : Language α} (hA : HasFinDeriv A) (hB : HasFinDeriv B) :
    HasFinDeriv (A + B) := by
  obtain ⟨F, hF, hcF, hAF⟩ := hA
  obtain ⟨G, hG, hcG, hBG⟩ := hB
  refine ⟨(fun p : Language α × Language α => p.1 + p.2) '' (F ×ˢ G), (hF.prod hG).image _, ?_,
    ⟨(A, B), ⟨hAF, hBG⟩, rfl⟩⟩
  rintro _ ⟨⟨X, Y⟩, ⟨hX, hY⟩, rfl⟩ a
  exact ⟨(X.leftQuotient [a], Y.leftQuotient [a]), ⟨hcF _ hX a, hcG _ hY a⟩,
    (leftQuotient_add X Y a).symm⟩

theorem hasFinDeriv_mul {A B : Language α} (hA : HasFinDeriv A) (hB : HasFinDeriv B) :
    HasFinDeriv (A * B) := by
  obtain ⟨F, hF, hcF, hAF⟩ := hA
  obtain ⟨G, hG, hcG, hBG⟩ := hB
  refine ⟨(fun p : Language α × Set (Language α) => p.1 * B + sSup p.2) ''
      (F ×ˢ {S | S ⊆ G}), (hF.prod hG.finite_subsets).image _, ?_,
      ⟨(A, ∅), ⟨hAF, by simp⟩, show A * B + sSup (∅ : Set (Language α)) = A * B by
        rw [sSup_empty_language, add_zero]⟩⟩
  rintro _ ⟨⟨X, S⟩, ⟨hX, hS⟩, rfl⟩ a
  simp only [Set.mem_setOf_eq] at hS
  refine ⟨(X.leftQuotient [a],
      (fun L : Language α => L.leftQuotient [a]) '' S ∪
        (if [] ∈ X then {B.leftQuotient [a]} else ∅)), ⟨hcF _ hX a, ?_⟩, ?_⟩
  · rintro L (⟨M, hM, rfl⟩ | hL)
    · exact hcG _ (hS hM) a
    · split at hL
      · rw [Set.mem_singleton_iff] at hL
        subst hL
        exact hcG _ hBG a
      · exact absurd hL (Set.notMem_empty _)
  · simp only
    rw [leftQuotient_add, leftQuotient_mul, leftQuotient_sSup, sSup_union_language]
    by_cases h : [] ∈ X
    · rw [if_pos h, if_pos h, sSup_singleton]
      abel
    · rw [if_neg h, if_neg h, sSup_empty_language]
      abel

theorem hasFinDeriv_kstar {A : Language α} (hA : HasFinDeriv A) : HasFinDeriv (A∗) := by
  obtain ⟨F, hF, hcF, hAF⟩ := hA
  refine ⟨insert (A∗) ((fun S : Set (Language α) => sSup S * A∗) '' {S | S ⊆ F}),
    (hF.finite_subsets.image _).insert _, ?_, by simp⟩
  rintro L hL a
  rcases hL with rfl | ⟨S, hS, rfl⟩
  · rw [leftQuotient_kstar]
    refine Or.inr ⟨{A.leftQuotient [a]}, ?_,
      show sSup {A.leftQuotient [a]} * A∗ = A.leftQuotient [a] * A∗ by rw [sSup_singleton]⟩
    simpa using hcF _ hAF a
  · simp only [Set.mem_setOf_eq] at hS
    refine Or.inr ⟨(fun L : Language α => L.leftQuotient [a]) '' S ∪
        (if [] ∈ sSup S then {A.leftQuotient [a]} else ∅), ?_, ?_⟩
    · rintro L (⟨M, hM, rfl⟩ | hL)
      · exact hcF _ (hS hM) a
      · split at hL
        · rw [Set.mem_singleton_iff] at hL
          subst hL
          exact hcF _ hAF a
        · exact absurd hL (Set.notMem_empty _)
    · simp only
      rw [leftQuotient_mul, leftQuotient_kstar, sSup_union_language, add_mul, leftQuotient_sSup]
      by_cases h : [] ∈ sSup S
      · rw [if_pos h, if_pos h, sSup_singleton]
      · rw [if_neg h, if_neg h, sSup_empty_language, zero_mul, add_zero]

theorem hasFinDeriv_of_regularExpression (R : RegularExpression α) : HasFinDeriv R.matches' := by
  induction R with
  | zero => exact hasFinDeriv_zero
  | epsilon => exact hasFinDeriv_one
  | char c => exact hasFinDeriv_singleton c
  | plus P Q ihP ihQ => exact hasFinDeriv_add ihP ihQ
  | comp P Q ihP ihQ => exact hasFinDeriv_mul ihP ihQ
  | star P ihP => exact hasFinDeriv_kstar ihP

/-- Every language matched by a regular expression is regular, i.e. accepted by a DFA with
finitely many states. -/
theorem isRegular_matches' (R : RegularExpression α) : R.matches'.IsRegular :=
  isRegular_of_hasFinDeriv (hasFinDeriv_of_regularExpression R)

end CS

import Mathlib
import RequestProject.Kleene

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

import RequestProject.DerivFamily
import RequestProject.DfaToRegex

/-!
# Kleene's theorem

A language over a finite alphabet is *regular* (matched by a regular expression) if and only if
it is accepted by a deterministic finite automaton.
-/

universe u v

namespace CS

/-- **Kleene's theorem** (finite-automata direction): over a finite alphabet, a language is
matched by a regular expression if and only if it is accepted by a DFA with finitely many
states. -/
theorem kleene_regex_dfa {α : Type u} [Fintype α] (L : Language α) :
    (∃ R : RegularExpression α, R.matches' = L) ↔
      ∃ (σ : Type v) (_ : Fintype σ) (M : DFA α σ), M.accepts = L := by
  constructor
  · rintro ⟨R, rfl⟩
    exact Language.isRegular_iff.mp (isRegular_matches' R)
  · rintro ⟨σ, _, M, rfl⟩
    classical
    exact exists_regularExpression_of_dfa M

/-- Restatement of Kleene's theorem using `Language.IsRegular`, Mathlib's predicate expressing
that a language is accepted by a DFA with finitely many states. -/
theorem kleene_regex_isRegular {α : Type u} [Fintype α] (L : Language α) :
    (∃ R : RegularExpression α, R.matches' = L) ↔ L.IsRegular :=
  (kleene_regex_dfa.{u, 0} L).trans Language.isRegular_iff.symm

end CS

