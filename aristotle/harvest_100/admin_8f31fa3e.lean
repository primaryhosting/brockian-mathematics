import Mathlib

/-!
# Kleene Regex Dfa
Category: Computer Science
Target: CS.kleene_regex_dfa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped Computability
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-- A language is *regex-expressible* if some regular expression matches exactly it. -/
def IsRegexLang {α : Type u} (L : Language α) : Prop :=
  ∃ r : RegularExpression α, r.matches' = L

/-! ## Generalities on languages -/

section Generalities

variable {α : Type u}

lemma mem_sSup_lang {S : Set (Language α)} {y : List α} :
    y ∈ sSup S ↔ ∃ M ∈ S, y ∈ M := Iff.rfl

lemma lang_ext {L₁ L₂ : Language α} (h : ∀ y, y ∈ L₁ ↔ y ∈ L₂) : L₁ = L₂ := Set.ext h

lemma mem_zero_lang {x : List α} : x ∉ (0 : Language α) := fun h => h

@[simp] lemma mem_zero_lang_iff {x : List α} : (x ∈ (0 : Language α)) ↔ False := Iff.rfl

@[simp] lemma mem_one_lang_iff {x : List α} : x ∈ (1 : Language α) ↔ x = [] := Iff.rfl

@[simp] lemma mem_singleton_lang_iff {w x : List α} : x ∈ ({w} : Language α) ↔ x = w := Iff.rfl

lemma mem_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Language α) (x : List α) :
    x ∈ ∑ i ∈ s, f i ↔ ∃ i ∈ s, x ∈ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      show x ∈ f a ∨ x ∈ ∑ i ∈ s, f i ↔ _
      simp [ih]

lemma IsRegexLang.zero : IsRegexLang (0 : Language α) := ⟨0, rfl⟩

lemma IsRegexLang.one : IsRegexLang (1 : Language α) := ⟨1, rfl⟩

lemma IsRegexLang.singleton (a : α) : IsRegexLang ({[a]} : Language α) :=
  ⟨RegularExpression.char a, rfl⟩

lemma IsRegexLang.add {L₁ L₂ : Language α} (h₁ : IsRegexLang L₁) (h₂ : IsRegexLang L₂) :
    IsRegexLang (L₁ + L₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ + r₂, rfl⟩

lemma IsRegexLang.mul {L₁ L₂ : Language α} (h₁ : IsRegexLang L₁) (h₂ : IsRegexLang L₂) :
    IsRegexLang (L₁ * L₂) := by
  obtain ⟨r₁, rfl⟩ := h₁
  obtain ⟨r₂, rfl⟩ := h₂
  exact ⟨r₁ * r₂, rfl⟩

lemma IsRegexLang.kstar {L : Language α} (h : IsRegexLang L) : IsRegexLang L∗ := by
  obtain ⟨r, rfl⟩ := h
  exact ⟨r.star, rfl⟩

lemma IsRegexLang.finset_sum {ι : Type*} (s : Finset ι) (f : ι → Language α)
    (h : ∀ i ∈ s, IsRegexLang (f i)) : IsRegexLang (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRegexLang.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end Generalities

/-! ## Kleene star manipulations -/

section Star

variable {α : Type u}

lemma cons_mem_kstar {L : Language α} {w u : List α} (hw : w ∈ L) (hu : u ∈ L∗) :
    w ++ u ∈ L∗ := by
  obtain ⟨W, rfl, hW⟩ := Language.mem_kstar.mp hu
  exact Language.mem_kstar.mpr ⟨w :: W, by simp, by simp_all⟩

lemma append_mem_kstar {L : Language α} {u v : List α} (hu : u ∈ L∗) (hv : v ∈ L∗) :
    u ++ v ∈ L∗ := by
  obtain ⟨U, rfl, hU⟩ := Language.mem_kstar.mp hu
  obtain ⟨V, rfl, hV⟩ := Language.mem_kstar.mp hv
  refine Language.mem_kstar.mpr ⟨U ++ V, by simp, ?_⟩
  intro y hy
  rcases List.mem_append.mp hy with h | h
  · exact hU y h
  · exact hV y h

end Star

/-! ## Part A: from regular expressions to DFAs, via Myhill–Nerode -/

section PartA

variable {α : Type u}

lemma kstar_split {L : Language α} {x y : List α} (h : x ++ y ∈ L∗) :
    (x ∈ L∗ ∧ y ∈ L∗) ∨ ∃ u v, u ∈ L∗ ∧ x = u ++ v ∧ y ∈ (L.leftQuotient v) * L∗ := by
  obtain ⟨W, hW, hmem⟩ := Language.mem_kstar.mp h
  clear h
  induction W generalizing x with
  | nil =>
      simp only [List.flatten_nil] at hW
      obtain ⟨hx, hy⟩ := List.append_eq_nil_iff.mp hW
      exact Or.inl ⟨by simp [hx, Language.nil_mem_kstar], by simp [hy, Language.nil_mem_kstar]⟩
  | cons w W ih =>
      simp only [List.flatten_cons] at hW
      rcases List.append_eq_append_iff.mp hW with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
      · refine Or.inr ⟨[], x, Language.nil_mem_kstar _, by simp, ?_⟩
        refine Language.mem_mul.mpr ⟨as, ?_, W.flatten, ?_, h2.symm⟩
        · show x ++ as ∈ L
          exact h1 ▸ hmem w (by simp)
        · exact Language.join_mem_kstar fun z hz => hmem z (by simp [hz])
      · have hmem' : ∀ z ∈ W, z ∈ L := fun z hz => hmem z (by simp [hz])
        rcases ih (x := bs) h2.symm hmem' with ⟨hbs, hy⟩ | ⟨u, v, hu, huv, hy⟩
        · exact Or.inl ⟨h1 ▸ cons_mem_kstar (hmem w (by simp)) hbs, hy⟩
        · exact Or.inr ⟨w ++ u, v, cons_mem_kstar (hmem w (by simp)) hu,
            by rw [h1, huv]; simp, hy⟩

lemma leftQuotient_mul (L₁ L₂ : Language α) (x : List α) :
    (L₁ * L₂).leftQuotient x =
      (L₁.leftQuotient x) * L₂ +
        sSup {N : Language α | ∃ v, (∃ u, u ∈ L₁ ∧ x = u ++ v) ∧ N = L₂.leftQuotient v} := by
  ext y
  simp only [Language.mem_leftQuotient, Language.mem_add, Language.mem_mul, mem_sSup_lang,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.mp hab with ⟨c, hc1, hc2⟩ | ⟨c, hc1, hc2⟩
    · exact Or.inr ⟨L₂.leftQuotient c, ⟨c, ⟨a, ha, hc1⟩, rfl⟩,
        by rw [Language.mem_leftQuotient, ← hc2]; exact hb⟩
    · exact Or.inl ⟨c, hc1 ▸ ha, b, hb, hc2.symm⟩
  · rintro (⟨c, hc, b, hb, rfl⟩ | ⟨N, ⟨v, ⟨u, hu, rfl⟩, rfl⟩, hy⟩)
    · exact ⟨x ++ c, hc, b, hb, by simp⟩
    · exact ⟨u, hu, v ++ y, hy, by simp⟩

lemma leftQuotient_kstar (L : Language α) (x : List α) :
    (L∗).leftQuotient x =
      (if x ∈ L∗ then L∗ else 0) +
        sSup {N : Language α |
          ∃ v, (∃ u, u ∈ L∗ ∧ x = u ++ v) ∧ N = (L.leftQuotient v) * L∗} := by
  ext y
  simp only [Language.mem_leftQuotient, Language.mem_add, mem_sSup_lang, Set.mem_setOf_eq]
  constructor
  · intro h
    rcases kstar_split h with ⟨hx, hy⟩ | ⟨u, v, hu, huv, hy⟩
    · exact Or.inl (by simp [hx, hy])
    · exact Or.inr ⟨_, ⟨v, ⟨u, hu, huv⟩, rfl⟩, hy⟩
  · rintro (h | ⟨N, ⟨v, ⟨u, hu, rfl⟩, rfl⟩, hy⟩)
    · by_cases hx : x ∈ L∗
      · rw [if_pos hx] at h
        exact append_mem_kstar hx h
      · rw [if_neg hx] at h
        exact absurd h mem_zero_lang
    · obtain ⟨s, hs, t, ht, rfl⟩ := Language.mem_mul.mp hy
      have hvs : v ++ s ∈ L := hs
      have h2 : u ++ ((v ++ s) ++ t) ∈ L∗ := append_mem_kstar hu (cons_mem_kstar hvs ht)
      simpa using h2

lemma leftQuotient_add (L₁ L₂ : Language α) (x : List α) :
    (L₁ + L₂).leftQuotient x = L₁.leftQuotient x + L₂.leftQuotient x :=
  lang_ext fun _ => Iff.rfl

lemma finite_range_leftQuotient_zero :
    (Set.range (0 : Language α).leftQuotient).Finite := by
  apply Set.Finite.subset (Set.finite_singleton (0 : Language α))
  rintro _ ⟨x, rfl⟩
  exact Set.mem_singleton_iff.mpr (lang_ext fun y => by simp)

lemma finite_range_leftQuotient_one :
    (Set.range (1 : Language α).leftQuotient).Finite := by
  apply Set.Finite.subset (Set.toFinite {(1 : Language α), 0})
  rintro _ ⟨x, rfl⟩
  rcases x with _ | ⟨a, x⟩
  · exact Or.inl (by simp)
  · exact Or.inr (Set.mem_singleton_iff.mpr (lang_ext fun y => by simp))

lemma finite_range_leftQuotient_char (a : α) :
    (Set.range ({[a]} : Language α).leftQuotient).Finite := by
  apply Set.Finite.subset (Set.toFinite {({[a]} : Language α), 1, 0})
  rintro _ ⟨x, rfl⟩
  match x with
  | [] => exact Or.inl (by simp)
  | [b] =>
      by_cases h : b = a
      · subst h
        exact Or.inr (Or.inl (lang_ext fun y => by simp))
      · exact Or.inr (Or.inr (Set.mem_singleton_iff.mpr (lang_ext fun y => by simp [h])))
  | b :: c :: t =>
      exact Or.inr (Or.inr (Set.mem_singleton_iff.mpr (lang_ext fun y => by simp)))

lemma finite_range_leftQuotient_add {L₁ L₂ : Language α}
    (h₁ : (Set.range L₁.leftQuotient).Finite) (h₂ : (Set.range L₂.leftQuotient).Finite) :
    (Set.range (L₁ + L₂).leftQuotient).Finite := by
  apply Set.Finite.subset ((h₁.prod h₂).image (fun p : Language α × Language α => p.1 + p.2))
  rintro _ ⟨x, rfl⟩
  exact ⟨(L₁.leftQuotient x, L₂.leftQuotient x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩,
    (leftQuotient_add L₁ L₂ x).symm⟩

lemma finite_range_leftQuotient_mul {L₁ L₂ : Language α}
    (h₁ : (Set.range L₁.leftQuotient).Finite) (h₂ : (Set.range L₂.leftQuotient).Finite) :
    (Set.range (L₁ * L₂).leftQuotient).Finite := by
  apply Set.Finite.subset ((h₁.prod h₂.finite_subsets).image
    (fun p : Language α × Set (Language α) => p.1 * L₂ + sSup p.2))
  rintro _ ⟨x, rfl⟩
  refine ⟨(L₁.leftQuotient x,
      {N : Language α | ∃ v, (∃ u, u ∈ L₁ ∧ x = u ++ v) ∧ N = L₂.leftQuotient v}),
    ⟨⟨x, rfl⟩, ?_⟩, (leftQuotient_mul L₁ L₂ x).symm⟩
  rintro N ⟨v, -, rfl⟩
  exact ⟨v, rfl⟩

lemma finite_range_leftQuotient_kstar {L : Language α}
    (h : (Set.range L.leftQuotient).Finite) :
    (Set.range (L∗).leftQuotient).Finite := by
  classical
  apply Set.Finite.subset (((Set.toFinite ({L∗, 0} : Set (Language α))).prod
      (h.image (fun N : Language α => N * L∗)).finite_subsets).image
    (fun p : Language α × Set (Language α) => p.1 + sSup p.2))
  rintro _ ⟨x, rfl⟩
  refine ⟨((if x ∈ L∗ then L∗ else 0),
      {N : Language α | ∃ v, (∃ u, u ∈ L∗ ∧ x = u ++ v) ∧ N = (L.leftQuotient v) * L∗}),
    ⟨?_, ?_⟩, (leftQuotient_kstar L x).symm⟩
  · by_cases hx : x ∈ L∗ <;> simp [hx]
  · rintro N ⟨v, -, rfl⟩
    exact ⟨L.leftQuotient v, ⟨v, rfl⟩, rfl⟩

/-- Every language matched by a regular expression has finitely many left quotients. -/
theorem finite_range_leftQuotient_matches' (r : RegularExpression α) :
    (Set.range (r.matches').leftQuotient).Finite := by
  induction r with
  | zero => exact finite_range_leftQuotient_zero
  | epsilon => exact finite_range_leftQuotient_one
  | char a => exact finite_range_leftQuotient_char a
  | plus P Q ihP ihQ => exact finite_range_leftQuotient_add ihP ihQ
  | comp P Q ihP ihQ => exact finite_range_leftQuotient_mul ihP ihQ
  | star P ih => exact finite_range_leftQuotient_kstar ih

/-- A regex-expressible language is regular (accepted by a DFA with finitely many states). -/
theorem isRegular_of_isRegexLang {L : Language α} (h : IsRegexLang L) : L.IsRegular := by
  obtain ⟨r, rfl⟩ := h
  exact Language.IsRegular.of_finite_range_leftQuotient (finite_range_leftQuotient_matches' r)

end PartA

/-! ## Part B: from DFAs to regular expressions, via Kleene's algorithm -/

section PartB

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/-- The set of words that take state `i` to state `j`, all of whose intermediate states
lie in the finite set `S`. -/
def pathLang (S : Finset σ) (i j : σ) : Language α :=
  {w | M.evalFrom i w = j ∧ ∀ n, 0 < n → n < w.length → M.evalFrom i (w.take n) ∈ S}

variable {M}

lemma mem_pathLang {S : Finset σ} {i j : σ} {w : List α} :
    w ∈ pathLang M S i j ↔
      M.evalFrom i w = j ∧ ∀ n, 0 < n → n < w.length → M.evalFrom i (w.take n) ∈ S :=
  Iff.rfl

lemma nil_mem_pathLang (S : Finset σ) (i : σ) : [] ∈ pathLang M S i i := by
  refine ⟨rfl, ?_⟩
  intro n _ hn
  simp at hn

lemma pathLang_mono {S T : Finset σ} (h : S ⊆ T) (i j : σ) :
    pathLang M S i j ≤ pathLang M T i j := by
  rintro w ⟨hw, hint⟩
  exact ⟨hw, fun n hn hn' => h (hint n hn hn')⟩

lemma pathLang_append {S : Finset σ} {i m j : σ} {u v : List α} (hm : m ∈ S)
    (hu : u ∈ pathLang M S i m) (hv : v ∈ pathLang M S m j) :
    u ++ v ∈ pathLang M S i j := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨by rw [M.evalFrom_of_append, hu1, hv1], ?_⟩
  intro n hn hlt
  rw [List.take_append, M.evalFrom_of_append]
  rcases lt_trichotomy n u.length with h | h | h
  · rw [Nat.sub_eq_zero_of_le h.le, List.take_zero]
    simpa using hu2 n hn h
  · subst h
    rw [List.take_length, Nat.sub_self, List.take_zero, hu1]
    simpa using hm
  · rw [List.take_of_length_le h.le, hu1]
    refine hv2 (n - u.length) (by omega) ?_
    simp only [List.length_append] at hlt
    omega

lemma kstar_pathLang_le {S T : Finset σ} {k : σ} (hST : S ⊆ T) (hk : k ∈ T) :
    (pathLang M S k k)∗ ≤ pathLang M T k k := by
  intro w hw
  obtain ⟨W, rfl, hW⟩ := Language.mem_kstar.mp hw
  clear hw
  induction W with
  | nil => simpa using nil_mem_pathLang T k
  | cons w W ih =>
      rw [List.flatten_cons]
      exact pathLang_append hk (pathLang_mono hST k k (hW w (by simp)))
        (ih fun z hz => hW z (by simp [hz]))

lemma pathLang_insert_le [DecidableEq σ] (k : σ) (S : Finset σ) (i j : σ) :
    pathLang M S i j + pathLang M S i k * (pathLang M S k k)∗ * pathLang M S k j
      ≤ pathLang M (insert k S) i j := by
  rintro w (hw | hw)
  · exact pathLang_mono (Finset.subset_insert k S) i j hw
  · obtain ⟨p, hp, t, ht, rfl⟩ := Language.mem_mul.mp hw
    obtain ⟨u, hu, z, hz, rfl⟩ := Language.mem_mul.mp hp
    have hk : k ∈ insert k S := Finset.mem_insert_self k S
    have hsub := Finset.subset_insert k S
    exact pathLang_append hk (pathLang_append hk (pathLang_mono hsub i k hu)
      (kstar_pathLang_le hsub hk hz)) (pathLang_mono hsub k j ht)

lemma pathLang_le_insert [DecidableEq σ] (k : σ) (S : Finset σ) :
    ∀ (N : ℕ) (i j : σ) (w : List α), w.length ≤ N → w ∈ pathLang M (insert k S) i j →
      w ∈ pathLang M S i j + pathLang M S i k * (pathLang M S k k)∗ * pathLang M S k j := by
  intro N
  induction N with
  | zero =>
      intro i j w hlen hw
      obtain ⟨hw1, -⟩ := hw
      have hw0 : w = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
      subst hw0
      exact Or.inl ⟨hw1, fun n _ hn => by simp at hn⟩
  | succ N ih =>
      intro i j w hlen hw
      obtain ⟨hw1, hw2⟩ := hw
      by_cases hex : ∃ n, 0 < n ∧ n < w.length ∧ M.evalFrom i (w.take n) = k
      · obtain ⟨hm0, hmlt, hmk⟩ := Nat.find_spec hex
        set m := Nat.find hex
        have hmin : ∀ n, n < m → ¬ (0 < n ∧ n < w.length ∧ M.evalFrom i (w.take n) = k) :=
          fun n hn => Nat.find_min hex hn
        have hu : w.take m ∈ pathLang M S i k := by
          refine ⟨hmk, ?_⟩
          intro n hn hlt
          rw [List.length_take, min_eq_left hmlt.le] at hlt
          rw [List.take_take, min_eq_left hlt.le]
          have h1 : M.evalFrom i (w.take n) ∈ insert k S := hw2 n hn (by omega)
          have h2 : M.evalFrom i (w.take n) ≠ k := fun hc => hmin n hlt ⟨hn, by omega, hc⟩
          exact Finset.mem_of_mem_insert_of_ne h1 h2
        have hv : w.drop m ∈ pathLang M (insert k S) k j := by
          refine ⟨?_, ?_⟩
          · have h := M.evalFrom_of_append i (w.take m) (w.drop m)
            rw [List.take_append_drop, hw1, hmk] at h
            exact h.symm
          · intro n hn hlt
            rw [List.length_drop] at hlt
            have key : w.take (m + n) = w.take m ++ (w.drop m).take n := List.take_add
            have h3 : M.evalFrom i (w.take (m + n)) ∈ insert k S :=
              hw2 (m + n) (by omega) (by omega)
            rw [key, M.evalFrom_of_append, hmk] at h3
            exact h3
        have hvlen : (w.drop m).length ≤ N := by
          rw [List.length_drop]; omega
        have hrec := ih k j (w.drop m) hvlen hv
        have hvstar : w.drop m ∈ (pathLang M S k k)∗ * pathLang M S k j := by
          rcases hrec with h | h
          · exact Language.mem_mul.mpr ⟨[], Language.nil_mem_kstar _, _, h, by simp⟩
          · obtain ⟨p, hp, t, ht, hpt⟩ := Language.mem_mul.mp h
            obtain ⟨a, ha, b, hb, hab⟩ := Language.mem_mul.mp hp
            exact Language.mem_mul.mpr ⟨p, hab ▸ cons_mem_kstar ha hb, t, ht, hpt⟩
        obtain ⟨z, hz, t, ht, hzt⟩ := Language.mem_mul.mp hvstar
        refine Or.inr (Language.mem_mul.mpr
          ⟨w.take m ++ z, Language.mem_mul.mpr ⟨w.take m, hu, z, hz, rfl⟩, t, ht, ?_⟩)
        rw [List.append_assoc, hzt, List.take_append_drop]
      · refine Or.inl ⟨hw1, ?_⟩
        intro n hn hlt
        have h1 := hw2 n hn hlt
        have h2 : M.evalFrom i (w.take n) ≠ k := fun hc => hex ⟨n, hn, hlt, hc⟩
        exact Finset.mem_of_mem_insert_of_ne h1 h2

/-- Kleene's recursion: adding one more allowed intermediate state `k`. -/
lemma pathLang_insert [DecidableEq σ] (k : σ) (S : Finset σ) (i j : σ) :
    pathLang M (insert k S) i j
      = pathLang M S i j + pathLang M S i k * (pathLang M S k k)∗ * pathLang M S k j := by
  refine le_antisymm (fun w hw => ?_) (pathLang_insert_le k S i j)
  exact pathLang_le_insert k S w.length i j w le_rfl hw

lemma pathLang_empty [Fintype α] (i j : σ) :
    pathLang M (∅ : Finset σ) i j
      = (if i = j then (1 : Language α) else 0)
        + ∑ a : α, (if M.step i a = j then ({[a]} : Language α) else 0) := by
  classical
  refine lang_ext fun w => ?_
  constructor
  · rintro ⟨h1, h2⟩
    match w with
    | [] =>
        refine Or.inl ?_
        have hij : i = j := h1
        simp only [if_pos hij]
        exact Language.nil_mem_one
    | [a] =>
        refine Or.inr ((mem_finset_sum _ _ _).mpr ⟨a, Finset.mem_univ a, ?_⟩)
        have hst : M.step i a = j := h1
        simp [hst]
    | a :: b :: t =>
        exact absurd (h2 1 (by norm_num) (by simp)) (by simp)
  · rintro (h | h)
    · by_cases hij : i = j
      · rw [if_pos hij] at h
        have hw : w = [] := h
        subst hw
        exact ⟨hij, fun n _ hn => by simp at hn⟩
      · rw [if_neg hij] at h
        exact h.elim
    · obtain ⟨a, -, ha⟩ := (mem_finset_sum _ _ _).mp h
      by_cases hst : M.step i a = j
      · rw [if_pos hst] at ha
        have hw : w = [a] := ha
        subst hw
        exact ⟨hst, fun n hn hlt => by simp at hlt; omega⟩
      · rw [if_neg hst] at ha
        exact ha.elim

lemma isRegexLang_pathLang [Fintype α] [DecidableEq σ] (S : Finset σ) (i j : σ) :
    IsRegexLang (pathLang M S i j) := by
  induction S using Finset.induction generalizing i j with
  | empty =>
      rw [pathLang_empty]
      refine IsRegexLang.add ?_ (IsRegexLang.finset_sum _ _ fun a _ => ?_)
      · split
        · exact IsRegexLang.one
        · exact IsRegexLang.zero
      · split
        · exact IsRegexLang.singleton a
        · exact IsRegexLang.zero
  | insert k S hk ih =>
      rw [pathLang_insert]
      exact (ih i j).add (((ih i k).mul (ih k k).kstar).mul (ih k j))

variable (M)

lemma accepts_eq_sum [Fintype σ] [DecidablePred (· ∈ M.accept)] :
    M.accepts = ∑ j ∈ Finset.univ.filter (fun j => j ∈ M.accept),
      pathLang M (Finset.univ : Finset σ) M.start j := by
  refine lang_ext fun w => ?_
  rw [mem_finset_sum]
  constructor
  · intro h
    exact ⟨M.evalFrom M.start w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl,
      fun n _ _ => Finset.mem_univ _⟩
  · rintro ⟨j, hj, hw, -⟩
    have hj' : j ∈ M.accept := (Finset.mem_filter.mp hj).2
    show M.evalFrom M.start w ∈ M.accept
    rw [hw]
    exact hj'

/-- The language accepted by a DFA over a finite alphabet is matched by a regular expression. -/
theorem isRegexLang_accepts [Fintype α] [Fintype σ] [DecidableEq σ] :
    IsRegexLang M.accepts := by
  classical
  rw [accepts_eq_sum]
  exact IsRegexLang.finset_sum _ _ fun j _ => isRegexLang_pathLang _ _ _

end PartB

/-! ## Kleene's theorem -/

/-- **Kleene's theorem**: over a finite alphabet, a language is matched by a regular
expression if and only if it is regular, i.e. accepted by a DFA with finitely many states. -/
theorem kleene_regex_dfa {α : Type u} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔ L.IsRegular := by
  constructor
  · intro h
    exact isRegular_of_isRegexLang h
  · rintro ⟨σ, _, M, rfl⟩
    classical
    exact isRegexLang_accepts M

/-- **Kleene's theorem**, with the DFA side spelled out: over a finite alphabet, a language
is matched by a regular expression if and only if there is a DFA with finitely many states
whose accepted language is exactly it. -/
theorem kleene_regex_dfa_explicit {α : Type u} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔
      ∃ (σ : Type v) (_ : Fintype σ) (M : DFA α σ), M.accepts = L := by
  rw [kleene_regex_dfa L]
  exact Language.isRegular_iff

end CS

