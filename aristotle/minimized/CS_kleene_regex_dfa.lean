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
open scoped Classical
open scoped Pointwise
open scoped Computability

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u v

/-! ## Part 1: the language of a regular expression is accepted by a finite DFA

We use the Myhill–Nerode theorem: it suffices to show that a regular expression has only
finitely many left quotients (Brzozowski derivatives, viewed as languages). -/

section RegexToDFA

variable {α : Type u}

def IsRegexLang (L : Language α) : Prop := ∃ r : RegularExpression α, r.matches' = L

theorem IsRegexLang.zero : IsRegexLang (0 : Language α) := ⟨0, rfl⟩

theorem IsRegexLang.one : IsRegexLang (1 : Language α) := ⟨1, rfl⟩

theorem IsRegexLang.char (a : α) : IsRegexLang ({[a]} : Language α) :=
  ⟨RegularExpression.char a, rfl⟩

theorem IsRegexLang.add {L M : Language α} (hL : IsRegexLang L) (hM : IsRegexLang M) :
    IsRegexLang (L + M) := by
  obtain ⟨r, rfl⟩ := hL; obtain ⟨s, rfl⟩ := hM
  exact ⟨r + s, rfl⟩

theorem IsRegexLang.mul {L M : Language α} (hL : IsRegexLang L) (hM : IsRegexLang M) :
    IsRegexLang (L * M) := by
  obtain ⟨r, rfl⟩ := hL; obtain ⟨s, rfl⟩ := hM
  exact ⟨r * s, rfl⟩

theorem IsRegexLang.kstar {L : Language α} (hL : IsRegexLang L) : IsRegexLang (L∗) := by
  obtain ⟨r, rfl⟩ := hL
  exact ⟨r.star, RegularExpression.matches'_star r⟩

theorem IsRegexLang.finsetSup {ι : Type*} (s : Finset ι) (f : ι → Language α)
    (h : ∀ i ∈ s, IsRegexLang (f i)) : IsRegexLang (⨆ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using IsRegexLang.zero
  | insert a s _ ih =>
    rw [Finset.iSup_insert]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

theorem mem_finsetSup {ι : Type*} (f : ι → Language α) (s : Finset ι) (x : List α) :
    x ∈ (⨆ i ∈ s, f i) ↔ ∃ i ∈ s, x ∈ f i := by
  simp only [Language.mem_iSup, exists_prop]

variable (M : DFA α σ)

/-- The language of words taking the automaton from `p` to `q`, all of whose intermediate states
lie in `S`. -/

def pathLang (S : Finset σ) (p q : σ) : Language α :=
  {x : List α | M.evalFrom p x = q ∧
    ∀ u v : List α, u ++ v = x → u ≠ [] → v ≠ [] → M.evalFrom p u ∈ S}

theorem pathLang_mono {S T : Finset σ} (h : S ⊆ T) (p q : σ) :
    pathLang M S p q ≤ pathLang M T p q := by
  rintro x ⟨h1, h2⟩
  exact ⟨h1, fun u v huv hu hv => h (h2 u v huv hu hv)⟩

theorem nil_mem_pathLang (S : Finset σ) (p : σ) : [] ∈ pathLang M S p p := by
  refine ⟨rfl, fun u v huv hu _ => ?_⟩
  simp only [List.append_eq_nil_iff] at huv
  exact absurd huv.1 hu

theorem singleton_mem_pathLang (S : Finset σ) (p : σ) (a : α) :
    [a] ∈ pathLang M S p (M.step p a) := by
  refine ⟨by simp, fun u v huv hu hv => ?_⟩
  rcases u with _ | ⟨b, u⟩
  · exact absurd rfl hu
  · rcases u with _ | ⟨c, u⟩
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at huv
      exact absurd huv.2 hv
    · simp at huv

variable [DecidableEq σ]

/-- Concatenating a path from `p` to `m` with a path from `m` to `q` yields a path from `p` to
`q` whose intermediate states may additionally include `m`. -/

theorem pathLang_append {S : Finset σ} {p m q : σ} {x y : List α}
    (hx : x ∈ pathLang M S p m) (hy : y ∈ pathLang M S m q) :
    x ++ y ∈ pathLang M (insert m S) p q := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨by rw [DFA.evalFrom_of_append, hx1, hy1], fun u w huw hu hw => ?_⟩
  rcases List.append_eq_append_iff.1 huw with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
  · rcases eq_or_ne a' [] with rfl | ha'
    · simp only [List.append_nil] at hx1
      rw [hx1]
      exact Finset.mem_insert_self m S
    · exact Finset.mem_insert_of_mem (hx2 u a' rfl hu ha')
  · rcases eq_or_ne c' [] with rfl | hc'
    · simp only [List.append_nil]
      rw [hx1]
      exact Finset.mem_insert_self m S
    · rw [DFA.evalFrom_of_append, hx1]
      exact Finset.mem_insert_of_mem (hy2 c' w rfl hc' hw)

theorem pathLang_mul_le {S : Finset σ} {p m q : σ} (hm : m ∈ S) :
    pathLang M S p m * pathLang M S m q ≤ pathLang M S p q := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  have h := pathLang_append M hx hy
  rwa [Finset.insert_eq_self.2 hm] at h

theorem kstar_pathLang_le {S : Finset σ} {m : σ} :
    (pathLang M S m m)∗ ≤ pathLang M (insert m S) m m := by
  rintro z ⟨ws, rfl, hws⟩
  induction ws with
  | nil => simpa using nil_mem_pathLang M (insert m S) m
  | cons w ws ih =>
    rw [List.flatten_cons]
    have hw : w ∈ pathLang M (insert m S) m m :=
      pathLang_mono M (Finset.subset_insert m S) m m (hws w (by simp))
    have hrest : ws.flatten ∈ pathLang M (insert m S) m m :=
      ih fun z hz => hws z (by simp [hz])
    have h := pathLang_append M hw hrest
    rwa [Finset.insert_idem] at h

theorem pathLang_insert_ge (S : Finset σ) (r p q : σ) :
    pathLang M S p q + pathLang M S p r * (pathLang M S r r)∗ * pathLang M S r q ≤
      pathLang M (insert r S) p q := by
  rintro z (hz | hz)
  · exact pathLang_mono M (Finset.subset_insert r S) p q hz
  · obtain ⟨w, ⟨x, hx, c, hc, rfl⟩, y, hy, rfl⟩ := hz
    have hc' : c ∈ pathLang M (insert r S) r r := kstar_pathLang_le M hc
    have hy' : y ∈ pathLang M (insert r S) r q :=
      pathLang_mono M (Finset.subset_insert r S) r q hy
    have hcy : c ++ y ∈ pathLang M (insert r S) r q := by
      have h := pathLang_append M hc' hy'
      rwa [Finset.insert_idem] at h
    have hx' : x ∈ pathLang M (insert r S) p r :=
      pathLang_mono M (Finset.subset_insert r S) p r hx
    have h := pathLang_append M hx' hcy
    rw [Finset.insert_idem] at h
    show (x ++ c) ++ y ∈ _
    rwa [List.append_assoc]

theorem pathLang_insert_le (S : Finset σ) (r q : σ) : ∀ (x : List α) (p : σ),
    x ∈ pathLang M (insert r S) p q →
    x ∈ pathLang M S p q + pathLang M S p r * (pathLang M S r r)∗ * pathLang M S r q := by
  intro x
  induction x with
  | nil =>
    intro p h
    obtain ⟨h1, -⟩ := h
    rw [DFA.evalFrom_nil] at h1
    subst h1
    exact Or.inl (nil_mem_pathLang M S p)
  | cons a x' ih =>
    intro p h
    obtain ⟨h1, h2⟩ := h
    rcases eq_or_ne x' [] with rfl | hx'
    · refine Or.inl ⟨h1, fun u v huv hu hv => ?_⟩
      rcases u with _ | ⟨b, u⟩
      · exact absurd rfl hu
      · rcases u with _ | ⟨c, u⟩
        · simp only [List.cons_append, List.nil_append, List.cons.injEq] at huv
          exact absurd huv.2 hv
        · simp at huv
    · set p' := M.step p a with hp'def
      have hstep : ∀ w : List α, M.evalFrom p (a :: w) = M.evalFrom p' w := by
        intro w; rw [DFA.evalFrom_cons]
      have hx'mem : x' ∈ pathLang M (insert r S) p' q := by
        refine ⟨by rw [← hstep]; exact h1, fun u v huv hu hv => ?_⟩
        have h3 := h2 (a :: u) v (by rw [List.cons_append, huv]) (by simp) hv
        rwa [hstep] at h3
      have hp'S : p' ∈ insert r S := by
        have h3 := h2 [a] x' rfl (by simp) hx'
        rwa [DFA.evalFrom_singleton] at h3
      have ha : [a] ∈ pathLang M S p p' := singleton_mem_pathLang M S p a
      rcases ih p' hx'mem with h3 | h3
      · rcases eq_or_ne p' r with hpr | hpr
        · subst hpr
          refine Or.inr ⟨[a] ++ [], ⟨[a], ha, [], Language.nil_mem_kstar _, rfl⟩, x', h3, ?_⟩
          simp
        · exact Or.inl (pathLang_mul_le M (Finset.mem_of_mem_insert_of_ne hp'S hpr)
            ⟨[a], ha, x', h3, rfl⟩)
      · obtain ⟨w, ⟨c, hc, d, hd, rfl⟩, e, he, rfl⟩ := h3
        rcases eq_or_ne p' r with hpr | hpr
        · subst hpr
          refine Or.inr ⟨[a] ++ (c ++ d), ⟨[a], ha, c ++ d, ?_, rfl⟩, e, he, by simp⟩
          exact mul_kstar_le_kstar (a := pathLang M S p' p') ⟨c, hc, d, hd, rfl⟩
        · refine Or.inr ⟨([a] ++ c) ++ d, ⟨[a] ++ c,
            pathLang_mul_le M (Finset.mem_of_mem_insert_of_ne hp'S hpr) ⟨[a], ha, c, hc, rfl⟩,
            d, hd, rfl⟩, e, he, by simp⟩

/-- The Kleene recursion: adding one allowed intermediate state `r`. -/

theorem pathLang_insert (S : Finset σ) (r p q : σ) :
    pathLang M (insert r S) p q =
      pathLang M S p q + pathLang M S p r * (pathLang M S r r)∗ * pathLang M S r q :=
  le_antisymm (fun x hx => pathLang_insert_le M S r q x p hx) (pathLang_insert_ge M S r p q)

variable [Fintype α]

/-- Base case of the Kleene recursion: paths with no intermediate states. -/

theorem pathLang_empty (p q : σ) :
    pathLang M ∅ p q = (if p = q then (1 : Language α) else 0) +
      ⨆ a ∈ (Finset.univ.filter fun a : α => M.step p a = q), ({[a]} : Language α) := by
  ext x
  rw [Language.mem_add, mem_finsetSup]
  constructor
  · rintro ⟨h1, h2⟩
    match x with
    | [] =>
      rw [DFA.evalFrom_nil] at h1
      left
      rw [if_pos h1]
      exact Language.nil_mem_one
    | [a] =>
      right
      refine ⟨a, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rwa [DFA.evalFrom_singleton] at h1
    | a :: b :: t =>
      exact absurd (h2 [a] (b :: t) rfl (by simp) (by simp)) (by simp)
  · rintro (h | ⟨a, ha, hx⟩)
    · rcases eq_or_ne p q with rfl | hpq
      · rw [if_pos rfl, Language.mem_one] at h
        subst h
        exact nil_mem_pathLang M ∅ p
      · rw [if_neg hpq] at h
        exact absurd h (Language.notMem_zero x)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      have hx' : x = [a] := hx
      subst hx'
      have h := singleton_mem_pathLang M (∅ : Finset σ) p a
      rwa [ha] at h

theorem isRegexLang_pathLang_empty (p q : σ) : IsRegexLang (pathLang M (∅ : Finset σ) p q) := by
  rw [pathLang_empty]
  refine IsRegexLang.add ?_ (IsRegexLang.finsetSup _ _ fun a _ => IsRegexLang.char a)
  by_cases h : p = q
  · rw [if_pos h]; exact IsRegexLang.one
  · rw [if_neg h]; exact IsRegexLang.zero

theorem isRegexLang_pathLang (S : Finset σ) : ∀ p q : σ, IsRegexLang (pathLang M S p q) := by
  induction S using Finset.induction_on with
  | empty => exact fun p q => isRegexLang_pathLang_empty M p q
  | insert r S _ ih =>
    intro p q
    rw [pathLang_insert]
    exact (ih p q).add (((ih p r).mul (ih r r).kstar).mul (ih r q))

variable [Fintype σ]

omit [DecidableEq σ] [Fintype α] in

theorem accepts_eq_finsetSup :
    M.accepts =
      ⨆ q ∈ (Finset.univ.filter fun q : σ => q ∈ M.accept), pathLang M Finset.univ M.start q := by
  ext x
  rw [mem_finsetSup]
  constructor
  · intro h
    refine ⟨M.evalFrom M.start x, ?_, rfl, fun u v _ _ _ => Finset.mem_univ _⟩
    simpa using h
  · rintro ⟨q, hq, h1, -⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [DFA.mem_accepts, DFA.eval, h1]
    exact hq

/-- The other direction of Kleene's theorem: over a finite alphabet, the language accepted by a
DFA with finitely many states is described by a regular expression. -/

theorem isRegexLang_accepts : IsRegexLang M.accepts := by
  rw [accepts_eq_finsetSup]
  exact IsRegexLang.finsetSup _ _ fun q _ => isRegexLang_pathLang M _ _ _

end DFAToRegex

/-- **Kleene's theorem.** Over a finite alphabet, a language is described by a regular expression
if and only if it is accepted by a DFA with finitely many states (`Language.IsRegular`). -/

theorem kleene_regex_dfa {α : Type u} [Fintype α] (L : Language α) :
    (∃ r : RegularExpression α, r.matches' = L) ↔ L.IsRegular := by
  constructor
  · rintro ⟨r, rfl⟩
    exact isRegular_matches' r
  · rintro ⟨s, hs, M, rfl⟩
    exact isRegexLang_accepts M

end CS

#print axioms CS.kleene_regex_dfa
