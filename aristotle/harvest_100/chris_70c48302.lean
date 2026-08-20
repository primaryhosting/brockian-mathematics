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

theorem leftQuotient_zero (x : List α) : (0 : Language α).leftQuotient x = 0 := by
  ext y; simp only [Language.mem_leftQuotient, Language.notMem_zero]

theorem leftQuotient_add (L M : Language α) (x : List α) :
    (L + M).leftQuotient x = L.leftQuotient x + M.leftQuotient x := by
  ext y; simp only [Language.mem_leftQuotient, Language.mem_add]

/-- Left quotient of a product: either the whole of `x` is consumed by the left factor, or `x`
splits as a word of the left factor followed by a prefix of a word of the right factor. -/
theorem leftQuotient_mul (L M : Language α) (x : List α) :
    (L * M).leftQuotient x =
      (L.leftQuotient x) * M + sSup {N | ∃ u v, x = u ++ v ∧ u ∈ L ∧ N = M.leftQuotient v} := by
  ext y
  simp only [Language.mem_leftQuotient, Language.mem_add, Language.mem_mul]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases List.append_eq_append_iff.1 hab with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · exact Or.inr ⟨M.leftQuotient a', ⟨a, a', rfl, ha, rfl⟩, by simpa using hb⟩
    · exact Or.inl ⟨c', by simpa using ha, b, hb, rfl⟩
  · rintro (⟨a, ha, b, hb, rfl⟩ | ⟨N, ⟨u, v, rfl, hu, rfl⟩, hy⟩)
    · exact ⟨x ++ a, by simpa using ha, b, hb, by simp⟩
    · exact ⟨u, hu, v ++ y, by simpa using hy, by simp⟩

/-- Auxiliary form of `kstar_split`, by induction on the list of factors. -/
theorem kstar_split_aux {L : Language α} : ∀ ws : List (List α), (∀ w ∈ ws, w ∈ L) →
    ∀ x y : List α, x ≠ [] → x ++ y = ws.flatten →
    ∃ u v y₁ y₂, x = u ++ v ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ y₁ ∈ L ∧ y = y₁ ++ y₂ ∧ y₂ ∈ L∗ := by
  intro ws
  induction ws with
  | nil =>
    intro _ x y hx hflat
    simp only [List.flatten_nil, List.append_eq_nil_iff] at hflat
    exact absurd hflat.1 hx
  | cons w ws ih =>
    intro hws x y hx hflat
    rw [List.flatten_cons] at hflat
    have hw : w ∈ L := hws w (by simp)
    have hws' : ∀ z ∈ ws, z ∈ L := fun z hz => hws z (by simp [hz])
    have hstar : ws.flatten ∈ L∗ := Language.join_mem_kstar hws'
    rcases List.append_eq_append_iff.1 hflat with ⟨a', hw', rfl⟩ | ⟨c', rfl, hflat'⟩
    · exact ⟨[], x, a', ws.flatten, by simp, hx, Language.nil_mem_kstar _, hw' ▸ hw, rfl, hstar⟩
    · rcases eq_or_ne c' [] with rfl | hc'
      · refine ⟨[], w, [], y, by simp, by simpa using hx, Language.nil_mem_kstar _,
          by simpa using hw, by simp, ?_⟩
        simp only [List.nil_append] at hflat'
        exact hflat' ▸ hstar
      · obtain ⟨u, v, y₁, y₂, h1, h2, h3, h4, h5, h6⟩ := ih hws' c' y hc' hflat'.symm
        exact ⟨w ++ u, v, y₁, y₂, by rw [h1, List.append_assoc], h2,
          mul_kstar_le_kstar (a := L) ⟨w, hw, u, h3, rfl⟩, h4, h5, h6⟩

/-- If `x ≠ []` and `x ++ y ∈ L∗`, then the star decomposition of `x ++ y` can be cut at the
factor that contains the end of `x`. -/
theorem kstar_split {L : Language α} {x y : List α} (hx : x ≠ []) (h : x ++ y ∈ L∗) :
    ∃ u v y₁ y₂, x = u ++ v ∧ v ≠ [] ∧ u ∈ L∗ ∧ v ++ y₁ ∈ L ∧ y = y₁ ++ y₂ ∧ y₂ ∈ L∗ := by
  obtain ⟨ws, hflat, hws⟩ := Language.mem_kstar.1 h
  exact kstar_split_aux ws hws x y hx hflat

/-- Left quotient of a Kleene star by a nonempty word. -/
theorem leftQuotient_kstar {L : Language α} {x : List α} (hx : x ≠ []) :
    (L∗).leftQuotient x =
      (sSup {N | ∃ u v, x = u ++ v ∧ v ≠ [] ∧ u ∈ L∗ ∧ N = L.leftQuotient v}) * L∗ := by
  ext y
  simp only [Language.mem_leftQuotient, Language.mem_mul]
  constructor
  · intro h
    obtain ⟨u, v, y₁, y₂, h1, h2, h3, h4, h5, h6⟩ := kstar_split hx h
    exact ⟨y₁, ⟨L.leftQuotient v, ⟨u, v, h1, h2, h3, rfl⟩, by simpa using h4⟩, y₂, h6, h5.symm⟩
  · rintro ⟨a, ⟨N, ⟨u, v, rfl, hv, hu, rfl⟩, ha⟩, b, hb, rfl⟩
    obtain ⟨W1, rfl, hW1⟩ := Language.mem_kstar.1 hu
    obtain ⟨W2, rfl, hW2⟩ := Language.mem_kstar.1 hb
    have hflat : W1.flatten ++ v ++ (a ++ W2.flatten) = (W1 ++ (v ++ a) :: W2).flatten := by
      simp [List.flatten_append]
    rw [hflat]
    refine Language.join_mem_kstar ?_
    intro z hz
    simp only [List.mem_append, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact hW1 z hz
    · simpa using ha
    · exact hW2 z hz

/-- **Brzozowski**: a regular expression has only finitely many left quotients. -/
theorem finite_range_leftQuotient_matches' (r : RegularExpression α) :
    (Set.range (r.matches').leftQuotient).Finite := by
  induction r with
  | zero =>
    refine Set.Finite.subset (Set.finite_singleton (0 : Language α)) ?_
    rintro _ ⟨x, rfl⟩
    simp only [RegularExpression.matches', Set.mem_singleton_iff]
    exact leftQuotient_zero x
  | epsilon =>
    refine Set.Finite.subset (Set.toFinite {(1 : Language α), 0}) ?_
    rintro _ ⟨x, rfl⟩
    rcases eq_or_ne x [] with rfl | hx
    · left; simp [RegularExpression.matches']
    · right
      simp only [RegularExpression.matches', Set.mem_singleton_iff]
      ext y
      simp only [Language.mem_leftQuotient, Language.mem_one, Language.notMem_zero, iff_false,
        List.append_eq_nil_iff, not_and]
      intro h; exact absurd h hx
  | char a =>
    refine Set.Finite.subset (Set.toFinite {({[a]} : Language α), 1, 0}) ?_
    rintro _ ⟨x, rfl⟩
    have h0 : (RegularExpression.char a).matches' = ({[a]} : Language α) := rfl
    have hmem : ∀ z : List α, z ∈ ({[a]} : Language α) ↔ z = [a] := fun _ => Iff.rfl
    rw [h0]
    rcases eq_or_ne x [] with rfl | hx
    · left; rw [Language.leftQuotient_nil]
    rcases eq_or_ne x [a] with rfl | hxa
    · right; left
      ext y
      rw [Language.mem_leftQuotient, hmem, Language.mem_one]
      simp
    · right; right
      ext y
      rw [Language.mem_leftQuotient, hmem]
      simp only [Language.notMem_zero, iff_false]
      intro h
      rcases List.append_eq_cons_iff.1 h with ⟨rfl, _⟩ | ⟨a', rfl, h'⟩
      · exact hx rfl
      · simp only [List.nil_eq, List.append_eq_nil_iff] at h'
        exact hxa (by simp [h'.1])
  | plus P Q ihP ihQ =>
    refine Set.Finite.subset ((ihP.prod ihQ).image fun p => p.1 + p.2) ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨(P.matches'.leftQuotient x, Q.matches'.leftQuotient x),
      ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, (leftQuotient_add _ _ x).symm⟩
  | comp P Q ihP ihQ =>
    refine Set.Finite.subset ((ihP.prod ihQ.finite_subsets).image
      (fun p : Language α × Set (Language α) => p.1 * Q.matches' + sSup p.2)) ?_
    rintro _ ⟨x, rfl⟩
    refine ⟨(P.matches'.leftQuotient x,
      {N | ∃ u v, x = u ++ v ∧ u ∈ P.matches' ∧ N = Q.matches'.leftQuotient v}),
      ⟨⟨x, rfl⟩, ?_⟩, ?_⟩
    · rintro N ⟨u, v, -, -, rfl⟩
      exact ⟨v, rfl⟩
    · exact (leftQuotient_mul _ _ x).symm
  | star P ihP =>
    refine Set.Finite.subset ((ihP.finite_subsets.image
      fun S => sSup S * P.matches'∗).insert (P.matches'∗)) ?_
    rintro _ ⟨x, rfl⟩
    rcases eq_or_ne x [] with rfl | hx
    · left; simp [RegularExpression.matches']
    · right
      refine ⟨{N | ∃ u v, x = u ++ v ∧ v ≠ [] ∧ u ∈ P.matches'∗ ∧ N = P.matches'.leftQuotient v},
        ?_, ?_⟩
      · rintro N ⟨u, v, -, -, -, rfl⟩
        exact ⟨v, rfl⟩
      · simp only [RegularExpression.matches']
        exact (leftQuotient_kstar hx).symm

/-- One direction of Kleene's theorem: the language of a regular expression is accepted by some
DFA with finitely many states. -/
theorem isRegular_matches' (r : RegularExpression α) : (r.matches').IsRegular :=
  Language.IsRegular.of_finite_range_leftQuotient (finite_range_leftQuotient_matches' r)

end RegexToDFA

/-! ## Part 2: a language accepted by a finite DFA over a finite alphabet is regular

This is the classical Kleene construction, by induction on the set of allowed intermediate
states of a path. -/

section DFAToRegex

variable {α : Type u} {σ : Type v}

/-- `L` is described by a regular expression. -/
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

theorem mem_pathLang {S : Finset σ} {p q : σ} {x : List α} :
    x ∈ pathLang M S p q ↔ M.evalFrom p x = q ∧
      ∀ u v : List α, u ++ v = x → u ≠ [] → v ≠ [] → M.evalFrom p u ∈ S := Iff.rfl

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

