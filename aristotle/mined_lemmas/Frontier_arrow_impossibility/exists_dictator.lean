/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A ranked voting rule (social welfare function) turns a profile of individual rankings of the
alternatives into a social ranking.  Arrow's theorem says that as soon as there are at least
three alternatives, no such rule can be unanimous (Pareto), independent of irrelevant
alternatives, and non-dictatorial at the same time.

The key intermediate result is the *field expansion* / contagion lemma
`Frontier.decisive_of_almostDecisiveFor`: a coalition that gets its way on one ordered pair of
alternatives against unanimous opposition is decisive for *every* ordered pair.  A minimal
decisive coalition is then shown to be a singleton, i.e. a dictator.
-/

namespace Frontier

/-- A *ranking* of the alternatives `α`: a total, transitive, antisymmetric relation, i.e. a
linear order given as a relation.  `rel x y` reads "`x` is at least as good as `y`". -/
structure Ranking (α : Type*) where
  rel : α → α → Prop
  rel_total : ∀ x y, rel x y ∨ rel y x
  rel_trans : ∀ {x y z}, rel x y → rel y z → rel x z
  rel_antisymm : ∀ {x y}, rel x y → rel y x → x = y

namespace Ranking

variable {α : Type*}

/-- Strict preference: `x` is ranked strictly above `y`. -/

theorem exists_dictator [Fintype V] (hU : Unanimous F) (hI : IIA F) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : ∃ i : V, IsDictator F i := by
  classical
  obtain ⟨r₀⟩ : Nonempty (Ranking α) := inferInstance
  -- there are at least three alternatives
  have h3 : ∀ x y : α, ∃ z : α, z ≠ x ∧ z ≠ y := by
    intro x y
    by_contra hcon
    push_neg at hcon
    have ha : a = x ∨ a = y := by
      by_cases h' : a = x
      · exact Or.inl h'
      · exact Or.inr (hcon a h')
    have hb : b = x ∨ b = y := by
      by_cases h' : b = x
      · exact Or.inl h'
      · exact Or.inr (hcon b h')
    have hc : c = x ∨ c = y := by
      by_cases h' : c = x
      · exact Or.inl h'
      · exact Or.inr (hcon c h')
    rcases ha with h' | h' <;> rcases hb with h'' | h'' <;> rcases hc with h''' | h''' <;>
      subst_vars <;> simp_all
  -- the whole electorate is decisive
  have huniv : Decisive F (Finset.univ : Finset V) := by
    intro x y _ p hp
    exact hU p x y fun i => hp i (Finset.mem_univ i)
  have hex : ∃ n, ∃ G : Finset V, Decisive F G ∧ G.card = n :=
    ⟨_, Finset.univ, huniv, rfl⟩
  obtain ⟨G, hG, hGcard⟩ := Nat.find_spec hex
  have hmin : ∀ H : Finset V, Decisive F H → Nat.find hex ≤ H.card := fun H hH =>
    Nat.find_le ⟨H, hH, rfl⟩
  have hGne : G.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hG0
    subst hG0
    have h1 : (F fun _ => r₀).pref a b := hG a b hab _ (by simp)
    have h2 : (F fun _ => r₀).pref b a := hG b a (Ne.symm hab) _ (by simp)
    exact (F fun _ => r₀).pref_asymm h1 h2
  obtain ⟨i, hi⟩ := hGne
  by_cases hsing : G.erase i = ∅
  · -- `G = {i}`, so `i` is a dictator
    refine ⟨i, ?_⟩
    intro p x y hxy
    have hGi : G = {i} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hi, fun j hj => ?_⟩
      by_contra hji
      have : j ∈ G.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      simp [hsing] at this
    refine hG x y hxy.2 p ?_
    intro j hj
    rw [hGi, Finset.mem_singleton] at hj
    subst hj
    exact hxy
  · -- otherwise minimality of `G` is contradicted
    exfalso
    have hG'ne : (G.erase i).Nonempty := Finset.nonempty_iff_ne_empty.mpr hsing
    have hcard2 : 2 ≤ G.card := by
      have h5 : (G.erase i).card + 1 = G.card := Finset.card_erase_add_one hi
      have h1 : 1 ≤ (G.erase i).card := Finset.card_pos.mpr hG'ne
      omega
    -- the pivotal profile: `i` ranks `a > b > c`, the rest of `G` ranks `c > a > b`, and the
    -- voters outside `G` rank `b > c > a`
    set q : V → Ranking α := fun j =>
      if j = i then top3 a b c r₀ else if j ∈ G then top3 c a b r₀ else top3 b c a r₀ with hqdef
    have hqi : q i = top3 a b c r₀ := by simp [hqdef]
    have hqG' : ∀ j, j ≠ i → j ∈ G → q j = top3 c a b r₀ := by
      intro j hj hjG; simp [hqdef, hj, hjG]
    have hqout : ∀ j, j ∉ G → q j = top3 b c a r₀ := by
      intro j hjG
      have hj : j ≠ i := by rintro rfl; exact hjG hi
      simp [hqdef, hj, hjG]
    -- everyone in `G` prefers `a` to `b`, so society does
    have hGab : ∀ j ∈ G, (q j).pref a b := by
      intro j hj
      by_cases hji : j = i
      · rw [hji, hqi]; exact top3_pref_fst_snd r₀ hab
      · rw [hqG' j hji hj]
        exact top3_pref_snd_trd r₀ (Ne.symm hac) (Ne.symm hbc) hab
    have hsocab : (F q).pref a b := hG a b hab q hGab
    by_cases hsocbc : (F q).pref b c
    · -- `{i}` is almost decisive for `(a, c)`, hence decisive: contradicts minimality
      have hsocac : (F q).pref a c := (F q).pref_trans hsocab hsocbc
      have hAD : AlmostDecisiveFor F {i} a c := by
        intro p hp hp'
        refine (hI p q a c ?_).mpr hsocac
        intro j
        by_cases hji : j = i
        · refine iff_of_true (hp j (by simp [hji])) ?_
          rw [hji, hqi]
          exact top3_pref_fst_trd r₀ hac
        · have hpj : ¬ (p j).pref a c := fun hcon =>
            (p j).pref_asymm hcon (hp' j (by simpa using hji))
          have hqj : ¬ (q j).pref a c := by
            by_cases hjG : j ∈ G
            · rw [hqG' j hji hjG]
              exact (top3 c a b r₀).pref_asymm (top3_pref_fst_snd r₀ (Ne.symm hac))
            · rw [hqout j hjG]
              exact (top3 b c a r₀).pref_asymm
                (top3_pref_snd_trd r₀ hbc (Ne.symm hab) (Ne.symm hac))
          exact iff_of_false hpj hqj
      have hdec : Decisive F ({i} : Finset V) :=
        decisive_of_almostDecisiveFor hU hI h3 hac hAD
      have hle := hmin _ hdec
      rw [Finset.card_singleton] at hle
      omega
    · -- `G.erase i` is almost decisive for `(c, b)`, hence decisive: contradicts minimality
      have hsoccb : (F q).pref c b := by
        rcases (F q).pref_total (Ne.symm hbc) with h' | h'
        · exact h'
        · exact absurd h' hsocbc
      have hAD : AlmostDecisiveFor F (G.erase i) c b := by
        intro p hp hp'
        refine (hI p q c b ?_).mpr hsoccb
        intro j
        by_cases hjG : j ∈ G.erase i
        · have hji : j ≠ i := (Finset.mem_erase.mp hjG).1
          have hjG' : j ∈ G := (Finset.mem_erase.mp hjG).2
          refine iff_of_true (hp j hjG) ?_
          rw [hqG' j hji hjG']
          exact top3_pref_fst_trd r₀ (Ne.symm hbc)
        · have hpj : ¬ (p j).pref c b := fun hcon =>
            (p j).pref_asymm hcon (hp' j hjG)
          have hqj : ¬ (q j).pref c b := by
            by_cases hji : j = i
            · rw [hji, hqi]
              exact (top3 a b c r₀).pref_asymm (top3_pref_snd_trd r₀ hab hac hbc)
            · have hjG' : j ∉ G := fun hmem => hjG (Finset.mem_erase.mpr ⟨hji, hmem⟩)
              rw [hqout j hjG']
              exact (top3 b c a r₀).pref_asymm (top3_pref_fst_snd r₀ hbc)
          exact iff_of_false hpj hqj
      have hdec : Decisive F (G.erase i) :=
        decisive_of_almostDecisiveFor hU hI h3 (Ne.symm hbc) hAD
      have h4 := hmin _ hdec
      have h5 : (G.erase i).card + 1 = G.card := Finset.card_erase_add_one hi
      omega

/-- **Arrow's impossibility theorem.**  With at least three alternatives (`a`, `b`, `c`
pairwise distinct) and finitely many voters, no ranked voting rule `F` is simultaneously
unanimous, independent of irrelevant alternatives, and non-dictatorial. -/
