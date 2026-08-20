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

import Mathlib

/-!
# Arrow's impossibility theorem

A *ranking* on a type of alternatives `A` is a total, transitive, antisymmetric relation
(a linear order presented as a relation).  A *profile* assigns a ranking to each voter, and a
*ranked voting rule* (social welfare function) aggregates profiles into a single relation.

The main result, `Frontier.arrow_impossibility`, states that whenever there are at least three
alternatives and finitely many voters, no ranked voting rule producing a ranking can
simultaneously satisfy unanimity (Pareto), independence of irrelevant alternatives, and
non-dictatorship.
-/

namespace Frontier

section Defs

variable {A : Type*}

/-- A *ranking* of the alternatives: a total, transitive, antisymmetric relation. -/

lemma exists_localDict (hR : IsRankingRule F) (hU : Unanimity F) (hI : IIA F)
    (b : A) (hb : ∃ x : A, x ≠ b) :
    ∃ d : V, LocalDict F d b := by
  classical
  obtain ⟨x₀, hx₀⟩ := hb
  obtain ⟨r₀, hr₀⟩ := exists_ranking A
  -- `Q S` is the profile in which the voters of `S` put `b` on top and the others at the bottom
  set Q : Finset V → Profile V A := fun S v => if v ∈ S then putTop b r₀ else putBot b r₀
    with hQ_def
  have hQmem : ∀ (S : Finset V) (v : V), v ∈ S → Q S v = putTop b r₀ := by
    intro S v hv; simp only [hQ_def, if_pos hv]
  have hQnot : ∀ (S : Finset V) (v : V), v ∉ S → Q S v = putBot b r₀ := by
    intro S v hv; simp only [hQ_def, if_neg hv]
  have hQprof : ∀ S, IsProfile (Q S) := by
    intro S v
    by_cases hv : v ∈ S
    · rw [hQmem S v hv]; exact isRanking_putTop hr₀ b
    · rw [hQnot S v hv]; exact isRanking_putBot hr₀ b
  -- `P S` says that society puts `b` on top for the profile `Q S`
  set P : Finset V → Prop := fun S => ∀ x, x ≠ b → SPref (F (Q S)) b x with hP_def
  have hP0 : ¬ P ∅ := by
    intro hcon
    have h1 : SPref (F (Q ∅)) x₀ b := by
      refine hU _ (hQprof _) x₀ b fun v => ?_
      rw [hQnot ∅ v (Finset.notMem_empty v)]
      exact spref_putBot hx₀
    exact h1.2 (hcon x₀ hx₀).1
  have hPuniv : P Finset.univ := by
    intro x hx
    refine hU _ (hQprof _) b x fun v => ?_
    rw [hQmem Finset.univ v (Finset.mem_univ v)]
    exact spref_putTop hx
  obtain ⟨T, d, hdT, hnT, hT⟩ := exists_pivotal P hP0 Finset.univ hPuniv
  -- at the pivotal set `T`, society puts `b` at the bottom
  have hbotT : ∀ x, x ≠ b → SPref (F (Q T)) x b := by
    refine (extremal hR hU hI b (Q T) (hQprof T) fun v => ?_).resolve_left hnT
    by_cases hv : v ∈ T
    · exact Or.inl fun x hx => by rw [hQmem T v hv]; exact spref_putTop hx
    · exact Or.inr fun x hx => by rw [hQnot T v hv]; exact spref_putBot hx
  refine ⟨d, ?_⟩
  intro x y hxb hyb hxy p hp hs
  -- the auxiliary profile `q`: the pivotal voter inserts `b` just above `y`,
  -- the voters of `T` put `b` on top, and all the others put `b` at the bottom
  set q : Profile V A := fun v =>
    if v = d then liftAbove b y (p v)
    else if v ∈ T then putTop b (p v) else putBot b (p v) with hq_def
  have hqd : q d = liftAbove b y (p d) := by simp only [hq_def, if_pos rfl]
  have hqT : ∀ v, v ≠ d → v ∈ T → q v = putTop b (p v) := by
    intro v h1 h2; simp only [hq_def, if_neg h1, if_pos h2]
  have hqN : ∀ v, v ≠ d → v ∉ T → q v = putBot b (p v) := by
    intro v h1 h2; simp only [hq_def, if_neg h1, if_neg h2]
  have hqprof : IsProfile q := by
    intro v
    by_cases hv : v = d
    · subst hv; rw [hqd]; exact isRanking_liftAbove (hp v)
    · by_cases hvT : v ∈ T
      · rw [hqT v hv hvT]; exact isRanking_putTop (hp v) b
      · rw [hqN v hv hvT]; exact isRanking_putBot (hp v) b
  -- society ranks `x` above `b`
  have hpair₁ : ∀ v, (Q T v x b ↔ q v x b) ∧ (Q T v b x ↔ q v b x) := by
    intro v
    by_cases hv : v = d
    · subst hv
      refine spref_pair_iff ?_ ?_
      · rw [hQnot T v hdT]; exact spref_putBot hxb
      · rw [hqd]; exact spref_liftAbove_of_spref hxb hs
    · by_cases hvT : v ∈ T
      · refine spref_pair_iff' ?_ ?_
        · rw [hQmem T v hvT]; exact spref_putTop hxb
        · rw [hqT v hv hvT]; exact spref_putTop hxb
      · refine spref_pair_iff ?_ ?_
        · rw [hQnot T v hvT]; exact spref_putBot hxb
        · rw [hqN v hv hvT]; exact spref_putBot hxb
  have hxb' : SPref (F q) x b :=
    iia_spref hI (hQprof T) hqprof x b (fun v => (hpair₁ v).1) (fun v => (hpair₁ v).2)
      (hbotT x hxb)
  -- society ranks `b` above `y`
  have hpair₂ : ∀ v, (Q (insert d T) v b y ↔ q v b y) ∧ (Q (insert d T) v y b ↔ q v y b) := by
    intro v
    by_cases hv : v = d
    · subst hv
      refine spref_pair_iff ?_ ?_
      · rw [hQmem _ v (Finset.mem_insert_self v T)]; exact spref_putTop hyb
      · rw [hqd]; exact spref_liftAbove_self (hp v) (Ne.symm hyb)
    · by_cases hvT : v ∈ T
      · refine spref_pair_iff ?_ ?_
        · rw [hQmem _ v (Finset.mem_insert_of_mem hvT)]; exact spref_putTop hyb
        · rw [hqT v hv hvT]; exact spref_putTop hyb
      · have hvI : v ∉ insert d T := by
          simp only [Finset.mem_insert]
          push_neg
          exact ⟨hv, hvT⟩
        refine spref_pair_iff' ?_ ?_
        · rw [hQnot _ v hvI]; exact spref_putBot hyb
        · rw [hqN v hv hvT]; exact spref_putBot hyb
  have hby' : SPref (F q) b y :=
    iia_spref hI (hQprof _) hqprof b y (fun v => (hpair₂ v).1) (fun v => (hpair₂ v).2)
      (hT y hyb)
  have hxy' : SPref (F q) x y := spref_trans (hR q hqprof) hxb' hby'
  -- transfer back to the original profile: the pair `x, y` was never touched
  have hpair₃ : ∀ v, (q v x y ↔ p v x y) ∧ (q v y x ↔ p v y x) := by
    intro v
    by_cases hv : v = d
    · subst hv
      rw [hqd]
      exact ⟨liftAbove_of_ne hxb hyb, liftAbove_of_ne hyb hxb⟩
    · by_cases hvT : v ∈ T
      · rw [hqT v hv hvT]
        exact ⟨putTop_of_ne hxb hyb, putTop_of_ne hyb hxb⟩
      · rw [hqN v hv hvT]
        exact ⟨putBot_of_ne hxb hyb, putBot_of_ne hyb hxb⟩
  exact iia_spref hI hqprof hp x y (fun v => (hpair₃ v).1) (fun v => (hpair₃ v).2) hxy'

omit [Fintype V] in
/-- Two voters decisive over overlapping pairs of distinct alternatives coincide. -/
