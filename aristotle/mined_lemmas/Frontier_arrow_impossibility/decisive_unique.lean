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

lemma decisive_unique (hR : IsRankingRule F) (hU : Unanimity F)
    {d₁ d₂ : V} {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h1 : Decisive F d₁ x y) (h2 : Decisive F d₂ y z) : d₁ = d₂ := by
  by_contra hne
  classical
  obtain ⟨r₀, hr₀⟩ := exists_ranking A
  -- `R₁` ranks `z > x > y`, `R₂` ranks `y > z > x`
  set R₁ : A → A → Prop := putTop z (putTop x (putTop y r₀)) with hR₁
  set R₂ : A → A → Prop := putTop y (putTop z (putTop x r₀)) with hR₂
  have hR₁rank : IsRanking R₁ :=
    isRanking_putTop (isRanking_putTop (isRanking_putTop hr₀ y) x) z
  have hR₂rank : IsRanking R₂ :=
    isRanking_putTop (isRanking_putTop (isRanking_putTop hr₀ x) z) y
  have hR₁zx : SPref R₁ z x := spref_putTop hxz
  have hR₁xy : SPref R₁ x y := spref_putTop_of_ne hxz hyz (spref_putTop (Ne.symm hxy))
  have hR₂yz : SPref R₂ y z := spref_putTop (Ne.symm hyz)
  have hR₂zx : SPref R₂ z x := spref_putTop_of_ne (Ne.symm hyz) hxy (spref_putTop hxz)
  set q : Profile V A := fun v => if v = d₂ then R₂ else R₁ with hq_def
  have hqval : ∀ v, (v = d₂ → q v = R₂) ∧ (v ≠ d₂ → q v = R₁) := by
    intro v
    exact ⟨fun hv => if_pos hv, fun hv => if_neg hv⟩
  have hq : IsProfile q := by
    intro v
    by_cases hv : v = d₂
    · rw [(hqval v).1 hv]; exact hR₂rank
    · rw [(hqval v).2 hv]; exact hR₁rank
  have hxy' : SPref (F q) x y := h1 q hq (by rw [(hqval d₁).2 hne]; exact hR₁xy)
  have hyz' : SPref (F q) y z := h2 q hq (by rw [(hqval d₂).1 rfl]; exact hR₂yz)
  have hzx' : SPref (F q) z x := by
    refine hU q hq z x fun v => ?_
    by_cases hv : v = d₂
    · rw [(hqval v).1 hv]; exact hR₂zx
    · rw [(hqval v).2 hv]; exact hR₁zx
  exact hzx'.2 (spref_trans (hR q hq) hxy' hyz').1

omit [Fintype V] in
/-- Local dictators for different alternatives coincide. -/
