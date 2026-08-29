/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set TopologicalSpace

namespace Frontier

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/
def IsCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → (∀ U ∈ 𝒰, U.Nonempty) →
    𝒰.PairwiseDisjoint id → 𝒰.Countable

/-- A **Suslin line**: a densely ordered linear order without endpoints, equipped with its
order topology, which satisfies the countable chain condition but is not separable.
(The real line satisfies every clause except the last one: it *is* separable.) -/
structure IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] : Prop where
  orderTopology : OrderTopology X
  denselyOrdered : DenselyOrdered X
  noMinOrder : NoMinOrder X
  noMaxOrder : NoMaxOrder X
  ccc : IsCCC X
  not_separable : ¬ SeparableSpace X

/-- **Suslin's Hypothesis** (SH): there is no Suslin line. Suslin's problem asks whether SH is
provable; it is in fact independent of ZFC (♦ implies the existence of a Suslin line, while
MA + ¬CH implies SH). -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type u) [LinearOrder X] [TopologicalSpace X], ¬ IsSuslinLine X

/-- Every separable space satisfies the countable chain condition. -/
theorem isCCC_of_separableSpace (X : Type u) [TopologicalSpace X] [SeparableSpace X] :
    IsCCC X := by
  intro 𝒰 hopen hne hdisj
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  choose f hf using fun (U : Set X) (hU : U ∈ 𝒰) =>
    hDd.inter_open_nonempty U (hopen U hU) (hne U hU)
  rw [← Set.countable_coe_iff]
  have : Countable D := hDc.to_subtype
  refine Function.Injective.countable
    (f := fun U : 𝒰 => (⟨f U.1 U.2, (hf U.1 U.2).2⟩ : D)) ?_
  rintro ⟨U, hU⟩ ⟨V, hV⟩ h
  simp only [Subtype.mk.injEq] at h ⊢
  by_contra hUV
  have hd : Disjoint U V := hdisj hU hV hUV
  refine Set.not_disjoint_iff.2 ⟨f U hU, (hf U hU).1, ?_⟩ hd
  exact h ▸ (hf V hV).1

/-- If a linearly ordered space with the order topology has a countable subset that is dense
in the order sense, then it is separable. -/
theorem separableSpace_of_countable_orderDense {X : Type u} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] {D : Set X} (hD : D.Countable)
    (h : ∀ a b : X, a < b → ∃ d ∈ D, a < d ∧ d < b) : SeparableSpace X := by
  rcases subsingleton_or_nontrivial X with hX | hX
  · exact ⟨⟨univ, Set.subsingleton_univ.countable, dense_univ⟩⟩
  · exact ⟨⟨D, hD, dense_of_exists_between fun _ _ hab => h _ _ hab⟩⟩

/-- A Suslin line has no countable order-dense subset: this is the classical combinatorial
reformulation of non-separability for a dense linear order. -/
theorem IsSuslinLine.no_countable_orderDense {X : Type u} [LinearOrder X] [TopologicalSpace X]
    (hX : IsSuslinLine X) :
    ¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ d ∈ D, a < d ∧ d < b := by
  rintro ⟨D, hDc, hD⟩
  haveI := hX.orderTopology
  exact hX.not_separable (separableSpace_of_countable_orderDense hDc hD)

/-- A Suslin line is not second countable. -/
theorem IsSuslinLine.not_secondCountable {X : Type u} [LinearOrder X] [TopologicalSpace X]
    (hX : IsSuslinLine X) : ¬ SecondCountableTopology X := by
  intro h
  exact hX.not_separable (by infer_instance)

/-- A Suslin line is uncountable. -/
theorem IsSuslinLine.not_countable {X : Type u} [LinearOrder X] [TopologicalSpace X]
    (hX : IsSuslinLine X) : ¬ Countable X := by
  intro h
  exact hX.not_separable ⟨⟨univ, Set.countable_univ, dense_univ⟩⟩

/-- The real line is not a Suslin line. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := fun h => h.not_separable inferInstance

/--
**Suslin's problem, formalized, together with the ZFC-provable reductions.**

1. Every separable space is ccc; hence "ccc" is a genuine weakening of "separable", and a
   Suslin line is exactly a dense linear order without endpoints (with the order topology)
   witnessing that the weakening is strict.
2. The real line is *not* a Suslin line (it is separable), so Suslin's problem really asks
   whether separability can be dropped from the classical order characterization of `ℝ`.
3. A Suslin line has no countable order-dense subset, is not second countable, and is
   uncountable.
4. Suslin's Hypothesis is equivalent to the statement that every ccc densely ordered linear
   order without endpoints, with its order topology, is separable.

(Whether a Suslin line exists is independent of ZFC: ♦ yields one, MA + ¬CH refutes all of
them; so no proof in ZFC can settle Suslin's Hypothesis either way.)
-/
theorem Suslin_line :
    (∀ (X : Type u) [TopologicalSpace X] [SeparableSpace X], IsCCC X) ∧
    ¬ IsSuslinLine ℝ ∧
    (∀ (X : Type u) [LinearOrder X] [TopologicalSpace X], IsSuslinLine X →
      (¬ ∃ D : Set X, D.Countable ∧ ∀ a b : X, a < b → ∃ d ∈ D, a < d ∧ d < b) ∧
        ¬ SecondCountableTopology X ∧ ¬ Countable X) ∧
    (SuslinHypothesis.{u} ↔
      ∀ (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        DenselyOrdered X → NoMinOrder X → NoMaxOrder X → IsCCC X → SeparableSpace X) := by
  refine ⟨fun X _ _ => isCCC_of_separableSpace X, not_isSuslinLine_real,
    fun X _ _ hX => ⟨hX.no_countable_orderDense, hX.not_secondCountable, hX.not_countable⟩, ?_⟩
  constructor
  · intro hSH X _ _ _ hdense hmin hmax hccc
    by_contra hsep
    exact hSH X ⟨‹OrderTopology X›, hdense, hmin, hmax, hccc, hsep⟩
  · intro h X _ _ hX
    haveI := hX.orderTopology
    exact hX.not_separable
      (h X hX.denselyOrdered hX.noMinOrder hX.noMaxOrder hX.ccc)

end Frontier

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

