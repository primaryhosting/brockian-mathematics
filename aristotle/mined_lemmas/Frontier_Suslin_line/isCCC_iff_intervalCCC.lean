import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Suslin's problem

Cantor characterised the real line as (up to order isomorphism) the unique nonempty complete
dense linear order without endpoints which is *separable*.  Suslin asked whether "separable"
can be weakened to the *countable chain condition* (ccc): every family of pairwise disjoint
nonempty open sets is countable.  A counterexample — a ccc, non-separable dense linear order
without endpoints, equipped with its order topology — is called a **Suslin line**, and
**Suslin's Hypothesis** (`SuslinHypothesis`) is the assertion that no Suslin line exists.

Suslin's Hypothesis is independent of ZFC (Jech, Tennenbaum, Solovay–Tennenbaum): Jensen's
diamond principle `◊` implies that a Suslin line exists, while `MA + ¬CH` implies that none
does.  Neither implication can be settled inside ZFC alone, so neither `SuslinHypothesis`
nor its negation is provable here.  What this file does is:

* give a precise formalisation of the notions involved (`IsCellularFamily`, `IsCCC`,
  `IsSuslinLine`, `SuslinHypothesis`);
* prove that Suslin's Hypothesis is *equivalent* to the classical topological statement
  "every ccc dense linear order without endpoints is separable";
* prove a **Lean-checked reduction** of Suslin's problem to a purely order-theoretic
  (topology-free) statement: every dense linear order without endpoints all of whose
  families of pairwise disjoint nonempty open intervals are countable has a countable
  order-dense subset;
* prove the *base case*: separable spaces are ccc, so a Suslin line is exactly a
  counterexample to the converse; in particular `ℝ` is not a Suslin line, and no Suslin
  line is countable, second countable, or topologically embeddable in `ℝ`.
-/

namespace Frontier

open Set TopologicalSpace Topology

universe u

/-- A *cellular family* in a topological space: a family of pairwise disjoint nonempty
open sets. -/

theorem isCCC_iff_intervalCCC [DenselyOrdered X] [Nontrivial X] :
    IsCCC X ↔ IntervalCCC X := by
  constructor
  · intro hccc s hlt hdisj
    have hcard : ((fun p : X × X => Ioo p.1 p.2) '' s).Countable := by
      refine hccc _ ⟨?_, ?_, ?_⟩
      · rintro _ ⟨p, hp, rfl⟩
        exact isOpen_Ioo
      · rintro _ ⟨p, hp, rfl⟩
        exact nonempty_Ioo.2 (hlt p hp)
      · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ hne
        exact hdisj hp hq (by rintro rfl; exact hne rfl)
    refine Set.countable_of_injective_of_countable_image
      (f := fun p : X × X => Ioo p.1 p.2) ?_ hcard
    intro p hp q hq h
    by_contra hpq
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 (hlt p hp)
    exact Set.disjoint_left.mp (hdisj hp hq hpq) hx (h ▸ hx)
  · rintro hI 𝒰 ⟨hopen, hne, hdisj⟩
    have hch : ∀ U ∈ 𝒰, ∃ p : X × X, p.1 < p.2 ∧ Ioo p.1 p.2 ⊆ U := by
      intro U hU
      obtain ⟨a, b, hab, hsub⟩ := (hopen U hU).exists_Ioo_subset (hne U hU)
      exact ⟨(a, b), hab, hsub⟩
    choose! f hf1 hf2 using hch
    have hs : (f '' 𝒰).Countable := by
      refine hI _ ?_ ?_
      · rintro _ ⟨U, hU, rfl⟩
        exact hf1 U hU
      · rintro _ ⟨U, hU, rfl⟩ _ ⟨V, hV, rfl⟩ hne'
        exact Set.disjoint_of_subset (hf2 U hU) (hf2 V hV)
          (hdisj hU hV (by rintro rfl; exact hne' rfl))
    refine Set.countable_of_injective_of_countable_image (f := f) ?_ hs
    intro U hU V hV h
    by_contra hUV
    obtain ⟨x, hx⟩ := nonempty_Ioo.2 (hf1 U hU)
    have hx' : x ∈ Ioo (f V).1 (f V).2 := by rw [← h]; exact hx
    exact Set.disjoint_left.mp (hdisj hU hV hUV) (hf2 U hU hx) (hf2 V hV hx')

end Reduction

/-- Suslin's Hypothesis, stated topologically: every ccc dense linear order without
endpoints, with its order topology, is separable. -/
