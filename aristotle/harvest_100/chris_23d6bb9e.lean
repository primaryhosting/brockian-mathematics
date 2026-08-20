/-
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

open Set TopologicalSpace

namespace Frontier

/-!
# Suslin's Problem

A *Suslin line* is a linear order, carrying its order topology, which satisfies the
**countable chain condition** (every family of pairwise disjoint nonempty open sets is
countable) but which is **not separable**.  Since every separable space is ccc
(`Frontier.isCCC_of_separableSpace`), a Suslin line is a space where the ccc fails to
imply separability.

*Suslin's Problem* asks whether every nonempty, ccc, densely ordered, unbounded,
conditionally complete linear order is order-isomorphic to `ℝ`; *Suslin's Hypothesis* is
the assertion that no Suslin line exists.

Both are independent of ZFC: Jensen's diamond principle `◊` implies that a Suslin line
exists, whereas `MA + ¬CH` implies Suslin's Hypothesis.  Consequently neither the
existence nor the nonexistence of a Suslin line is a theorem of ZFC, so neither can be
proved (nor refuted) in Lean's ambient set theory; the independence statements themselves
are assertions about models of ZFC rather than statements in the ZFC-like foundation Lean
formalises.

What *is* a theorem of ZFC, and is proved here, is the precise reduction of Suslin's
Problem to the nonexistence of a *Suslin continuum* (`Frontier.Suslin_line`), whose
mathematical core is Cantor's characterisation of the real line
(`Frontier.nonempty_orderIso_real`): a nonempty separable densely ordered unbounded
conditionally complete linear order is order-isomorphic to `ℝ`.  In particular Suslin's
Hypothesis implies the positive answer to Suslin's Problem, and conversely a positive
answer rules out all *complete* Suslin lines.

Mathlib has no notion of the countable chain condition, no notion of Suslin line, and no
characterisation of `ℝ` as an ordered topological space, so all of this is developed from
scratch here; the Mathlib inputs used are Cantor's isomorphism theorem for countable dense
linear orders (`Order.iso_of_countable_dense`), `exists_countable_dense`, and
`OrderIso.toHomeomorph`.
-/

/-- The **countable chain condition**: every family of pairwise disjoint nonempty open
sets is countable. -/
def IsCCC (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → (∀ U ∈ 𝒰, U.Nonempty) →
    𝒰.PairwiseDisjoint id → 𝒰.Countable

/-- A **Suslin line**: a linear order with its order topology which is ccc but not
separable. -/
def IsSuslinLine (X : Type*) [LinearOrder X] [TopologicalSpace X] : Prop :=
  OrderTopology X ∧ IsCCC X ∧ ¬ SeparableSpace X

/-- A **Suslin continuum**: a nonempty, densely ordered, unbounded, conditionally complete
Suslin line; i.e. a "linear continuum" which is ccc but not separable. -/
def IsSuslinContinuum (X : Type*) [ConditionallyCompleteLinearOrder X]
    [TopologicalSpace X] : Prop :=
  OrderTopology X ∧ DenselyOrdered X ∧ NoMinOrder X ∧ NoMaxOrder X ∧ Nonempty X ∧
    IsCCC X ∧ ¬ SeparableSpace X

/-- **Suslin's Hypothesis**: there is no Suslin line. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type) (_ : LinearOrder X) (_ : TopologicalSpace X), ¬ IsSuslinLine X

/-- **Suslin's Problem** (the positive answer): every nonempty ccc densely ordered
unbounded conditionally complete linear order, with its order topology, is
order-isomorphic to `ℝ`. -/
def SuslinProblem : Prop :=
  ∀ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
    OrderTopology X → DenselyOrdered X → NoMinOrder X → NoMaxOrder X → Nonempty X →
      IsCCC X → Nonempty (X ≃o ℝ)

/-!
## Separability implies the countable chain condition
-/

/-- Every separable space satisfies the countable chain condition: a family of pairwise
disjoint nonempty open sets injects into a countable dense set. -/
theorem isCCC_of_separableSpace (X : Type*) [TopologicalSpace X] [SeparableSpace X] :
    IsCCC X := by
  intro 𝒰 hopen hne hdisj
  obtain ⟨s, hcount, hdense⟩ := exists_countable_dense X
  have hpt : ∀ U : 𝒰, ((U : Set X) ∩ s).Nonempty := fun U =>
    hdense.inter_open_nonempty _ (hopen _ U.2) (hne _ U.2)
  choose f hf using hpt
  haveI : Countable s := hcount.to_subtype
  have hinj : Function.Injective (fun U : 𝒰 => (⟨f U, (hf U).2⟩ : s)) := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ h
    simp only [Subtype.mk.injEq] at h
    by_contra hne'
    have hUV : U ≠ V := by simpa [Subtype.ext_iff] using hne'
    have hdisjUV := hdisj hU hV hUV
    have h1 : f ⟨U, hU⟩ ∈ U := (hf ⟨U, hU⟩).1
    have h2 : f ⟨V, hV⟩ ∈ V := (hf ⟨V, hV⟩).1
    rw [h] at h1
    exact (Set.disjoint_left.mp hdisjUV h1) h2
  exact Set.countable_coe_iff.mp hinj.countable

/-- The real line is not a Suslin line: it is separable, hence ccc and separable. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ := by
  rintro ⟨-, -, hns⟩
  exact hns inferInstance

/-!
## Cantor's characterisation of the real line

Throughout this section `s` is a (topologically) dense subset of a nonempty, densely
ordered, unbounded, conditionally complete linear order `X` with the order topology, and
`g : s ≃o ℚ` is an order isomorphism of `s` with the rationals.  The map `cantorMap g`
sending `x` to `sSup {g d | d ∈ s, d < x}` is then an order isomorphism `X ≃o ℝ`.
-/

section Cantor

variable {X : Type*} [ConditionallyCompleteLinearOrder X] [TopologicalSpace X]
  [OrderTopology X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X] [Nonempty X]
  {s : Set X}

omit [NoMaxOrder X] [Nonempty X] in
theorem exists_mem_lt (hs : Dense s) (x : X) : ∃ d : s, (d : X) < x := by
  obtain ⟨y, hy⟩ := exists_lt x
  obtain ⟨z, hz, _, hz2⟩ := hs.exists_between hy
  exact ⟨⟨z, hz⟩, hz2⟩

omit [NoMinOrder X] [Nonempty X] in
theorem exists_lt_mem (hs : Dense s) (x : X) : ∃ d : s, x < (d : X) := by
  obtain ⟨y, hy⟩ := exists_gt x
  obtain ⟨z, hz, hz1, _⟩ := hs.exists_between hy
  exact ⟨⟨z, hz⟩, hz1⟩

omit [NoMinOrder X] [NoMaxOrder X] [Nonempty X] in
theorem exists_mem_between (hs : Dense s) {x y : X} (h : x < y) :
    ∃ d : s, x < (d : X) ∧ (d : X) < y := by
  obtain ⟨z, hz, hz1, hz2⟩ := hs.exists_between h
  exact ⟨⟨z, hz⟩, hz1, hz2⟩

/-- The map used to identify `X` with `ℝ`: send `x` to the supremum of the values of a
fixed order isomorphism `g : s ≃o ℚ` on the elements of `s` below `x`. -/
noncomputable def cantorMap (g : s ≃o ℚ) (x : X) : ℝ :=
  sSup ((fun d : s => ((g d : ℚ) : ℝ)) '' {d : s | (d : X) < x})

omit [NoMaxOrder X] [Nonempty X] in
theorem cantorMap_setNonempty (hs : Dense s) (g : s ≃o ℚ) (x : X) :
    ((fun d : s => ((g d : ℚ) : ℝ)) '' {d : s | (d : X) < x}).Nonempty := by
  obtain ⟨d, hd⟩ := exists_mem_lt hs x
  exact ⟨_, Set.mem_image_of_mem _ hd⟩

omit [NoMinOrder X] [Nonempty X] in
theorem cantorMap_bddAbove (hs : Dense s) (g : s ≃o ℚ) (x : X) :
    BddAbove ((fun d : s => ((g d : ℚ) : ℝ)) '' {d : s | (d : X) < x}) := by
  obtain ⟨d0, hd0⟩ := exists_lt_mem hs x
  refine ⟨((g d0 : ℚ) : ℝ), ?_⟩
  rintro _ ⟨d, hd, rfl⟩
  have hltX : (d : X) < (d0 : X) := lt_trans hd hd0
  have hlt : d < d0 := hltX
  show ((g d : ℚ) : ℝ) ≤ ((g d0 : ℚ) : ℝ)
  exact_mod_cast (g.lt_iff_lt.mpr hlt).le

omit [Nonempty X] in
/-- `cantorMap g` is strictly monotone. -/
theorem cantorMap_strictMono (hs : Dense s) (g : s ≃o ℚ) : StrictMono (cantorMap g) := by
  intro x y hxy
  obtain ⟨d1, hd1x, hd1y⟩ := exists_mem_between hs hxy
  obtain ⟨d2, hd2a, hd2b⟩ := exists_mem_between hs hd1y
  have h1 : cantorMap g x ≤ ((g d1 : ℚ) : ℝ) := by
    refine csSup_le (cantorMap_setNonempty hs g x) ?_
    rintro _ ⟨d, hd, rfl⟩
    have hltX : (d : X) < (d1 : X) := lt_trans hd hd1x
    have hlt : d < d1 := hltX
    show ((g d : ℚ) : ℝ) ≤ ((g d1 : ℚ) : ℝ)
    exact_mod_cast (g.lt_iff_lt.mpr hlt).le
  have h2 : ((g d2 : ℚ) : ℝ) ≤ cantorMap g y :=
    le_csSup (cantorMap_bddAbove hs g y) (Set.mem_image_of_mem _ hd2b)
  have h3 : ((g d1 : ℚ) : ℝ) < ((g d2 : ℚ) : ℝ) := by
    have hlt : d1 < d2 := hd2a
    exact_mod_cast g.lt_iff_lt.mpr hlt
  linarith

omit [Nonempty X] in
/-- `cantorMap g` is surjective onto `ℝ`: the preimage of `r` is the supremum of the
elements of `s` whose `g`-value is `< r`. -/
theorem cantorMap_surjective (hs : Dense s) (g : s ≃o ℚ) :
    Function.Surjective (cantorMap g) := by
  intro r
  set A : Set X := (fun d : s => (d : X)) '' {d : s | ((g d : ℚ) : ℝ) < r} with hA
  have hAne : A.Nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt r
    exact ⟨_, ⟨g.symm q, by simpa using hq, rfl⟩⟩
  have hAbdd : BddAbove A := by
    obtain ⟨q, hq⟩ := exists_rat_gt r
    refine ⟨((g.symm q : s) : X), ?_⟩
    rintro _ ⟨d, hd, rfl⟩
    have hlt : ((g d : ℚ) : ℝ) < ((q : ℚ) : ℝ) := lt_trans hd hq
    have hq2 : g d < q := by exact_mod_cast hlt
    have hd' : d < g.symm q := by
      have h := g.lt_iff_lt (x := d) (y := g.symm q)
      simp only [OrderIso.apply_symm_apply] at h
      exact h.mp hq2
    exact le_of_lt hd'
  set x : X := sSup A with hx
  refine ⟨x, ?_⟩
  have hle : cantorMap g x ≤ r := by
    refine csSup_le (cantorMap_setNonempty hs g x) ?_
    rintro _ ⟨d, hd, rfl⟩
    have hex : ∃ a ∈ A, (d : X) < a := by
      by_contra hcon
      push_neg at hcon
      exact absurd (csSup_le hAne hcon) (not_le.mpr hd)
    obtain ⟨a, ⟨d', hd', rfl⟩, hlt⟩ := hex
    have hdd' : d < d' := hlt
    have hcast : ((g d : ℚ) : ℝ) < ((g d' : ℚ) : ℝ) := by
      exact_mod_cast g.lt_iff_lt.mpr hdd'
    show ((g d : ℚ) : ℝ) ≤ r
    exact le_of_lt (lt_trans hcast hd')
  have hge : r ≤ cantorMap g x := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hcon
    obtain ⟨q', hq1', hq2'⟩ := exists_rat_btwn hq2
    have hmem : ((g.symm q' : s) : X) ∈ A := ⟨g.symm q', by simpa using hq2', rfl⟩
    have hxle : ((g.symm q' : s) : X) ≤ x := le_csSup hAbdd hmem
    have hqq'Q : q < q' := by exact_mod_cast hq1'
    have hqq' : (g.symm q : s) < g.symm q' := g.symm.lt_iff_lt.mpr hqq'Q
    have hqq'X : ((g.symm q : s) : X) < ((g.symm q' : s) : X) := hqq'
    have hlt : ((g.symm q : s) : X) < x := lt_of_lt_of_le hqq'X hxle
    have hle2 : ((q : ℚ) : ℝ) ≤ cantorMap g x := by
      have h := le_csSup (cantorMap_bddAbove hs g x) (Set.mem_image_of_mem
        (fun d : s => ((g d : ℚ) : ℝ)) hlt)
      simpa using h
    linarith
  linarith [hle, hge]

end Cantor

/-- **Cantor's characterisation of the real line.**  A nonempty separable densely ordered
unbounded conditionally complete linear order, with its order topology, is
order-isomorphic to `ℝ`. -/
theorem nonempty_orderIso_real (X : Type*) [ConditionallyCompleteLinearOrder X]
    [TopologicalSpace X] [OrderTopology X] [DenselyOrdered X] [NoMinOrder X] [NoMaxOrder X]
    [Nonempty X] [SeparableSpace X] : Nonempty (X ≃o ℝ) := by
  obtain ⟨s, hcount, hs⟩ := exists_countable_dense X
  haveI : Countable s := hcount.to_subtype
  haveI : Nonempty s := hs.nonempty.to_subtype
  haveI : DenselyOrdered s := ⟨fun a b hab => by
    obtain ⟨d, h1, h2⟩ := exists_mem_between hs (show (a : X) < (b : X) from hab)
    exact ⟨d, h1, h2⟩⟩
  haveI : NoMinOrder s := ⟨fun a => by
    obtain ⟨b, hb⟩ := exists_lt (a : X)
    obtain ⟨d, _, h2⟩ := exists_mem_between hs hb
    exact ⟨d, h2⟩⟩
  haveI : NoMaxOrder s := ⟨fun a => by
    obtain ⟨b, hb⟩ := exists_gt (a : X)
    obtain ⟨d, h1, _⟩ := exists_mem_between hs hb
    exact ⟨d, h1⟩⟩
  obtain ⟨g⟩ := Order.iso_of_countable_dense s ℚ
  exact ⟨StrictMono.orderIsoOfSurjective _ (cantorMap_strictMono hs g)
    (cantorMap_surjective hs g)⟩

/-- A space order-isomorphic to `ℝ`, in the order topology, is separable. -/
theorem separableSpace_of_orderIso_real {X : Type*} [Preorder X] [TopologicalSpace X]
    [OrderTopology X] (e : X ≃o ℝ) : SeparableSpace X := by
  have h : ℝ ≃ₜ X := (e.toHomeomorph).symm
  exact h.surjective.denseRange.separableSpace h.continuous

/-- Suslin's Hypothesis implies the positive answer to Suslin's Problem. -/
theorem suslinProblem_of_suslinHypothesis : SuslinHypothesis → SuslinProblem := by
  intro hSH X inst1 inst2 hot hd hmin hmax hne hccc
  letI := inst1; letI := inst2; letI := hot; letI := hd
  letI := hmin; letI := hmax; letI := hne
  have hsep : SeparableSpace X := by
    by_contra hns
    exact hSH X inst1.toLinearOrder inst2 ⟨hot, hccc, hns⟩
  exact nonempty_orderIso_real X

/-- Every Suslin continuum is in particular a Suslin line, so the existence of a Suslin
continuum refutes Suslin's Hypothesis. -/
theorem not_suslinHypothesis_of_isSuslinContinuum (X : Type)
    [inst1 : ConditionallyCompleteLinearOrder X] [inst2 : TopologicalSpace X]
    (hX : IsSuslinContinuum X) : ¬ SuslinHypothesis := by
  obtain ⟨hot, -, -, -, -, hccc, hnsep⟩ := hX
  exact fun hSH => hSH X inst1.toLinearOrder inst2 ⟨hot, hccc, hnsep⟩

/-!
## Main theorem
-/

/-- **Suslin's Problem.**  The positive answer to Suslin's Problem — every nonempty ccc
densely ordered unbounded conditionally complete linear order, with its order topology, is
order-isomorphic to `ℝ` — holds if and only if there is no Suslin continuum, i.e. no such
order which fails to be separable.  Moreover Suslin's Hypothesis (there is no Suslin line
at all) implies the positive answer.

This is a theorem of ZFC; whether either side holds is *not* decided by ZFC: Jensen's `◊`
yields a Suslin line, whereas `MA + ¬CH` refutes all of them. -/
theorem Suslin_line :
    (SuslinProblem ↔
      ¬ ∃ (X : Type) (_ : ConditionallyCompleteLinearOrder X) (_ : TopologicalSpace X),
          IsSuslinContinuum X) ∧
    (SuslinHypothesis → SuslinProblem) := by
  refine ⟨⟨?_, ?_⟩, suslinProblem_of_suslinHypothesis⟩
  · rintro hSP ⟨X, inst1, inst2, hot, hd, hmin, hmax, hne, hccc, hnsep⟩
    letI := inst1; letI := inst2; letI := hot
    exact hnsep (separableSpace_of_orderIso_real
      (hSP X inst1 inst2 hot hd hmin hmax hne hccc).some)
  · intro h X inst1 inst2 hot hd hmin hmax hne hccc
    letI := inst1; letI := inst2; letI := hot; letI := hd
    letI := hmin; letI := hmax; letI := hne
    have hsep : SeparableSpace X := by
      by_contra hns
      exact h ⟨X, inst1, inst2, hot, hd, hmin, hmax, hne, hccc, hns⟩
    exact nonempty_orderIso_real X

end Frontier

