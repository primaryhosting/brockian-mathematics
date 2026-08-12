import Mathlib

/-!
# Suslin Line
Category: Frontier — Set Theory
Target: Frontier.Suslin_line
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Classical

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace Frontier

open Set TopologicalSpace

universe u

/-- The **countable chain condition** (ccc): every family of pairwise disjoint nonempty open
sets is countable. -/
def IsCCC (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → (∀ U ∈ 𝒰, U.Nonempty) →
    (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, U ≠ V → Disjoint U V) → 𝒰.Countable

/-- A **Suslin line**: a linearly ordered topological space (with the order topology) which
satisfies the countable chain condition but is not separable. -/
def IsSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] : Prop :=
  IsCCC X ∧ ¬ SeparableSpace X

/-- The classical ("dense") form of a Suslin line: additionally the order is dense in itself and
has no endpoints. -/
def IsDenseSuslinLine (X : Type u) [LinearOrder X] [TopologicalSpace X] [OrderTopology X] :
    Prop :=
  IsSuslinLine X ∧ DenselyOrdered X ∧ NoMinOrder X ∧ NoMaxOrder X

/-- **Suslin's Hypothesis** (SH): there is no Suslin line, i.e. every ccc linearly ordered
topological space is separable.  This statement is independent of ZFC:  Jensen showed that
Jensen's diamond principle `◊` (which holds in `L`) implies the existence of a Suslin line, hence
`¬ SH`, while Solovay and Tennenbaum showed that `MA + ¬CH` implies `SH`. -/
def SuslinHypothesis : Prop :=
  ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X], ¬ IsSuslinLine X

/-! ## Separability implies ccc -/

/-- Every separable space satisfies the countable chain condition. -/
theorem isCCC_of_separableSpace (X : Type u) [TopologicalSpace X] [SeparableSpace X] :
    IsCCC X := by
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense X
  intro 𝒰 hopen hne hdisj
  have hpt : ∀ U : 𝒰, ∃ d : D, (d : X) ∈ (U : Set X) := by
    rintro ⟨U, hU⟩
    obtain ⟨d, hdD, hdU⟩ := hDd.exists_mem_open (hopen U hU) (hne U hU)
    exact ⟨⟨d, hdD⟩, hdU⟩
  choose f hf using hpt
  haveI : Countable D := hDc.to_subtype
  have hinj : Function.Injective f := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ h
    by_contra hne'
    have hUV : U ≠ V := by
      intro h'; exact hne' (Subtype.ext h')
    have hd := hdisj U hU V hV hUV
    have h1 : (f ⟨U, hU⟩ : X) ∈ U := hf ⟨U, hU⟩
    have h2 : (f ⟨U, hU⟩ : X) ∈ V := by
      rw [h]; exact hf ⟨V, hV⟩
    exact (hd.le_bot ⟨h1, h2⟩ : _)
  haveI : Countable 𝒰 := hinj.countable
  exact Set.countable_coe_iff.mp inferInstance

/-! ## Basic consequences for Suslin lines -/

variable {X : Type u} [LinearOrder X] [TopologicalSpace X] [OrderTopology X]

/-- A Suslin line in the classical (dense, endpointless) sense is in particular a Suslin line. -/
theorem isSuslinLine_of_isDenseSuslinLine (h : IsDenseSuslinLine X) : IsSuslinLine X := h.1

/-- A separable linear order is not a Suslin line. -/
theorem not_isSuslinLine_of_separableSpace [SeparableSpace X] : ¬ IsSuslinLine X := by
  rintro ⟨-, h⟩
  exact h ‹SeparableSpace X›

/-- A Suslin line is uncountable. -/
theorem uncountable_of_isSuslinLine (h : IsSuslinLine X) : Uncountable X := by
  rw [← not_countable_iff]
  intro hc
  haveI : Countable X := hc
  exact h.2 ⟨⟨Set.univ, Set.countable_univ, dense_univ⟩⟩

/-- A Suslin line is not second countable. -/
theorem not_secondCountable_of_isSuslinLine (h : IsSuslinLine X) :
    ¬ SecondCountableTopology X := by
  intro hsc
  exact h.2 (by haveI := hsc; infer_instance)

/-- The real line is not a Suslin line. -/
theorem not_isSuslinLine_real : ¬ IsSuslinLine ℝ :=
  not_isSuslinLine_of_separableSpace

/-- The rationals do not form a Suslin line. -/
theorem not_isSuslinLine_rat : ¬ IsSuslinLine ℚ :=
  not_isSuslinLine_of_separableSpace

/-! ## The base case of the reduction of a Suslin line to a Suslin tree -/

/-- **Base step of the Suslin-tree construction.**  In a densely ordered Suslin line, for every
countable set `C` there is a nonempty open interval avoiding `C`.  (Iterating this along `ω₁` is
the classical construction of a Suslin tree from a Suslin line.) -/
theorem exists_Ioo_disjoint_of_countable [DenselyOrdered X]
    (h : IsSuslinLine X) {C : Set X} (hC : C.Countable) :
    ∃ a b : X, a < b ∧ (Set.Ioo a b).Nonempty ∧ Disjoint (Set.Ioo a b) C := by
  haveI : Uncountable X := uncountable_of_isSuslinLine h
  haveI : Nontrivial X := by
    rcases exists_pair_ne X with ⟨x, y, hxy⟩
    exact ⟨x, y, hxy⟩
  have hnd : ¬ Dense C := by
    intro hd
    exact h.2 ⟨⟨C, hC, hd⟩⟩
  -- the complement of the closure of `C` is a nonempty open set
  have hopen : IsOpen (closure C)ᶜ := isClosed_closure.isOpen_compl
  have hnonempty : ((closure C)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hcl
    exact hnd (dense_iff_closure_eq.mpr hcl)
  obtain ⟨a, b, hab, hsub⟩ := hopen.exists_Ioo_subset hnonempty
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact Set.nonempty_Ioo.mpr hab
  · refine Set.disjoint_left.mpr fun x hx hxC => ?_
    exact hsub hx (subset_closure hxC)

/-! ## A left-separated `ω₁`-sequence in any non-separable space

The classical construction of a Suslin tree from a Suslin line proceeds by transfinite recursion
of length `ω₁`, at each step using non-separability to find a point (indeed an interval) outside
the closure of what has been chosen so far.  We carry out this recursion here. -/

open Classical in
/-- The transfinite sequence obtained by repeatedly choosing, if possible, a point outside the
closure of the previously chosen points. -/
noncomputable def leftSepSeq (Y : Type u) [TopologicalSpace Y] [Nonempty Y] :
    Ordinal.{u} → Y
  | a => if h : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) then
      h.choose else Classical.arbitrary Y
  termination_by a => a
  decreasing_by all_goals exact b.2

open Classical in
theorem leftSepSeq_def (Y : Type u) [TopologicalSpace Y] [Nonempty Y] (a : Ordinal.{u}) :
    leftSepSeq Y a =
      if h : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) then
        h.choose else Classical.arbitrary Y := by
  rw [leftSepSeq]

/-- Initial segments of `ω₁` are countable. -/
theorem countable_Iio_of_lt_ord_aleph_one {a : Ordinal.{u}} (ha : a < (Cardinal.aleph 1).ord) :
    (Set.Iio a).Countable := by
  rw [Cardinal.countable_iff_lt_aleph_one, Ordinal.mk_Iio_ordinal]
  have h := Cardinal.lt_ord.mp ha
  calc Cardinal.lift.{u + 1, u} a.card
      < Cardinal.lift.{u + 1, u} (Cardinal.aleph 1) := Cardinal.lift_lt.mpr h
    _ = Cardinal.aleph 1 := by simp

/-- In a non-separable space the recursion never gets stuck: each `leftSepSeq Y a` with `a < ω₁`
lies outside the closure of its predecessors. -/
theorem leftSepSeq_notMem_closure (Y : Type u) [TopologicalSpace Y] [Nonempty Y]
    (hns : ¬ SeparableSpace Y) {a : Ordinal.{u}} (ha : a < (Cardinal.aleph 1).ord) :
    leftSepSeq Y a ∉ closure (leftSepSeq Y '' Set.Iio a) := by
  haveI : Countable (Set.Iio a) := (countable_Iio_of_lt_ord_aleph_one ha).to_subtype
  have hex : ∃ x : Y, x ∉ closure (Set.range (fun b : Set.Iio a => leftSepSeq Y b.1)) := by
    by_contra hall
    push_neg at hall
    refine hns ⟨⟨Set.range (fun b : Set.Iio a => leftSepSeq Y b.1), Set.countable_range _, ?_⟩⟩
    exact dense_iff_closure_eq.mpr (Set.eq_univ_of_forall hall)
  have himg : leftSepSeq Y '' Set.Iio a = Set.range (fun b : Set.Iio a => leftSepSeq Y b.1) := by
    rw [Set.image_eq_range]
  rw [himg, leftSepSeq_def Y a, dif_pos hex]
  exact hex.choose_spec

/-- **Left-separated `ω₁`-sequence.**  Every non-separable topological space admits an injective
`ω₁`-sequence of points, each lying outside the closure of its predecessors.  Applied to a Suslin
line this is the skeleton of the classical construction of a Suslin tree. -/
theorem exists_leftSeparated_omega1 (Y : Type u) [TopologicalSpace Y] [Nonempty Y]
    (hns : ¬ SeparableSpace Y) :
    ∃ f : Ordinal.{u} → Y,
      (∀ a < (Cardinal.aleph 1).ord, f a ∉ closure (f '' Set.Iio a)) ∧
        Set.InjOn f (Set.Iio (Cardinal.aleph 1).ord) := by
  refine ⟨leftSepSeq Y, fun a ha => leftSepSeq_notMem_closure Y hns ha, ?_⟩
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact leftSepSeq_notMem_closure Y hns hb
      (subset_closure ⟨a, h, hab⟩)
  · exact leftSepSeq_notMem_closure Y hns ha
      (subset_closure ⟨b, h, hab.symm⟩)

/-- A Suslin line carries a left-separated `ω₁`-sequence. -/
theorem exists_leftSeparated_omega1_of_isSuslinLine {Y : Type u} [LinearOrder Y]
    [TopologicalSpace Y] [OrderTopology Y] (h : IsSuslinLine Y) :
    ∃ f : Ordinal.{u} → Y,
      (∀ a < (Cardinal.aleph 1).ord, f a ∉ closure (f '' Set.Iio a)) ∧
        Set.InjOn f (Set.Iio (Cardinal.aleph 1).ord) := by
  haveI : Uncountable Y := uncountable_of_isSuslinLine h
  haveI : Nonempty Y := inferInstance
  exact exists_leftSeparated_omega1 Y h.2

/-! ## Precise form of Suslin's problem -/

/-- Suslin's Hypothesis says exactly that every ccc linearly ordered topological space is
separable. -/
theorem suslinHypothesis_iff :
    SuslinHypothesis ↔
      ∀ (X : Type) [LinearOrder X] [TopologicalSpace X] [OrderTopology X],
        IsCCC X → SeparableSpace X := by
  constructor
  · intro h X _ _ _ hccc
    by_contra hsep
    exact h X ⟨hccc, hsep⟩
  · intro h X _ _ _ hS
    exact hS.2 (h X hS.1)

/-- The failure of Suslin's Hypothesis is exactly the existence of a ccc non-separable linearly
ordered topological space. -/
theorem not_suslinHypothesis_iff :
    ¬ SuslinHypothesis ↔
      ∃ (X : Type) (_ : LinearOrder X) (t : TopologicalSpace X),
        ∃ _ : @OrderTopology X t _, @IsCCC X t ∧ ¬ @SeparableSpace X t := by
  constructor
  · intro h
    by_contra hex
    apply h
    intro X _ _ _ hS
    exact hex ⟨X, ‹_›, ‹_›, ‹_›, hS.1, hS.2⟩
  · rintro ⟨X, lo, t, ot, hccc, hsep⟩ h
    exact @h X lo t ot ⟨hccc, hsep⟩

/-- **Reduction schema for `◊`-type hypotheses.**  Any principle `P` which produces a ccc
non-separable linearly ordered topological space refutes Suslin's Hypothesis; conversely any
principle implied by `SH` is consistent with `SH`.  This is the shape of Jensen's theorem
`◊ → ¬ SH`. -/
theorem not_suslinHypothesis_of_provides_line (P : Prop) (hP : P)
    (h : P → ∃ (X : Type) (lo : LinearOrder X) (t : TopologicalSpace X),
      ∃ _ : @OrderTopology X t _, @IsSuslinLine X lo t ‹_›) :
    ¬ SuslinHypothesis := by
  obtain ⟨X, lo, t, ot, hS⟩ := h hP
  intro hSH
  exact hSH X hS

/-! ## Main statement -/

/-- **Suslin's problem, formalized.**  We record:
1. every separable space is ccc (so a Suslin line is precisely a ccc, non-separable linear order);
2. Suslin's Hypothesis is equivalent to "every ccc LOTS is separable";
3. its negation is precisely the existence of a Suslin line;
4. the real line is not a Suslin line, and every Suslin line is uncountable and not second
   countable;
5. the base step of the reduction of a Suslin line to a Suslin tree: in a dense Suslin line every
   countable set misses a nonempty open interval;
6. the transfinite form of that step: every Suslin line carries an injective, left-separated
   `ω₁`-sequence. -/
theorem Suslin_line :
    (∀ (Y : Type) [TopologicalSpace Y], SeparableSpace Y → IsCCC Y) ∧
    (SuslinHypothesis ↔
      ∀ (Y : Type) [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y],
        IsCCC Y → SeparableSpace Y) ∧
    (¬ SuslinHypothesis ↔
      ∃ (Y : Type) (_ : LinearOrder Y) (t : TopologicalSpace Y),
        ∃ _ : @OrderTopology Y t _, @IsCCC Y t ∧ ¬ @SeparableSpace Y t) ∧
    ¬ IsSuslinLine ℝ ∧
    (∀ (Y : Type) [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y],
      IsSuslinLine Y → Uncountable Y ∧ ¬ SecondCountableTopology Y) ∧
    (∀ (Y : Type) [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y] [DenselyOrdered Y],
      IsSuslinLine Y → ∀ C : Set Y, C.Countable →
        ∃ a b : Y, a < b ∧ (Set.Ioo a b).Nonempty ∧ Disjoint (Set.Ioo a b) C) ∧
    (∀ (Y : Type) [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y], IsSuslinLine Y →
      ∃ f : Ordinal.{0} → Y,
        (∀ a < (Cardinal.aleph 1).ord, f a ∉ closure (f '' Set.Iio a)) ∧
          Set.InjOn f (Set.Iio (Cardinal.aleph 1).ord)) := by
  refine ⟨fun Y _ hs => by haveI := hs; exact isCCC_of_separableSpace Y,
    suslinHypothesis_iff, not_suslinHypothesis_iff, not_isSuslinLine_real,
    fun Y _ _ _ h => ⟨uncountable_of_isSuslinLine h, not_secondCountable_of_isSuslinLine h⟩,
    fun Y _ _ _ _ h C hC => exists_Ioo_disjoint_of_countable h hC,
    fun Y _ _ _ h => exists_leftSeparated_omega1_of_isSuslinLine h⟩

end Frontier

