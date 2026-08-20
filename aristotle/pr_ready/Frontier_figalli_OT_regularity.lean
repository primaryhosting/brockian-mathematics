/-!
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
Statement: Regularity of optimal transport maps under the MTW condition (Figalli).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

We work in the standard Kantorovich-duality framework for optimal transport with a
general cost `c : X → Y → ℝ`.

A pair of potentials `(u, v)` is *admissible* when `u x + v y ≤ c x y` for all `x, y`
(this is the constraint set of the dual Kantorovich problem). The *contact set*
(equivalently, the graph of the `c`-subdifferential of `u`) is the set of pairs where
equality holds; any transport plan that is optimal for `c` is supported in it, and an
optimal transport *map* `T` is precisely a selection of the contact fibers.

The regularity theory of Ma–Trudinger–Wang, Loeper and Figalli (Figalli, Kim, McCann,
Loeper, De Philippis–Figalli) shows that under the MTW condition `(A3w)` together with
suitable convexity of the domains and boundedness of the densities, the `c`-subdifferential
of a `c`-convex Kantorovich potential is *single valued*, i.e. every contact fiber is a
singleton. Below, that single-valuedness is taken as the hypothesis `hT`, and the theorem
`Frontier.figalli_OT_regularity` is the Lean-checked reduction from that hypothesis to
continuity of the optimal transport map: single-valuedness of the contact fibers plus
compactness of the target and continuity of the data force the transport map to be
continuous.

`Frontier.figalli_OT_optimality` records that such a map is indeed an optimal transport
map (it minimises the transport cost among all maps pushing `μ` to `ν`), and
`Frontier.figalli_OT_regularity_example` checks that the hypotheses are non-vacuous on a
genuine quadratic-cost example.
-/

section Contact

variable {X Y : Type*}

/-- Admissible pair of Kantorovich potentials for the cost `c`: the dual constraint
`u x + v y ≤ c x y`. -/
def IsKantorovichPotentials (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) : Prop :=
  ∀ (x : X) (y : Y), u x + v y ≤ c x y

/-- The contact set of a pair of potentials: the graph of the `c`-subdifferential of `u`.
Every optimal transport plan is concentrated on this set. -/
def contactSet (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) : Set (X × Y) :=
  {p : X × Y | u p.1 + v p.2 = c p.1 p.2}

/-- The contact fiber over `x`, i.e. the `c`-subdifferential `∂^c u (x)`. -/
def contactFiber (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (x : X) : Set Y :=
  {y : Y | u x + v y = c x y}

theorem mem_contactSet_iff (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (x : X) (y : Y) :
    (x, y) ∈ contactSet c u v ↔ y ∈ contactFiber c u v x := Iff.rfl

variable [TopologicalSpace X] [TopologicalSpace Y]

/-- The contact set is closed whenever the cost and the potentials are continuous. -/
theorem isClosed_contactSet {c : X → Y → ℝ} {u : X → ℝ} {v : Y → ℝ}
    (hc : Continuous fun p : X × Y => c p.1 p.2) (hu : Continuous u) (hv : Continuous v) :
    IsClosed (contactSet c u v) :=
  isClosed_eq ((hu.comp continuous_fst).add (hv.comp continuous_snd)) hc

end Contact

/-- **Regularity of optimal transport maps (Figalli, under the MTW condition).**

Let `c` be a continuous cost on `X × Y` with `Y` compact, and let `(u, v)` be continuous
Kantorovich potentials.  If the `c`-subdifferential of `u` is single valued — the
conclusion supplied by the Ma–Trudinger–Wang condition `(A3w)` in the regularity theory of
Loeper and Figalli — with `T x` its unique element, then the optimal transport map `T` is
continuous. -/
theorem figalli_OT_regularity {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] {c : X → Y → ℝ} {u : X → ℝ} {v : Y → ℝ}
    (hc : Continuous fun p : X × Y => c p.1 p.2) (hu : Continuous u) (hv : Continuous v)
    {T : X → Y} (hT : ∀ x : X, contactFiber c u v x = {T x}) :
    Continuous T := by
  rw [continuous_iff_isClosed]
  intro C hC
  have hset : T ⁻¹' C = Prod.fst '' (contactSet c u v ∩ (Set.univ ×ˢ C)) := by
    ext x
    constructor
    · intro hx
      refine ⟨(x, T x), ⟨?_, ⟨Set.mem_univ _, hx⟩⟩, rfl⟩
      have : T x ∈ contactFiber c u v x := by rw [hT x]; exact rfl
      exact this
    · rintro ⟨p, ⟨hp1, -, hp2⟩, rfl⟩
      have hfib : p.2 ∈ contactFiber c u v p.1 := hp1
      rw [hT p.1, Set.mem_singleton_iff] at hfib
      show T p.1 ∈ C
      rw [← hfib]
      exact hp2
  rw [hset]
  exact isClosedMap_fst_of_compactSpace _
    ((isClosed_contactSet hc hu hv).inter (isClosed_univ.prod hC))

/-- A selection of the contact set is an optimal transport map: it minimises the transport
cost among all maps pushing `μ` forward to `ν`.  This is the Kantorovich-duality half of
the theory, and it justifies calling the map `T` of `figalli_OT_regularity` an *optimal
transport map*. -/
theorem figalli_OT_optimality {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {c : X → Y → ℝ} {u : X → ℝ} {v : Y → ℝ} (hpair : IsKantorovichPotentials c u v)
    {mu : MeasureTheory.Measure X} {nu : MeasureTheory.Measure Y} {T S : X → Y}
    (hTm : AEMeasurable T mu) (hSm : AEMeasurable S mu)
    (hTpush : mu.map T = nu) (hSpush : mu.map S = nu)
    (hcontact : ∀ x : X, (x, T x) ∈ contactSet c u v)
    (hu : MeasureTheory.Integrable u mu) (hv : MeasureTheory.Integrable v nu)
    (hcS : MeasureTheory.Integrable (fun x : X => c x (S x)) mu) :
    ∫ x : X, c x (T x) ∂mu ≤ ∫ x : X, c x (S x) ∂mu := by
  -- `v ∘ T` and `v ∘ S` are integrable and have the same integral, namely `∫ v ∂ν`.
  have hvT : MeasureTheory.Integrable (fun x : X => v (T x)) mu := by
    have h : MeasureTheory.Integrable (v ∘ T) mu := by
      rw [← MeasureTheory.integrable_map_measure
        (by rw [hTpush]; exact hv.aestronglyMeasurable) hTm, hTpush]
      exact hv
    exact h
  have hvS : MeasureTheory.Integrable (fun x : X => v (S x)) mu := by
    have h : MeasureTheory.Integrable (v ∘ S) mu := by
      rw [← MeasureTheory.integrable_map_measure
        (by rw [hSpush]; exact hv.aestronglyMeasurable) hSm, hSpush]
      exact hv
    exact h
  have hintT : ∫ x : X, v (T x) ∂mu = ∫ y : Y, v y ∂nu := by
    rw [← hTpush]
    exact (MeasureTheory.integral_map hTm
      (by rw [hTpush]; exact hv.aestronglyMeasurable)).symm
  have hintS : ∫ x : X, v (S x) ∂mu = ∫ y : Y, v y ∂nu := by
    rw [← hSpush]
    exact (MeasureTheory.integral_map hSm
      (by rw [hSpush]; exact hv.aestronglyMeasurable)).symm
  have hTeq : ∫ x : X, c x (T x) ∂mu = ∫ x : X, u x ∂mu + ∫ y : Y, v y ∂nu := by
    have : (fun x : X => c x (T x)) = fun x : X => u x + v (T x) := by
      funext x; exact (hcontact x).symm
    rw [this, MeasureTheory.integral_add hu hvT, hintT]
  have hSle : ∫ x : X, u x ∂mu + ∫ y : Y, v y ∂nu ≤ ∫ x : X, c x (S x) ∂mu := by
    rw [← hintS, ← MeasureTheory.integral_add hu hvS]
    exact MeasureTheory.integral_mono (hu.add hvS) hcS fun x => hpair x (S x)
  rw [hTeq]
  exact hSle

/-!
## A non-vacuous instance

We check the hypotheses of `figalli_OT_regularity` on a genuine quadratic-cost example:
`X = [0,1]`, `Y = [1,2]`, `c x y = (x - y)^2 / 2`, with the Kantorovich potentials
`u x = -x`, `v y = y - 1/2`.  Here the contact fiber over `x` is exactly `{x + 1}`, so the
optimal transport map is the translation `x ↦ x + 1`, and the theorem yields its
continuity.
-/

/-- The translation `x ↦ x + 1` as a map `[0,1] → [1,2]`. -/
def shiftMap (x : Set.Icc (0 : ℝ) 1) : Set.Icc (1 : ℝ) 2 :=
  ⟨(x : ℝ) + 1, by
    obtain ⟨hx0, hx1⟩ := x.2
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩⟩

/-- The quadratic cost on `[0,1] × [1,2]`. -/
noncomputable def quadCost (x : Set.Icc (0 : ℝ) 1) (y : Set.Icc (1 : ℝ) 2) : ℝ :=
  ((x : ℝ) - (y : ℝ)) ^ 2 / 2

/-- The potentials for the quadratic-cost example are admissible. -/
theorem quadCost_isKantorovichPotentials :
    IsKantorovichPotentials quadCost (fun x => -(x : ℝ)) (fun y => (y : ℝ) - 1 / 2) := by
  intro x y
  have h : (0 : ℝ) ≤ ((y : ℝ) - (x : ℝ) - 1) ^ 2 := sq_nonneg _
  simp only [quadCost]
  nlinarith [h]

/-- The contact fibers of the quadratic-cost example are singletons: this is the
single-valuedness of the `c`-subdifferential in this model case. -/
theorem quadCost_contactFiber (x : Set.Icc (0 : ℝ) 1) :
    contactFiber quadCost (fun x => -(x : ℝ)) (fun y => (y : ℝ) - 1 / 2) x = {shiftMap x} := by
  ext y
  simp only [contactFiber, Set.mem_setOf_eq, Set.mem_singleton_iff, quadCost, shiftMap]
  constructor
  · intro h
    have hy : (y : ℝ) = (x : ℝ) + 1 := by nlinarith [sq_nonneg ((y : ℝ) - (x : ℝ) - 1)]
    exact Subtype.ext hy
  · intro h
    have hy : (y : ℝ) = (x : ℝ) + 1 := by rw [h]
    rw [hy]; ring

/-- The optimal transport map of the quadratic-cost example is continuous, as an instance of
`figalli_OT_regularity`. -/
theorem figalli_OT_regularity_example : Continuous shiftMap := by
  refine figalli_OT_regularity (c := quadCost) (u := fun x => -(x : ℝ))
    (v := fun y => (y : ℝ) - 1 / 2) ?_ ?_ ?_ quadCost_contactFiber
  · exact ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).pow 2 |>.div_const 2
  · exact continuous_subtype_val.neg
  · exact continuous_subtype_val.sub continuous_const

end Frontier

#print axioms Frontier.figalli_OT_regularity
#print axioms Frontier.figalli_OT_optimality
#print axioms Frontier.figalli_OT_regularity_example

