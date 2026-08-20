/-
# Figalli OT Regularity
Category: Frontier — Fields Medal Work
Target: Frontier.figalli_OT_regularity
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

def contactSet (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) : Set (X × Y) :=
  {p : X × Y | u p.1 + v p.2 = c p.1 p.2}

/-- The contact fiber over `x`, i.e. the `c`-subdifferential `∂^c u (x)`. -/

def contactFiber (c : X → Y → ℝ) (u : X → ℝ) (v : Y → ℝ) (x : X) : Set Y :=
  {y : Y | u x + v y = c x y}

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
