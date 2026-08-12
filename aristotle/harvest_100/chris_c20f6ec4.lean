-- (Lean requires `import` lines to precede any module documentation, so the requested
-- header comment appears immediately below the import.)
import Mathlib

/-!
# Poincare 3 Sphere
Category: Frontier — Moonshot
Target: Frontier.poincare_3sphere
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open Function Topology Metric

universe u v

/-- The model space `ℝ³`. -/
abbrev E3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The 3-sphere `S³`, realized as the unit sphere in `ℝ⁴`. -/
abbrev Sphere3 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

/-!
## `S³` is a closed connected 3-manifold

Mathlib already provides the instances `T2Space Sphere3`, `CompactSpace Sphere3` and
`ChartedSpace E3 Sphere3` (the stereographic atlas); we add connectedness.
-/

/-- The 3-sphere is connected. -/
instance sphere3_connectedSpace : ConnectedSpace Sphere3 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    simp
  exact isConnected_iff_connectedSpace.1
    (isConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)

/-- The 3-sphere is path connected. -/
instance sphere3_pathConnectedSpace : PathConnectedSpace Sphere3 := by
  have hrank : (1 : Cardinal) < Module.rank ℝ (EuclideanSpace ℝ (Fin 4)) := by
    rw [rank_eq_card_basis (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis]
    simp
  exact isPathConnected_iff_pathConnectedSpace.1
    (isPathConnected_sphere hrank (0 : EuclideanSpace ℝ (Fin 4)) zero_le_one)

/-- `S³` is a compact Hausdorff, connected, three-dimensional charted space: i.e. a closed
connected topological 3-manifold. -/
theorem sphere3_isClosedConnected3Manifold :
    T2Space Sphere3 ∧ CompactSpace Sphere3 ∧ ConnectedSpace Sphere3 ∧
      Nonempty (ChartedSpace E3 Sphere3) :=
  ⟨inferInstance, inferInstance, inferInstance, ⟨inferInstance⟩⟩

/-!
## The statement of the Poincaré conjecture, and equivalent formulations

A *closed 3-manifold* is a compact Hausdorff space that is locally homeomorphic to `ℝ³`,
i.e. carries a `ChartedSpace E3` structure (no boundary charts are allowed).
-/

/-- **The Poincaré conjecture** (Perelman): every simply connected closed (compact, boundaryless)
topological 3-manifold is homeomorphic to the 3-sphere. -/
def Poincare3Conjecture : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace E3 M], Nonempty (M ≃ₜ Sphere3)

/-- Reformulation: a continuous bijection onto `S³` is enough. -/
def Poincare3Bij : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace E3 M],
    ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f

/-- Reformulation: a continuous bijection *from* `S³` is enough. -/
def Poincare3Rev : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace E3 M],
    ∃ g : Sphere3 → M, Continuous g ∧ Function.Bijective g

/-- Reformulation: a surjective topological embedding into `S³` is enough. -/
def Poincare3Emb : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace E3 M],
    ∃ f : M → Sphere3, IsEmbedding f ∧ Function.Surjective f

/-- Weakened form of the conjecture: every simply connected closed 3-manifold admits a
continuous *injection* into `S³`.  This is equivalent to the conjecture itself modulo
invariance of domain (see `Frontier.poincare_3sphere`). -/
def Poincare3Inj : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [SimplyConnectedSpace M] [ChartedSpace E3 M],
    ∃ f : M → Sphere3, Continuous f ∧ Function.Injective f

/-- Reformulation of the hypothesis "simply connected" as "path connected with trivial
fundamental group". -/
def Poincare3Pi1 : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    [ChartedSpace E3 M], (∀ x : M, Subsingleton (FundamentalGroup M x)) →
      Nonempty (M ≃ₜ Sphere3)

/-- **Invariance of domain** in dimension `n`: a continuous injective map defined on an open
subset of `ℝⁿ` has open image.  This is a classical theorem of Brouwer which is not available
in Mathlib; below it is used only as an explicit hypothesis. -/
def InvarianceOfDomain (n : ℕ) : Prop :=
  ∀ (s : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    IsOpen s → ContinuousOn f s → Set.InjOn f s → IsOpen (f '' s)

/-!
## Simple connectedness via the fundamental group
-/

section FundamentalGroupSection

open CategoryTheory

/-- A path connected space with trivial fundamental group at some basepoint is simply
connected. -/
theorem simplyConnectedSpace_of_subsingleton_fundamentalGroup {X : Type u} [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) [Subsingleton (FundamentalGroup X x)] :
    SimplyConnectedSpace X := by
  rw [simply_connected_iff_unique_homotopic]
  refine ⟨⟨x⟩, fun y z => ?_⟩
  have hne : Path.Homotopic.Quotient y z := ⟦PathConnectedSpace.somePath y z⟧
  have hsub : Subsingleton (Path.Homotopic.Quotient y z) := by
    constructor
    intro f g
    let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
      ⟦PathConnectedSpace.somePath x y⟧
    let b : FundamentalGroupoid.mk z ⟶ FundamentalGroupoid.mk x :=
      ⟦PathConnectedSpace.somePath z x⟧
    let A : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
      (Groupoid.isoEquivHom _ _).symm a
    let B : FundamentalGroupoid.mk z ≅ FundamentalGroupoid.mk x :=
      (Groupoid.isoEquivHom _ _).symm b
    have key : A.hom ≫ f ≫ B.hom = A.hom ≫ g ≫ B.hom :=
      Subsingleton.elim (α := FundamentalGroup X x) _ _
    rw [Iso.cancel_iso_hom_left] at key
    exact (Iso.cancel_iso_hom_right _ _ B).1 key
  exact ⟨uniqueOfSubsingleton hne⟩

/-- The Poincaré conjecture is equivalent to its formulation in which "simply connected" is
spelled out as "path connected with trivial fundamental group". -/
theorem poincare3_pi1_iff : Poincare3Conjecture.{u} ↔ Poincare3Pi1.{u} := by
  constructor
  · intro h M _ _ _ _ _ hpi
    haveI : Subsingleton (FundamentalGroup M (Classical.arbitrary M)) :=
      hpi (Classical.arbitrary M)
    haveI : SimplyConnectedSpace M :=
      simplyConnectedSpace_of_subsingleton_fundamentalGroup (Classical.arbitrary M)
    exact h M
  · intro h M _ _ _ _ _
    exact h M (fun x => inferInstanceAs (Subsingleton (Path.Homotopic.Quotient x x)))

end FundamentalGroupSection

/-!
## Point-set consequences of the hypotheses
-/

/-- A compact `n`-manifold (compact charted space over `ℝⁿ`) is second countable. -/
theorem secondCountable_of_compact_manifold (n : ℕ) {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    SecondCountableTopology M := by
  set E := EuclideanSpace ℝ (Fin n)
  have hcover : ⋃ x : M, (chartAt E x).source = Set.univ := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨y, mem_chart_source E y⟩
  obtain ⟨t, ht⟩ := IsCompact.elim_finite_subcover (isCompact_univ (X := M))
    (fun x : M => (chartAt E x).source) (fun x => (chartAt E x).open_source)
    (by rw [hcover])
  have hsc : ∀ x : M, SecondCountableTopology ((chartAt E x).source : Set M) :=
    fun x => (chartAt E x).toHomeomorphSourceTarget.secondCountableTopology
  have hcover2 : ⋃ x : {x : M // x ∈ t}, (chartAt E (x : M)).source = Set.univ := by
    refine Set.eq_univ_of_univ_subset ?_
    intro y _
    have hy := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion, exists_prop] at hy ⊢
    obtain ⟨x, hx, hyx⟩ := hy
    exact ⟨⟨x, hx⟩, hyx⟩
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover M _ {x : M // x ∈ t} _
    (fun x => (chartAt E (x : M)).source) (fun x => hsc (x : M))
    (fun x => (chartAt E (x : M)).open_source) hcover2

/-- Every closed (compact Hausdorff) `n`-manifold is metrizable; in particular the spaces
occurring in the Poincaré conjecture are metrizable, second countable spaces. -/
theorem metrizable_of_closed_manifold (n : ℕ) {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [CompactSpace M] :
    TopologicalSpace.MetrizableSpace M := by
  haveI := secondCountable_of_compact_manifold n (M := M)
  exact TopologicalSpace.metrizableSpace_of_t3_secondCountable M

/-!
## Unconditional equivalences
-/

/-- For compact Hausdorff spaces `M` and `S`, being homeomorphic is equivalent to the existence
of a continuous bijection in either direction, and to the existence of a surjective embedding. -/
theorem tfae_homeomorph_of_compact_t2 (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    (S : Type v) [TopologicalSpace S] [T2Space S] [CompactSpace S] :
    List.TFAE
      [Nonempty (M ≃ₜ S),
       ∃ f : M → S, Continuous f ∧ Function.Bijective f,
       ∃ g : S → M, Continuous g ∧ Function.Bijective g,
       ∃ f : M → S, IsEmbedding f ∧ Function.Surjective f] := by
  tfae_have 1 → 2 := by
    rintro ⟨e⟩; exact ⟨e, e.continuous, e.bijective⟩
  tfae_have 2 → 1 := by
    rintro ⟨f, hf, hbij⟩
    exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij) hf⟩
  tfae_have 1 → 3 := by
    rintro ⟨e⟩; exact ⟨e.symm, e.symm.continuous, e.symm.bijective⟩
  tfae_have 3 → 1 := by
    rintro ⟨g, hg, hbij⟩
    exact ⟨(Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hbij) hg).symm⟩
  tfae_have 1 → 4 := by
    rintro ⟨e⟩; exact ⟨e, e.isEmbedding, e.surjective⟩
  tfae_have 4 → 2 := by
    rintro ⟨f, hemb, hsurj⟩
    exact ⟨f, hemb.continuous, hemb.injective, hsurj⟩
  tfae_finish

/-- The Poincaré conjecture is equivalent to each of its three reformulations. -/
theorem tfae_poincare3 :
    List.TFAE [Poincare3Conjecture.{u}, Poincare3Bij.{u}, Poincare3Rev.{u}, Poincare3Emb.{u},
      Poincare3Pi1.{u}] := by
  have key : ∀ (M : Type u) [TopologicalSpace M] [T2Space M] [CompactSpace M],
      List.TFAE
        [Nonempty (M ≃ₜ Sphere3),
         ∃ f : M → Sphere3, Continuous f ∧ Function.Bijective f,
         ∃ g : Sphere3 → M, Continuous g ∧ Function.Bijective g,
         ∃ f : M → Sphere3, IsEmbedding f ∧ Function.Surjective f] := by
    intro M _ _ _
    exact tfae_homeomorph_of_compact_t2 M Sphere3
  tfae_have 1 → 2 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 1).1 (h M)
  tfae_have 2 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 1).2 (h M)
  tfae_have 1 → 3 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 2).1 (h M)
  tfae_have 3 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 2).2 (h M)
  tfae_have 1 → 4 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 3).1 (h M)
  tfae_have 4 → 1 := by
    intro h M _ _ _ _ _
    exact ((key M).out 0 3).2 (h M)
  tfae_have 1 ↔ 5 := poincare3_pi1_iff
  tfae_finish

/-!
## The reduction using invariance of domain
-/

/-- Modulo invariance of domain, a continuous injection between `n`-manifolds is an open map. -/
theorem isOpenMap_of_continuous_injective (n : ℕ) (hIoD : InvarianceOfDomain n)
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {N : Type v} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    (f : M → N) (hf : Continuous f) (hinj : Function.Injective f) : IsOpenMap f := by
  set E := EuclideanSpace ℝ (Fin n)
  intro U hU
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨m, hmU, rfl⟩
  set p := chartAt E m with hp
  set q := chartAt E (f m) with hq
  set W : Set M := U ∩ (p.source ∩ f ⁻¹' q.source) with hW
  have hWopen : IsOpen W := hU.inter (p.open_source.inter (hf.isOpen_preimage _ q.open_source))
  have hmW : m ∈ W := ⟨hmU, mem_chart_source E m, mem_chart_source E (f m)⟩
  have hWsrc : W ⊆ p.source := fun x hx => hx.2.1
  have hWfsrc : ∀ x ∈ W, f x ∈ q.source := fun x hx => hx.2.2
  set s : Set E := p '' W with hs
  have hsopen : IsOpen s := p.isOpen_image_of_subset_source hWopen hWsrc
  set g : E → E := fun z => q (f (p.symm z)) with hg
  have hcont : ContinuousOn g s := by
    have h1 : ContinuousOn (p.symm) s :=
      p.continuousOn_symm.mono (fun z hz => by
        obtain ⟨x, hx, rfl⟩ := hz
        exact p.mapsTo (hWsrc hx))
    have h2 : Set.MapsTo (p.symm) s W := by
      rintro _ ⟨x, hx, rfl⟩
      rwa [p.left_inv (hWsrc hx)]
    have h3 : ContinuousOn (fun x : M => q (f x)) W :=
      ContinuousOn.comp q.continuousOn hf.continuousOn (fun x hx => hWfsrc x hx)
    exact h3.comp h1 h2
  have hinjOn : Set.InjOn g s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    simp only [hg, p.left_inv (hWsrc ha), p.left_inv (hWsrc hb)] at hab
    rw [hinj (q.injOn (hWfsrc a ha) (hWfsrc b hb) hab)]
  have himg : g '' s = q '' (f '' W) := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, by simp [hg, p.left_inv (hWsrc hx)]⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨p x, ⟨x, hx, rfl⟩, by simp [hg, p.left_inv (hWsrc hx)]⟩
  have hopen1 : IsOpen (q '' (f '' W)) := himg ▸ hIoD s g hsopen hcont hinjOn
  have hsub : f '' W ⊆ q.source := by rintro _ ⟨x, hx, rfl⟩; exact hWfsrc x hx
  have hfin : IsOpen (f '' W) := by
    have hqq : q.symm '' (q '' (f '' W)) = f '' W := by
      ext y
      constructor
      · rintro ⟨_, ⟨y', hy', rfl⟩, rfl⟩
        rwa [q.left_inv (hsub hy')]
      · intro hy
        exact ⟨q y, ⟨y, hy, rfl⟩, q.left_inv (hsub hy)⟩
    rw [← hqq]
    refine q.symm.isOpen_image_of_subset_source hopen1 ?_
    rw [q.symm_source]
    rintro _ ⟨y, hy, rfl⟩
    exact q.mapsTo (hsub hy)
  exact ⟨f '' W, Set.image_mono (fun x hx => hx.1), hfin, ⟨m, hmW, rfl⟩⟩

/-- An open continuous injection from a nonempty compact space into a connected Hausdorff space
is a homeomorphism. -/
theorem homeomorph_of_isOpenMap_injective {M : Type u} [TopologicalSpace M] [CompactSpace M]
    [Nonempty M] {N : Type v} [TopologicalSpace N] [T2Space N] [ConnectedSpace N]
    (f : M → N) (hf : Continuous f) (hinj : Function.Injective f) (hopen : IsOpenMap f) :
    Nonempty (M ≃ₜ N) := by
  have hsurj : Function.Surjective f := by
    have hclopen : IsClopen (Set.range f) :=
      ⟨(isCompact_range hf).isClosed, hopen.isOpen_range⟩
    rcases isClopen_iff.1 hclopen with h | h
    · exact absurd h (by simp [Set.eq_empty_iff_forall_notMem])
    · intro y
      have : y ∈ Set.range f := h ▸ Set.mem_univ y
      exact this
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hf⟩

/-- Modulo invariance of domain: a continuous injection from a nonempty compact `n`-manifold
into a connected Hausdorff `n`-manifold is a homeomorphism. -/
theorem homeomorph_of_continuous_injective (n : ℕ) (hIoD : InvarianceOfDomain n)
    {M : Type u} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [Nonempty M]
    {N : Type v} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [T2Space N] [ConnectedSpace N]
    (f : M → N) (hf : Continuous f) (hinj : Function.Injective f) : Nonempty (M ≃ₜ N) :=
  homeomorph_of_isOpenMap_injective f hf hinj
    (isOpenMap_of_continuous_injective n hIoD f hf hinj)

/-- Modulo invariance of domain, the weakened form of the conjecture implies the conjecture. -/
theorem poincare3_of_inj (hIoD : InvarianceOfDomain 3) (h : Poincare3Inj.{u}) :
    Poincare3Conjecture.{u} := by
  intro M _ _ _ _ _
  obtain ⟨f, hf, hinj⟩ := h M
  exact homeomorph_of_continuous_injective 3 hIoD f hf hinj

/-!
## Main statement
-/

/-- **The Poincaré conjecture in dimension 3: formalized statement together with Lean-checked
reductions.**

`Poincare3Conjecture` is the statement that every simply connected closed (compact, boundaryless)
topological 3-manifold is homeomorphic to `S³`.

The first component below is an unconditional equivalence of the conjecture with four
reformulations: it suffices to produce a continuous bijection to `S³`, or a continuous bijection
from `S³`, or a surjective topological embedding into `S³`; and the hypothesis "simply connected"
may equivalently be spelled out as "path connected with trivial fundamental group".

The second component is a reduction of the full conjecture to the *a priori* weaker statement
`Poincare3Inj`, that every simply connected closed 3-manifold admits a continuous injection into
`S³`; this reduction is proved modulo Brouwer's invariance of domain, which is supplied as an
explicit hypothesis since it is not available in Mathlib. -/
theorem poincare_3sphere :
    List.TFAE [Poincare3Conjecture.{u}, Poincare3Bij.{u}, Poincare3Rev.{u}, Poincare3Emb.{u},
        Poincare3Pi1.{u}] ∧
      (InvarianceOfDomain 3 → Poincare3Inj.{u} → Poincare3Conjecture.{u}) :=
  ⟨tfae_poincare3, poincare3_of_inj⟩

end Frontier

