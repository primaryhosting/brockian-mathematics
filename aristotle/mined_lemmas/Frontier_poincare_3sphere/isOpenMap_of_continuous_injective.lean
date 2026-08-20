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
