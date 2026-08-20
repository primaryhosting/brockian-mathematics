import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
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

namespace Brockian.Weyl.DeficiencyODE

open scoped InnerProductSpace
open Filter Topology

/-!
## Unbounded operators: graphs, adjoints, essential self-adjointness
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The graph of the (generally unbounded) operator `T` defined on the domain `D ≤ E`,
viewed as a submodule of `E × E`. -/

theorem essentiallySelfAdjoint_of_deficiency_trivial [CompleteSpace E] {D : Submodule ℂ E}
    {T : D →ₗ[ℂ] E} (hdense : Dense (D : Set E)) (hsym : IsSymmetricOp T)
    (hplus : ∀ u : E, (∀ x : D, ⟪T x, u⟫_ℂ = -Complex.I * ⟪(x : E), u⟫_ℂ) → u = 0)
    (hminus : ∀ u : E, (∀ x : D, ⟪T x, u⟫_ℂ = Complex.I * ⟪(x : E), u⟫_ℂ) → u = 0) :
    EssentiallySelfAdjoint T := by
  refine ⟨hdense, le_antisymm ?_ (closure_opGraph_le_adjointGraph hsym)⟩
  -- the closed subspace `S`, closure of the graph
  set S : Submodule ℂ (E × E) := (opGraph T).topologicalClosure
  have hScl : IsClosed (S : Set (E × E)) := Submodule.isClosed_topologicalClosure _
  -- the range `W` of `(x,y) ↦ y - i x` on `S`
  set W : Submodule ℂ E := Submodule.map (defMap E : (E × E) →ₗ[ℂ] E) S
  -- `W` is closed
  have hWclosed : IsClosed (W : Set E) := by
    haveI : CompleteSpace S := hScl.completeSpace_coe
    have hanti : AntilipschitzWith 2 (fun p : S => defMap E (p : E × E)) := by
      refine AntilipschitzWith.of_le_mul_dist fun p q => ?_
      have hmem : ((p : E × E) - (q : E × E)) ∈ S := S.sub_mem p.2 q.2
      have h1 : ‖((p : E × E) - q).1‖ ≤ ‖defMap E ((p : E × E) - q)‖ :=
        norm_fst_le_of_mem_closure hsym hmem
      have hmap : defMap E ((p : E × E) - q) = defMap E p - defMap E q := by
        simp [map_sub]
      have h2 : ‖((p : E × E) - q).2‖ ≤ 2 * ‖defMap E ((p : E × E) - q)‖ := by
        have : ((p : E × E) - q).2 =
            defMap E ((p : E × E) - q) + Complex.I • ((p : E × E) - q).1 := by
          simp [defMap]
        calc ‖((p : E × E) - q).2‖
            ≤ ‖defMap E ((p : E × E) - q)‖ + ‖Complex.I • ((p : E × E) - q).1‖ := by
              rw [this]; exact norm_add_le _ _
          _ ≤ 2 * ‖defMap E ((p : E × E) - q)‖ := by
              rw [norm_smul]; simp only [Complex.norm_I, one_mul]; linarith
      have hd : dist p q = ‖(p : E × E) - q‖ := by
        rw [Subtype.dist_eq, dist_eq_norm]
      rw [hd, dist_eq_norm, ← hmap, Prod.norm_def]
      simp only [NNReal.coe_ofNat]
      have hnn := norm_nonneg (defMap E ((p : E × E) - q))
      exact max_le (by linarith) h2
    have hrange : Set.range (fun p : S => defMap E (p : E × E)) = (W : Set E) := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩; exact ⟨(p : E × E), p.2, rfl⟩
      · rintro ⟨p, hp, rfl⟩; exact ⟨⟨p, hp⟩, rfl⟩
    rw [← hrange]
    exact hanti.isClosed_range ((defMap E).uniformContinuous.comp uniformContinuous_subtype_val)
  -- `W` is dense, since its orthogonal complement is trivial
  have hWtop : W = ⊤ := by
    have hbot : Wᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro u hu
      refine hplus u fun x => ?_
      have hmemS : ((x : E), T x) ∈ S := by
        refine Submodule.le_topologicalClosure _ ?_
        rw [mem_opGraph_iff]; exact ⟨x, rfl⟩
      have : (T x - Complex.I • (x : E)) ∈ W := ⟨((x : E), T x), hmemS, rfl⟩
      have h0 := hu _ this
      rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
      simpa using h0
    have := (Submodule.topologicalClosure_eq_top_iff (K := W)).mpr hbot
    rwa [hWclosed.submodule_topologicalClosure_eq] at this
  -- conclusion
  rintro ⟨u, v⟩ huv
  have hex : (v - Complex.I • u) ∈ W := by rw [hWtop]; trivial
  obtain ⟨q, hqS, hq⟩ := hex
  have hqAd : q ∈ adjointGraph T := closure_opGraph_le_adjointGraph hsym hqS
  set w : E := u - q.1 with hw
  have hv : v - q.2 = Complex.I • w := by
    have : q.2 - Complex.I • q.1 = v - Complex.I • u := hq
    rw [hw, smul_sub]
    linear_combination (norm := module) -this
  have hwad : ∀ x : D, ⟪T x, w⟫_ℂ = Complex.I * ⟪(x : E), w⟫_ℂ := by
    intro x
    have h1 : ⟪T x, u⟫_ℂ = ⟪(x : E), v⟫_ℂ := huv x
    have h2 : ⟪T x, q.1⟫_ℂ = ⟪(x : E), q.2⟫_ℂ := hqAd x
    have : ⟪T x, w⟫_ℂ = ⟪(x : E), v - q.2⟫_ℂ := by
      rw [hw, inner_sub_right, inner_sub_right, h1, h2]
    rw [this, hv, inner_smul_right]
  have hw0 : w = 0 := hminus w hwad
  have hu : u = q.1 := by
    have h := hw0; rw [hw, sub_eq_zero] at h; exact h
  have hv2 : v = q.2 := sub_eq_zero.mp (by rw [hv, hw0, smul_zero])
  have hpq : ((u, v) : E × E) = q := Prod.ext_iff.mpr ⟨hu, hv2⟩
  rw [hpq]
  exact hqS

/-!
## The deficiency difference equation (discrete Weyl theory)

For the discrete Schrödinger operator the deficiency equation `T u = z u` is the second order
difference equation `q n * c n - c (n+1) - c (n-1) = z * c n`.  The Wronskian argument below
shows that for non-real `z` this equation has no nonzero `ℓ²` solution, for an *arbitrary* real
potential (no regularity or boundedness of the potential is assumed).
-/

/-- The (imaginary part of the) Wronskian of a solution with its complex conjugate. -/
