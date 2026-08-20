import Mathlib
import RequestProject.AlexanderTrick

/-!
# Twisted spheres

A *twisted sphere* is obtained by gluing two copies of the closed `n`-disk along their boundary
`𝕊ⁿ⁻¹` by a homeomorphism `f`.  All the known exotic spheres in dimension `7` arise this way
(Milnor's `S³`-bundles over `S⁴` carry Morse functions with exactly two critical points, which exhibits
them as twisted spheres).

The main result of this file is that **every twisted sphere is homeomorphic to the standard
sphere**: this is the topological half of Milnor's theorem, and it is proved here in full, for
every dimension `n`, using the Alexander trick from `RequestProject.AlexanderTrick`.
-/

namespace Frontier

open Metric

/-- The unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ`. -/
abbrev Sph (n : ℕ) : Type := sphere (0 : EuclideanSpace ℝ (Fin n)) 1

/-- The closed unit disk `Dⁿ ⊆ ℝⁿ`. -/
abbrev Dsk (n : ℕ) : Type := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1

lemma norm_coe_dsk_le {n : ℕ} (x : Dsk n) : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 :=
  mem_closedBall_zero_iff.mp x.2

/-- The boundary sphere sits inside the disk. -/
def sphereToDisk {n : ℕ} (x : Sph n) : Dsk n :=
  ⟨(x : EuclideanSpace ℝ (Fin n)), by
    rw [mem_closedBall_zero_iff, norm_coe_unitSphere]⟩

/-- The gluing relation defining the twisted sphere `Dⁿ ∪_f Dⁿ`. -/
inductive GlueRel {n : ℕ} (f : Sph n ≃ₜ Sph n) : Dsk n ⊕ Dsk n → Dsk n ⊕ Dsk n → Prop
  | intro (x : Sph n) : GlueRel f (Sum.inl (sphereToDisk x)) (Sum.inr (sphereToDisk (f x)))

/-- The twisted sphere `Σ_f = Dⁿ ∪_f Dⁿ`: two disks glued along their boundary by `f`. -/
def TwistedSphere {n : ℕ} (f : Sph n ≃ₜ Sph n) : Type := Quot (GlueRel f)

instance {n : ℕ} (f : Sph n ≃ₜ Sph n) : TopologicalSpace (TwistedSphere f) :=
  inferInstanceAs (TopologicalSpace (Quot _))

instance {n : ℕ} (f : Sph n ≃ₜ Sph n) : CompactSpace (TwistedSphere f) :=
  inferInstanceAs (CompactSpace (Quot _))

/-- The canonical map from the disjoint union of the two disks to the twisted sphere. -/
def TwistedSphere.mk {n : ℕ} (f : Sph n ≃ₜ Sph n) (p : Dsk n ⊕ Dsk n) : TwistedSphere f :=
  Quot.mk _ p

lemma TwistedSphere.mk_surjective {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    Function.Surjective (TwistedSphere.mk f) := Quot.mk_surjective

lemma TwistedSphere.continuous_mk {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    Continuous (TwistedSphere.mk f) := continuous_quot_mk

lemma TwistedSphere.sound {n : ℕ} (f : Sph n ≃ₜ Sph n) (x : Sph n) :
    TwistedSphere.mk f (Sum.inl (sphereToDisk x))
      = TwistedSphere.mk f (Sum.inr (sphereToDisk (f x))) :=
  Quot.sound (GlueRel.intro x)

/-! ## Untwisting: `Σ_f ≃ₜ Σ_id` via the Alexander trick -/

/-- The Alexander extension of `f`, as a self-homeomorphism of the closed disk. -/
noncomputable def diskMap {n : ℕ} (f : Sph n ≃ₜ Sph n) (y : Dsk n) : Dsk n :=
  ⟨coneHomeomorph f (y : EuclideanSpace ℝ (Fin n)), by
    rw [mem_closedBall_zero_iff, norm_coneHomeomorph]
    exact norm_coe_dsk_le y⟩

lemma continuous_diskMap {n : ℕ} (f : Sph n ≃ₜ Sph n) : Continuous (diskMap f) :=
  Continuous.subtype_mk ((coneHomeomorph f).continuous.comp continuous_subtype_val) _

lemma diskMap_symm_diskMap {n : ℕ} (f : Sph n ≃ₜ Sph n) (y : Dsk n) :
    diskMap f.symm (diskMap f y) = y := by
  apply Subtype.ext
  exact coneMap_comp_coneMap _ _ (fun z => f.symm_apply_apply z) _

lemma diskMap_diskMap_symm {n : ℕ} (f : Sph n ≃ₜ Sph n) (y : Dsk n) :
    diskMap f (diskMap f.symm y) = y := by
  apply Subtype.ext
  exact coneMap_comp_coneMap _ _ (fun z => f.apply_symm_apply z) _

lemma diskMap_sphereToDisk {n : ℕ} (f : Sph n ≃ₜ Sph n) (x : Sph n) :
    diskMap f (sphereToDisk x) = sphereToDisk (f x) := by
  apply Subtype.ext
  exact coneHomeomorph_coe_sphere f x

/-- The identity homeomorphism of the boundary sphere; `Σ_(id)` is the untwisted double. -/
abbrev sphereId (n : ℕ) : Sph n ≃ₜ Sph n := Homeomorph.refl _

/-- Untwisting map `Σ_(id) → Σ_f`. -/
noncomputable def untwistInv {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere (sphereId n) → TwistedSphere f := by
  refine Quot.lift (fun p => TwistedSphere.mk f (Sum.map id (diskMap f) p)) ?_
  rintro _ _ ⟨x⟩
  simpa [Sum.map, diskMap_sphereToDisk f x] using TwistedSphere.sound f x

/-- Twisting map `Σ_f → Σ_(id)`. -/
noncomputable def untwist {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere f → TwistedSphere (sphereId n) := by
  refine Quot.lift (fun p => TwistedSphere.mk (sphereId n) (Sum.map id (diskMap f.symm) p)) ?_
  rintro _ _ ⟨x⟩
  have h : diskMap f.symm (sphereToDisk (f x)) = sphereToDisk x := by
    rw [diskMap_sphereToDisk f.symm (f x)]
    simp
  simpa [Sum.map, h] using TwistedSphere.sound (sphereId n) x

/-- **Untwisting.**  For every boundary homeomorphism `f`, the twisted sphere `Σ_f` is
homeomorphic to the untwisted double `Σ_(id)`.  This is where the Alexander trick is used. -/
noncomputable def twistedSphereHomeomorphUntwisted {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere f ≃ₜ TwistedSphere (sphereId n) where
  toFun := untwist f
  invFun := untwistInv f
  left_inv := by
    intro z
    induction z using Quot.ind with
    | mk p =>
      cases p with
      | inl x => rfl
      | inr y =>
        show TwistedSphere.mk f (Sum.inr (diskMap f (diskMap f.symm y))) = _
        rw [diskMap_diskMap_symm]
        rfl
  right_inv := by
    intro z
    induction z using Quot.ind with
    | mk p =>
      cases p with
      | inl x => rfl
      | inr y =>
        show TwistedSphere.mk (sphereId n) (Sum.inr (diskMap f.symm (diskMap f y))) = _
        rw [diskMap_symm_diskMap]
        rfl
  continuous_toFun := by
    apply continuous_quot_lift
    exact (TwistedSphere.continuous_mk _).comp
      (continuous_id.sumMap (continuous_diskMap f.symm))
  continuous_invFun := by
    apply continuous_quot_lift
    exact (TwistedSphere.continuous_mk _).comp
      (continuous_id.sumMap (continuous_diskMap f))

/-! ## The untwisted double of the disk is the sphere -/

/-- Append a last coordinate to a Euclidean vector. -/
noncomputable def snocLp {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp x) t)

lemma norm_snocLp_sq {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖snocLp x t‖ ^ 2 = ‖x‖ ^ 2 + t ^ 2 := by
  simp only [snocLp, EuclideanSpace.norm_eq, Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last, Real.norm_eq_abs, sq_abs]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]

lemma snocLp_apply_castSucc {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (i : Fin n) :
    (WithLp.ofLp (snocLp x t)) i.castSucc = (WithLp.ofLp x) i := by
  simp [snocLp]

lemma snocLp_apply_last {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    (WithLp.ofLp (snocLp x t)) (Fin.last n) = t := by
  simp [snocLp]

lemma snocLp_injective {n : ℕ} {x y : EuclideanSpace ℝ (Fin n)} {t s : ℝ}
    (h : snocLp x t = snocLp y s) : x = y ∧ t = s := by
  constructor
  · ext i
    have := congrArg (fun v => (WithLp.ofLp v) i.castSucc) h
    simpa [snocLp_apply_castSucc] using this
  · have := congrArg (fun v => (WithLp.ofLp v) (Fin.last n)) h
    simpa [snocLp_apply_last] using this

/-- Every Euclidean vector in `ℝⁿ⁺¹` is a `snocLp`. -/
lemma exists_snocLp {n : ℕ} (v : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), v = snocLp x t := by
  refine ⟨WithLp.toLp 2 (Fin.init (WithLp.ofLp v)), (WithLp.ofLp v) (Fin.last n), ?_⟩
  apply WithLp.ofLp_injective
  simp [snocLp, Fin.snoc_init_self]

/-- The two hemisphere maps `Dⁿ → 𝕊ⁿ`, for `e = ±1`. -/
noncomputable def hemisphere {n : ℕ} (e : ℝ) (he : e ^ 2 = 1) (x : Dsk n) : Sph (n + 1) :=
  ⟨snocLp (x : EuclideanSpace ℝ (Fin n))
      (e * Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)), by
    have hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 1 := by
      have h1 := norm_coe_dsk_le x
      nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]
    rw [mem_sphere_zero_iff_norm]
    have hsq : ‖snocLp (x : EuclideanSpace ℝ (Fin n))
        (e * Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2))‖ ^ 2 = 1 := by
      rw [norm_snocLp_sq, mul_pow, he, one_mul,
        Real.sq_sqrt (by linarith)]
      ring
    nlinarith [norm_nonneg (snocLp (x : EuclideanSpace ℝ (Fin n))
      (e * Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)))]⟩

lemma continuous_snocLp {X : Type*} [TopologicalSpace X] {n : ℕ}
    {g : X → EuclideanSpace ℝ (Fin n)} {t : X → ℝ} (hg : Continuous g) (ht : Continuous t) :
    Continuous fun s => snocLp (g s) (t s) := by
  refine (PiLp.continuous_toLp 2 _).comp ?_
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ ?_ i
  · simpa using ht
  · intro j
    simpa using (continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hg)

lemma continuous_hemisphere {n : ℕ} (e : ℝ) (he : e ^ 2 = 1) :
    Continuous (hemisphere (n := n) e he) := by
  apply Continuous.subtype_mk
  exact continuous_snocLp continuous_subtype_val
    (continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.sub ((continuous_norm.comp continuous_subtype_val).pow 2))))

/-- The map from the untwisted double to the sphere. -/
noncomputable def doubleToSphere {n : ℕ} : Dsk n ⊕ Dsk n → Sph (n + 1) :=
  Sum.elim (hemisphere 1 (by norm_num)) (hemisphere (-1) (by norm_num))

lemma continuous_doubleToSphere {n : ℕ} : Continuous (doubleToSphere (n := n)) :=
  Continuous.sumElim (continuous_hemisphere _ _) (continuous_hemisphere _ _)

lemma hemisphere_of_norm_one {n : ℕ} (e : ℝ) (he : e ^ 2 = 1) (x : Dsk n)
    (hx : ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1) :
    (hemisphere e he x : EuclideanSpace ℝ (Fin (n + 1)))
      = snocLp (x : EuclideanSpace ℝ (Fin n)) 0 := by
  show snocLp _ _ = _
  rw [hx]
  norm_num

lemma doubleToSphere_glue {n : ℕ} (a b : Dsk n ⊕ Dsk n) (h : GlueRel (sphereId n) a b) :
    doubleToSphere a = doubleToSphere b := by
  cases h with
  | intro x =>
    apply Subtype.ext
    show (hemisphere 1 (by norm_num) (sphereToDisk x) : EuclideanSpace ℝ (Fin (n+1)))
      = (hemisphere (-1) (by norm_num) (sphereToDisk (x : Sph n)) : EuclideanSpace ℝ (Fin (n+1)))
    have hx : ‖((sphereToDisk x : Dsk n) : EuclideanSpace ℝ (Fin n))‖ = 1 :=
      norm_coe_unitSphere x
    rw [hemisphere_of_norm_one _ _ _ hx, hemisphere_of_norm_one _ _ _ hx]

/-- The induced map from the untwisted double to the sphere. -/
noncomputable def untwistedToSphere {n : ℕ} : TwistedSphere (sphereId n) → Sph (n + 1) :=
  Quot.lift doubleToSphere doubleToSphere_glue

lemma untwistedToSphere_surjective {n : ℕ} :
    Function.Surjective (untwistedToSphere (n := n)) := by
  intro v
  obtain ⟨x, t, hxt⟩ := exists_snocLp (v : EuclideanSpace ℝ (Fin (n + 1)))
  have hv : ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := norm_coe_unitSphere v
  have hsum : ‖x‖ ^ 2 + t ^ 2 = 1 := by
    rw [← norm_snocLp_sq, ← hxt, hv]; norm_num
  have hxle : ‖x‖ ≤ 1 := by nlinarith [norm_nonneg x, sq_nonneg t]
  have hsq : Real.sqrt (1 - ‖x‖ ^ 2) = |t| := by
    have : (1 : ℝ) - ‖x‖ ^ 2 = t ^ 2 := by linarith
    rw [this, Real.sqrt_sq_eq_abs]
  set d : Dsk n := ⟨x, mem_closedBall_zero_iff.mpr hxle⟩ with hd
  rcases le_total 0 t with ht | ht
  · refine ⟨Quot.mk _ (Sum.inl d), ?_⟩
    apply Subtype.ext
    show snocLp x (1 * Real.sqrt (1 - ‖x‖ ^ 2)) = _
    rw [one_mul, hsq, abs_of_nonneg ht, ← hxt]
  · refine ⟨Quot.mk _ (Sum.inr d), ?_⟩
    apply Subtype.ext
    show snocLp x (-1 * Real.sqrt (1 - ‖x‖ ^ 2)) = _
    rw [hsq, abs_of_nonpos ht, hxt]
    ring_nf

/-- If the two hemisphere coordinates agree with opposite signs, the point is on the equator. -/
lemma norm_eq_one_of_sqrt_eq_neg {n : ℕ} {x : Dsk n}
    (h : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)
      = -Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2)) :
    ‖(x : EuclideanSpace ℝ (Fin n))‖ = 1 := by
  have hz : Real.sqrt (1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2) = 0 := by linarith
  have hle : 1 - ‖(x : EuclideanSpace ℝ (Fin n))‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp hz
  have h1 := norm_coe_dsk_le x
  nlinarith [norm_nonneg (x : EuclideanSpace ℝ (Fin n))]

lemma doubleToSphere_inj_aux {n : ℕ} (a b : Dsk n ⊕ Dsk n)
    (h : doubleToSphere a = doubleToSphere b) :
    Quot.mk (GlueRel (sphereId n)) a = Quot.mk (GlueRel (sphereId n)) b := by
  have key : ∀ (u v : Dsk n) (e₁ e₂ : ℝ) (h₁ : e₁ ^ 2 = 1) (h₂ : e₂ ^ 2 = 1),
      (hemisphere e₁ h₁ u : EuclideanSpace ℝ (Fin (n+1)))
        = (hemisphere e₂ h₂ v : EuclideanSpace ℝ (Fin (n+1))) →
      (u : EuclideanSpace ℝ (Fin n)) = (v : EuclideanSpace ℝ (Fin n)) ∧
        e₁ * Real.sqrt (1 - ‖(u : EuclideanSpace ℝ (Fin n))‖ ^ 2)
          = e₂ * Real.sqrt (1 - ‖(v : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
    intro u v e₁ e₂ h₁ h₂ huv
    exact snocLp_injective huv
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      obtain ⟨h1, -⟩ := key u v 1 1 (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [Subtype.ext h1]
    | inr v =>
      obtain ⟨h1, h2⟩ := key u v 1 (-1) (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [one_mul, neg_one_mul, ← h1] at h2
      have hnorm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 := norm_eq_one_of_sqrt_eq_neg h2
      have hu : u = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := rfl
      have hv : v = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := Subtype.ext h1.symm
      rw [hu, hv]
      exact TwistedSphere.sound (sphereId n) _
  | inr u =>
    cases b with
    | inl v =>
      obtain ⟨h1, h2⟩ := key u v (-1) 1 (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [one_mul, neg_one_mul, ← h1] at h2
      have hnorm : ‖(u : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        norm_eq_one_of_sqrt_eq_neg (by linarith)
      have hu : u = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := rfl
      have hv : v = sphereToDisk ⟨(u : EuclideanSpace ℝ (Fin n)),
          mem_sphere_zero_iff_norm.mpr hnorm⟩ := Subtype.ext h1.symm
      rw [hu, hv]
      exact (TwistedSphere.sound (sphereId n) _).symm
    | inr v =>
      obtain ⟨h1, -⟩ := key u v (-1) (-1) (by norm_num) (by norm_num) (congrArg Subtype.val h)
      rw [Subtype.ext h1]

lemma untwistedToSphere_injective {n : ℕ} :
    Function.Injective (untwistedToSphere (n := n)) := by
  intro z w h
  induction z using Quot.ind with
  | mk a =>
    induction w using Quot.ind with
    | mk b => exact doubleToSphere_inj_aux a b h

/-- **The untwisted double of the `n`-disk is the `n`-sphere.** -/
noncomputable def untwistedHomeomorphSphere (n : ℕ) :
    TwistedSphere (sphereId n) ≃ₜ Sph (n + 1) :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective untwistedToSphere
      ⟨untwistedToSphere_injective, untwistedToSphere_surjective⟩)
    (continuous_quot_lift _ continuous_doubleToSphere)

/-- **Every twisted sphere is homeomorphic to the standard sphere.**

This is the topological half of Milnor's theorem, proved here in full generality: gluing two
`n`-disks along their boundary by *any* homeomorphism always yields a space homeomorphic to
`𝕊ⁿ`.  Only the smooth structure can differ — which is exactly what Milnor's invariant detects. -/
noncomputable def twistedSphereHomeomorphSphere {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    TwistedSphere f ≃ₜ Sph (n + 1) :=
  (twistedSphereHomeomorphUntwisted f).trans (untwistedHomeomorphSphere n)

/-- **Every twisted sphere is homeomorphic to the standard sphere**, in existential form. -/
theorem nonempty_twistedSphere_homeomorph_sphere {n : ℕ} (f : Sph n ≃ₜ Sph n) :
    Nonempty (TwistedSphere f ≃ₜ Sph (n + 1)) :=
  ⟨twistedSphereHomeomorphSphere f⟩

end Frontier

/-
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`; the header is
-- repeated verbatim as the module docstring immediately below the imports.)
import Mathlib
import RequestProject.AlexanderTrick
import RequestProject.TwistedSphere

/-!
# Milnor Exotic 7 Sphere
Category: Frontier Abel
Target: Frontier.milnor_exotic_7sphere
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Manifold ContDiff

namespace Frontier

/-! ## Setting

`E7` is the model space `ℝ⁷`, and `S7` is the standard (round) `7`-sphere sitting inside `ℝ⁸`.
Mathlib already equips `S7` with a smooth structure modelled on `E7`.
-/

/-- The `7`-dimensional Euclidean model space `ℝ⁷`. -/
abbrev E7 : Type := EuclideanSpace ℝ (Fin 7)

/-- The standard smooth `7`-sphere `𝕊⁷ ⊆ ℝ⁸`. -/
abbrev S7 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 8)) 1

/-- **Statement of Milnor's theorem.**  There exists a smooth `7`-manifold which is
homeomorphic, but not diffeomorphic, to the standard `7`-sphere.

This is exactly the statement recorded (as an unproven `proof_wanted`) in Mathlib's
`Mathlib/Geometry/Manifold/PoincareConjecture.lean` under the name
`exists_homeomorph_isEmpty_diffeomorph_sphere_seven`. -/
def ExoticSevenSphereExists : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : ChartedSpace E7 M)
    (_ : IsManifold (𝓡 7) ∞ M) (_homeo : M ≃ₜ S7),
    IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ S7)

/-! ## The topological half of Milnor's theorem, proved

Milnor's manifolds are `S³`-bundles over `S⁴` carrying a Morse function with exactly two
critical points; such a manifold is a *twisted sphere*, i.e. two `7`-disks glued along their
boundary `𝕊⁶` by a homeomorphism.  The file `RequestProject.TwistedSphere` proves, in every
dimension and for *every* gluing homeomorphism, that the result is homeomorphic to the standard
sphere (via the Alexander trick of `RequestProject.AlexanderTrick`).  We record the
`7`-dimensional case here. -/

/-- **Every twisted `7`-sphere is homeomorphic to the standard `7`-sphere.**  Proved
unconditionally: this is the topological half of Milnor's theorem. -/
theorem twisted_seven_sphere_homeomorph (f : Sph 7 ≃ₜ Sph 7) :
    Nonempty (TwistedSphere f ≃ₜ S7) :=
  ⟨twistedSphereHomeomorphSphere f⟩

/-! ## Bundled smooth 7-manifolds

To speak about invariants of smooth `7`-manifolds we bundle the data. -/

/-- A bundled smooth `7`-manifold: a type together with a topology, an atlas modelled on
`ℝ⁷`, and the smoothness condition. -/
structure SmoothSeven where
  /-- The underlying type of the manifold. -/
  carrier : Type
  [topology : TopologicalSpace carrier]
  [charts : ChartedSpace E7 carrier]
  [smooth : IsManifold (𝓡 7) ∞ carrier]

attribute [instance] SmoothSeven.topology SmoothSeven.charts SmoothSeven.smooth

/-- Diffeomorphisms between bundled smooth `7`-manifolds. -/
abbrev SmoothSeven.Diffeo (M N : SmoothSeven) : Type :=
  M.carrier ≃ₘ⟮𝓡 7, 𝓡 7⟯ N.carrier

/-- Homeomorphisms between bundled smooth `7`-manifolds. -/
abbrev SmoothSeven.Homeo (M N : SmoothSeven) : Type :=
  M.carrier ≃ₜ N.carrier

/-- The standard `7`-sphere as a bundled smooth `7`-manifold. -/
noncomputable def sphereSeven : SmoothSeven := { carrier := S7 }

@[simp] lemma sphereSeven_carrier : sphereSeven.carrier = S7 := rfl

/-- Every bundled smooth `7`-manifold is diffeomorphic to itself. -/
lemma SmoothSeven.nonempty_diffeo_self (M : SmoothSeven) : Nonempty (M.Diffeo M) :=
  ⟨Diffeomorph.refl (𝓡 7) M.carrier ∞⟩

/-- Every bundled smooth `7`-manifold is homeomorphic to itself. -/
lemma SmoothSeven.nonempty_homeo_self (M : SmoothSeven) : Nonempty (M.Homeo M) :=
  ⟨Homeomorph.refl M.carrier⟩

/-- A diffeomorphism is in particular a homeomorphism. -/
lemma SmoothSeven.nonempty_homeo_of_nonempty_diffeo {M N : SmoothSeven}
    (h : Nonempty (M.Diffeo N)) : Nonempty (M.Homeo N) :=
  h.elim fun d => ⟨d.toHomeomorph⟩

/-! ## Milnor's theorem, reduced to its smooth half

Milnor's proof has two halves:

* a *topological* half: the manifolds in question are twisted spheres, hence homeomorphic to
  `𝕊⁷`.  This half is **proved** above (`Frontier.twisted_seven_sphere_homeomorph`).
* a *smooth* half: a diffeomorphism invariant `λ` (built from the Hirzebruch signature theorem
  applied to a coboundary) distinguishes them from `𝕊⁷`.

The target theorem below performs the reduction: it consumes only the smooth half. -/

/-- **Milnor's exotic 7-sphere, reduced to its smooth half.**

Let `f` be any homeomorphism of `𝕊⁶`, and equip the twisted sphere `Σ_f = D⁷ ∪_f D⁷` with a
smooth structure modelled on `ℝ⁷`.  If `Σ_f` is not diffeomorphic to the standard `𝕊⁷`, then an
exotic `7`-sphere exists, i.e. `Frontier.ExoticSevenSphereExists` holds — a statement recorded
in Mathlib only as the open `proof_wanted
exists_homeomorph_isEmpty_diffeomorph_sphere_seven`.

Note that no homeomorphism `Σ_f ≃ₜ 𝕊⁷` is assumed: it is *proved*, via the Alexander trick.
The only remaining hypothesis is Milnor's smooth-invariant computation. -/
theorem milnor_exotic_7sphere (f : Sph 7 ≃ₜ Sph 7)
    (charts : ChartedSpace E7 (TwistedSphere f))
    (smooth : IsManifold (𝓡 7) ∞ (TwistedSphere f))
    (hnd : IsEmpty (TwistedSphere f ≃ₘ⟮𝓡 7, 𝓡 7⟯ S7)) :
    ExoticSevenSphereExists :=
  ⟨TwistedSphere f, inferInstance, charts, smooth, twistedSphereHomeomorphSphere f, hnd⟩

/-- **Milnor's exotic 7-sphere, as an abstract Lean-checked reduction.**

If `P` is any predicate on smooth `7`-manifolds which is invariant under diffeomorphism, and if
some smooth `7`-manifold `M` is homeomorphic to the standard `7`-sphere while `P` separates `M`
from `𝕊⁷`, then an exotic `7`-sphere exists. -/
theorem milnor_exotic_7sphere_of_smooth_invariant
    (P : SmoothSeven → Prop)
    (hP : ∀ M N : SmoothSeven, Nonempty (M.Diffeo N) → (P M ↔ P N))
    (M : SmoothSeven) (hhomeo : Nonempty (M.Homeo sphereSeven))
    (hMP : ¬ P M) (hSP : P sphereSeven) :
    ExoticSevenSphereExists := by
  obtain ⟨h⟩ := hhomeo
  exact ⟨M.carrier, M.topology, M.charts, M.smooth, h,
    ⟨fun d => hMP ((hP M sphereSeven ⟨d⟩).mpr hSP)⟩⟩

/-- The converse: if an exotic `7`-sphere exists, then a separating diffeomorphism invariant
exists as well.  Hence the hypotheses of the abstract reduction are not merely sufficient but
also necessary. -/
theorem exists_separating_invariant_of_exotic (h : ExoticSevenSphereExists) :
    ∃ (P : SmoothSeven → Prop) (M : SmoothSeven),
      (∀ A B : SmoothSeven, Nonempty (A.Diffeo B) → (P A ↔ P B)) ∧
        Nonempty (M.Homeo sphereSeven) ∧ ¬ P M ∧ P sphereSeven := by
  obtain ⟨M, tM, cM, sM, homeo, hempty⟩ := h
  refine ⟨fun N => Nonempty (N.Diffeo sphereSeven), @SmoothSeven.mk M tM cM sM,
    fun A B hAB => ?_, ⟨homeo⟩, ?_, ⟨Diffeomorph.refl (𝓡 7) sphereSeven.carrier ∞⟩⟩
  · obtain ⟨e⟩ := hAB
    exact ⟨fun ⟨g⟩ => ⟨e.symm.trans g⟩, fun ⟨g⟩ => ⟨e.trans g⟩⟩
  · exact fun hc => hc.elim hempty.elim

/-- Milnor's theorem is *equivalent* to the existence of a diffeomorphism invariant separating
some manifold homeomorphic to `𝕊⁷` from `𝕊⁷` itself. -/
theorem milnor_exotic_7sphere_iff :
    ExoticSevenSphereExists ↔
      ∃ (P : SmoothSeven → Prop) (M : SmoothSeven),
        (∀ A B : SmoothSeven, Nonempty (A.Diffeo B) → (P A ↔ P B)) ∧
          Nonempty (M.Homeo sphereSeven) ∧ ¬ P M ∧ P sphereSeven :=
  ⟨exists_separating_invariant_of_exotic,
    fun ⟨P, M, hP, hhomeo, hMP, hSP⟩ =>
      milnor_exotic_7sphere_of_smooth_invariant P hP M hhomeo hMP hSP⟩

/-- The reduction is sharp in the following sense: a *topological* invariant can never do the
job, so the separating invariant must genuinely be a smooth invariant. -/
theorem no_topological_invariant_separates
    (P : SmoothSeven → Prop)
    (hP : ∀ M N : SmoothSeven, Nonempty (M.Homeo N) → (P M ↔ P N))
    (M : SmoothSeven) (hhomeo : Nonempty (M.Homeo sphereSeven)) :
    ¬ (¬ P M ∧ P sphereSeven) := by
  rintro ⟨hMP, hSP⟩
  exact hMP ((hP M sphereSeven hhomeo).mpr hSP)

/-! ## The arithmetic base case: Milnor's `λ`-invariant modulo `7`

For the `S³`-bundles `M_j` over `S⁴` with clutching data `h + l = 1`, `h - l = j` (`j` odd),
Milnor's invariant is `λ (M_j) = j² - 1 ∈ ℤ/7`, while `λ (𝕊⁷) = 0`.  The base case of the
argument is the purely arithmetic observation that `j² - 1 ≢ 0 (mod 7)` for suitable odd `j`
(e.g. `j = 3`, giving `λ = 1`).  This is checked below by decision procedure. -/

/-- Milnor's `λ`-invariant of the bundle `M_j`, as an element of `ℤ/7`. -/
def milnorLambda (j : ℤ) : ZMod 7 := (j : ZMod 7) ^ 2 - 1

/-- The standard sphere corresponds to `j = 1`, where the invariant vanishes. -/
theorem milnorLambda_one : milnorLambda 1 = 0 := by decide

/-- For `j = 3` the invariant is nonzero, so `M₃` cannot be diffeomorphic to `𝕊⁷`. -/
theorem milnorLambda_three_ne_zero : milnorLambda 3 ≠ 0 := by decide

/-- There is an odd `j` for which Milnor's invariant is nonzero: the arithmetic base case of
Milnor's construction. -/
theorem exists_odd_milnorLambda_ne_zero : ∃ j : ℤ, Odd j ∧ milnorLambda j ≠ 0 :=
  ⟨3, ⟨1, by norm_num⟩, milnorLambda_three_ne_zero⟩

/-- **Milnor's argument, packaged.**  Given a `ℤ/7`-valued diffeomorphism invariant `lam` of
smooth `7`-manifolds, a family `Mfam` of smooth `7`-manifolds each homeomorphic to `𝕊⁷` with
`lam (Mfam j) = milnorLambda j`, and `lam 𝕊⁷ = 0`, an exotic `7`-sphere exists. -/
theorem milnor_exotic_7sphere_of_lambda
    (lam : SmoothSeven → ZMod 7)
    (hlam : ∀ M N : SmoothSeven, Nonempty (M.Diffeo N) → lam M = lam N)
    (Mfam : ℤ → SmoothSeven)
    (hhomeo : ∀ j : ℤ, Nonempty ((Mfam j).Homeo sphereSeven))
    (hval : ∀ j : ℤ, lam (Mfam j) = milnorLambda j)
    (hsphere : lam sphereSeven = 0) :
    ExoticSevenSphereExists := by
  obtain ⟨j, -, hj⟩ := exists_odd_milnorLambda_ne_zero
  refine milnor_exotic_7sphere_of_smooth_invariant (fun N => lam N = 0)
    (fun M N h => by simp only [hlam M N h]) (Mfam j) (hhomeo j) ?_ hsphere
  simp only [hval j]
  exact hj

end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.milnor_exotic_7sphere
#print axioms Frontier.twisted_seven_sphere_homeomorph
#print axioms Frontier.milnor_exotic_7sphere_of_smooth_invariant
#print axioms Frontier.milnor_exotic_7sphere_iff
#print axioms Frontier.milnor_exotic_7sphere_of_lambda
#print axioms Frontier.no_topological_invariant_separates
#print axioms Frontier.exists_odd_milnorLambda_ne_zero
#print axioms Frontier.nonempty_twistedSphere_homeomorph_sphere
#print axioms Frontier.exists_norm_preserving_extension

import Mathlib

/-!
# The Alexander trick (cone extension of a sphere homeomorphism)

Given a homeomorphism `f` of the unit sphere of a real normed space `E`, the *cone extension*
`coneMap f` is the radial extension `x ↦ ‖x‖ • f (x / ‖x‖)` (and `0 ↦ 0`).  It is a
norm-preserving homeomorphism of `E` which restricts to `f` on the unit sphere and maps the
closed unit ball onto itself.

This is the classical *Alexander trick*, and it is the topological input which makes every
"twisted sphere" homeomorphic to the standard sphere.
-/

namespace Frontier

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma norm_coe_unitSphere (y : sphere (0 : E) 1) : ‖(y : E)‖ = 1 :=
  mem_sphere_zero_iff_norm.mp y.2

omit [NormedSpace ℝ E] in
lemma coe_unitSphere_ne_zero (y : sphere (0 : E) 1) : (y : E) ≠ 0 := by
  intro h
  have := norm_coe_unitSphere y
  rw [h, norm_zero] at this
  exact zero_ne_one this

/-- Radial projection of a nonzero vector onto the unit sphere. -/
noncomputable def normalizePt {x : E} (hx : x ≠ 0) : sphere (0 : E) 1 :=
  ⟨‖x‖⁻¹ • x, by
    simp only [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    field_simp⟩

@[simp] lemma coe_normalizePt {x : E} (hx : x ≠ 0) : (normalizePt hx : E) = ‖x‖⁻¹ • x := rfl

open scoped Classical in
/-- The cone (radial) extension of a self-map of the unit sphere to the whole space. -/
noncomputable def coneMap (f : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) : E :=
  if h : x = 0 then 0 else ‖x‖ • (f (normalizePt h) : E)

@[simp] lemma coneMap_zero (f : sphere (0 : E) 1 → sphere (0 : E) 1) : coneMap f 0 = 0 := by
  simp [coneMap]

lemma coneMap_of_ne_zero (f : sphere (0 : E) 1 → sphere (0 : E) 1) {x : E} (hx : x ≠ 0) :
    coneMap f x = ‖x‖ • (f (normalizePt hx) : E) := by
  rw [coneMap, dif_neg hx]

/-- The cone extension preserves norms. -/
@[simp] lemma norm_coneMap (f : sphere (0 : E) 1 → sphere (0 : E) 1) (x : E) :
    ‖coneMap f x‖ = ‖x‖ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [coneMap_of_ne_zero f hx, norm_smul, norm_coe_unitSphere]
    simp

/-- The cone extension restricts to the original map on the unit sphere. -/
lemma coneMap_coe_sphere (f : sphere (0 : E) 1 → sphere (0 : E) 1) (x : sphere (0 : E) 1) :
    coneMap f (x : E) = f x := by
  have hx : (x : E) ≠ 0 := coe_unitSphere_ne_zero x
  have hn : ‖(x : E)‖ = 1 := norm_coe_unitSphere x
  have hpt : normalizePt hx = x := by
    apply Subtype.ext
    simp [hn]
  rw [coneMap_of_ne_zero f hx, hpt, hn, one_smul]

/-- The radial projection, as a continuous map on the open subspace of nonzero vectors. -/
noncomputable def radialProj : {x : E // x ≠ 0} → sphere (0 : E) 1 := fun p => normalizePt p.2

lemma continuous_radialProj : Continuous (radialProj (E := E)) := by
  apply Continuous.subtype_mk
  have h1 : Continuous fun p : {x : E // x ≠ 0} => ‖(p : E)‖ :=
    continuous_norm.comp continuous_subtype_val
  exact (h1.inv₀ fun p => norm_ne_zero_iff.mpr p.2).smul continuous_subtype_val

lemma continuous_coneMap {f : sphere (0 : E) 1 → sphere (0 : E) 1} (hf : Continuous f) :
    Continuous (coneMap f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, coneMap_zero]
    refine squeeze_zero_norm (fun y => le_of_eq (norm_coneMap f y)) ?_
    simpa using (continuous_norm (E := E)).tendsto' 0 0 (by simp)
  · have hopen : IsOpen {y : E | y ≠ 0} := isOpen_ne
    have hcont : ContinuousOn (coneMap f) {y : E | y ≠ 0} := by
      rw [continuousOn_iff_continuous_restrict]
      have hrestr : Set.restrict {y : E | y ≠ 0} (coneMap f)
          = fun p : {y : E // y ∈ {y : E | y ≠ 0}} =>
            ‖(p : E)‖ • (f (radialProj ⟨p.1, p.2⟩) : E) := by
        funext p
        exact coneMap_of_ne_zero f p.2
      rw [hrestr]
      exact (continuous_norm.comp continuous_subtype_val).smul
        (continuous_subtype_val.comp (hf.comp (continuous_radialProj.comp
          (Continuous.subtype_mk continuous_subtype_val _))))
    exact hcont.continuousAt (hopen.mem_nhds hx)

/-- Cone extensions compose: if `g ∘ f = id` on the sphere then `coneMap g ∘ coneMap f = id`. -/
lemma coneMap_comp_coneMap (f g : sphere (0 : E) 1 → sphere (0 : E) 1) (hgf : ∀ y, g (f y) = y)
    (x : E) : coneMap g (coneMap f x) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hFx : coneMap f x ≠ 0 := by
      intro h
      rw [← norm_eq_zero, norm_coneMap] at h
      exact hnx h
    rw [coneMap_of_ne_zero g hFx]
    have hpt : normalizePt hFx = f (normalizePt hx) := by
      apply Subtype.ext
      rw [coe_normalizePt, norm_coneMap, coneMap_of_ne_zero f hx, smul_smul,
        inv_mul_cancel₀ hnx, one_smul]
    rw [hpt, hgf, norm_coneMap, coe_normalizePt, smul_smul, mul_inv_cancel₀ hnx, one_smul]

/-- **The Alexander trick.**  A homeomorphism of the unit sphere of a real normed space extends
to a norm-preserving homeomorphism of the whole space (the radial, or cone, extension). -/
noncomputable def coneHomeomorph (f : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) : E ≃ₜ E where
  toFun := coneMap f
  invFun := coneMap f.symm
  left_inv x := coneMap_comp_coneMap _ _ (fun y => f.symm_apply_apply y) x
  right_inv x := coneMap_comp_coneMap _ _ (fun y => f.apply_symm_apply y) x
  continuous_toFun := continuous_coneMap f.continuous
  continuous_invFun := continuous_coneMap f.symm.continuous

@[simp] lemma coneHomeomorph_apply (f : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    coneHomeomorph f x = coneMap f x := rfl

/-- The Alexander extension preserves norms, hence maps the closed unit ball to itself. -/
lemma norm_coneHomeomorph (f : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) (x : E) :
    ‖coneHomeomorph f x‖ = ‖x‖ := norm_coneMap _ x

/-- The Alexander extension restricts to `f` on the unit sphere. -/
lemma coneHomeomorph_coe_sphere (f : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1)
    (x : sphere (0 : E) 1) : coneHomeomorph f (x : E) = f x := coneMap_coe_sphere _ x

/-- **The Alexander trick**, in existential form: every homeomorphism of the unit sphere is the
restriction of a norm-preserving self-homeomorphism of the ambient space. -/
theorem exists_norm_preserving_extension (f : sphere (0 : E) 1 ≃ₜ sphere (0 : E) 1) :
    ∃ F : E ≃ₜ E, (∀ x : sphere (0 : E) 1, F (x : E) = (f x : E)) ∧ ∀ x : E, ‖F x‖ = ‖x‖ :=
  ⟨coneHomeomorph f, coneHomeomorph_coe_sphere f, norm_coneHomeomorph f⟩

end Frontier

