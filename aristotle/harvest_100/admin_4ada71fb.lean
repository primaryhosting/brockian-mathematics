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

import Mathlib

/-!
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/
noncomputable def vec3 (x y z : ℝ) : E3 := WithLp.toLp 2 ![x, y, z]

@[simp] lemma vec3_zero (x y z : ℝ) : vec3 x y z 0 = x := rfl
@[simp] lemma vec3_one (x y z : ℝ) : vec3 x y z 1 = y := rfl
@[simp] lemma vec3_two (x y z : ℝ) : vec3 x y z 2 = z := rfl

lemma ext3 {u v : E3} (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) : u = v := by
  ext i; fin_cases i <;> assumption

lemma norm_sq3 (u : E3) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_three, sq_abs]

lemma inner3 (u v : E3) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three]; ring

@[simp] lemma smul3 (r : ℝ) (u : E3) (i : Fin 3) : (r • u) i = r * u i := rfl

@[simp] lemma add3 (u v : E3) (i : Fin 3) : (u + v) i = u i + v i := rfl

@[simp] lemma sub3 (u v : E3) (i : Fin 3) : (u - v) i = u i - v i := rfl

@[simp] lemma neg3 (u : E3) (i : Fin 3) : (-u) i = -(u i) := rfl

lemma eq_zero_iff3 {u : E3} : u = 0 ↔ u 0 = 0 ∧ u 1 = 0 ∧ u 2 = 0 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2⟩; exact ext3 h0 h1 h2

/-! ### The cross product -/

/-- The cross product of two vectors of `E3`. -/
noncomputable def cross3 (u v : E3) : E3 :=
  vec3 (u 1 * v 2 - u 2 * v 1) (u 2 * v 0 - u 0 * v 2) (u 0 * v 1 - u 1 * v 0)

@[simp] lemma cross3_zero (u v : E3) : cross3 u v 0 = u 1 * v 2 - u 2 * v 1 := rfl
@[simp] lemma cross3_one (u v : E3) : cross3 u v 1 = u 2 * v 0 - u 0 * v 2 := rfl
@[simp] lemma cross3_two (u v : E3) : cross3 u v 2 = u 0 * v 1 - u 1 * v 0 := rfl

lemma inner_cross3_left (u v : E3) : ⟪u, cross3 u v⟫ = 0 := by
  rw [inner3]; simp; ring

lemma inner_cross3_right (u v : E3) : ⟪v, cross3 u v⟫ = 0 := by
  rw [inner3]; simp; ring

/-- Lagrange's identity. -/
lemma norm_cross3_sq (u v : E3) : ‖cross3 u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - ⟪u, v⟫ ^ 2 := by
  rw [norm_sq3, norm_sq3, norm_sq3, inner3]; simp; ring

/-! ### Rotations about the coordinate axes -/

/-- The linear map rotating the `xy`-plane. -/
noncomputable def rotZlin (c s : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun v := vec3 (c * v 0 - s * v 1) (s * v 0 + c * v 1) (v 2)
  map_add' u v := by apply ext3 <;> simp <;> ring
  map_smul' r v := by apply ext3 <;> simp <;> ring

@[simp] lemma rotZlin_apply (c s : ℝ) (v : E3) :
    rotZlin c s v = vec3 (c * v 0 - s * v 1) (s * v 0 + c * v 1) (v 2) := rfl

/-- The linear map rotating the `yz`-plane. -/
noncomputable def rotXlin (c s : ℝ) : E3 →ₗ[ℝ] E3 where
  toFun v := vec3 (v 0) (c * v 1 - s * v 2) (s * v 1 + c * v 2)
  map_add' u v := by apply ext3 <;> simp <;> ring
  map_smul' r v := by apply ext3 <;> simp <;> ring

@[simp] lemma rotXlin_apply (c s : ℝ) (v : E3) :
    rotXlin c s v = vec3 (v 0) (c * v 1 - s * v 2) (s * v 1 + c * v 2) := rfl

/-- The rotation of the `xy`-plane as a linear isometry equivalence. -/
noncomputable def rotZequiv (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearEquiv.isometryOfInner
    { toLinearMap := rotZlin c s
      invFun := rotZlin c (-s)
      left_inv := by
        intro v
        refine ext3 ?_ ?_ rfl
        · simp; linear_combination (v 0) * h
        · simp; linear_combination (v 1) * h
      right_inv := by
        intro v
        refine ext3 ?_ ?_ rfl
        · simp; linear_combination (v 0) * h
        · simp; linear_combination (v 1) * h }
    (by
      intro u v
      rw [inner3, inner3]
      simp only [rotZlin_apply, vec3_zero, vec3_one, vec3_two, LinearEquiv.coe_mk]
      linear_combination (u 0 * v 0 + u 1 * v 1) * h)

/-- The rotation of the `yz`-plane as a linear isometry equivalence. -/
noncomputable def rotXequiv (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E3 ≃ₗᵢ[ℝ] E3 :=
  LinearEquiv.isometryOfInner
    { toLinearMap := rotXlin c s
      invFun := rotXlin c (-s)
      left_inv := by
        intro v
        refine ext3 rfl ?_ ?_
        · simp; linear_combination (v 1) * h
        · simp; linear_combination (v 2) * h
      right_inv := by
        intro v
        refine ext3 rfl ?_ ?_
        · simp; linear_combination (v 1) * h
        · simp; linear_combination (v 2) * h }
    (by
      intro u v
      rw [inner3, inner3]
      simp only [rotXlin_apply, vec3_zero, vec3_one, vec3_two, LinearEquiv.coe_mk]
      linear_combination (u 1 * v 1 + u 2 * v 2) * h)

@[simp] lemma rotZequiv_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (v : E3) :
    rotZequiv c s h v = vec3 (c * v 0 - s * v 1) (s * v 0 + c * v 1) (v 2) := rfl

@[simp] lemma rotXequiv_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (v : E3) :
    rotXequiv c s h v = vec3 (v 0) (c * v 1 - s * v 2) (s * v 1 + c * v 2) := rfl

lemma circle_sq (w : Circle) : ((w : ℂ).re) ^ 2 + ((w : ℂ).im) ^ 2 = 1 := by
  have h : ‖(w : ℂ)‖ = 1 := Circle.norm_coe w
  have := Complex.normSq_eq_norm_sq (w : ℂ)
  rw [h] at this
  simp only [Complex.normSq_apply] at this
  nlinarith [this]

/-- Rotations about the `z`-axis, as a group homomorphism from the unit circle. -/
noncomputable def rotZ : Circle →* (E3 ≃ₗᵢ[ℝ] E3) where
  toFun w := rotZequiv (w : ℂ).re (w : ℂ).im (circle_sq w)
  map_one' := by
    refine LinearIsometryEquiv.ext fun v => ?_
    refine ext3 ?_ ?_ rfl <;> simp
  map_mul' w z := by
    refine LinearIsometryEquiv.ext fun v => ?_
    refine ext3 ?_ ?_ rfl <;>
      simp [Circle.coe_mul, Complex.mul_re, Complex.mul_im] <;> ring

/-- Rotations about the `x`-axis, as a group homomorphism from the unit circle. -/
noncomputable def rotX : Circle →* (E3 ≃ₗᵢ[ℝ] E3) where
  toFun w := rotXequiv (w : ℂ).re (w : ℂ).im (circle_sq w)
  map_one' := by
    refine LinearIsometryEquiv.ext fun v => ?_
    refine ext3 rfl ?_ ?_ <;> simp
  map_mul' w z := by
    refine LinearIsometryEquiv.ext fun v => ?_
    refine ext3 rfl ?_ ?_ <;>
      simp [Circle.coe_mul, Complex.mul_re, Complex.mul_im] <;> ring

@[simp] lemma rotZ_apply (w : Circle) (v : E3) :
    rotZ w v = vec3 ((w : ℂ).re * v 0 - (w : ℂ).im * v 1)
      ((w : ℂ).im * v 0 + (w : ℂ).re * v 1) (v 2) := rfl

@[simp] lemma rotX_apply (w : Circle) (v : E3) :
    rotX w v = vec3 (v 0) ((w : ℂ).re * v 1 - (w : ℂ).im * v 2)
      ((w : ℂ).im * v 1 + (w : ℂ).re * v 2) := rfl

/-! ### Preservation of the cross product -/

/-- The subgroup of linear isometries preserving the cross product. -/
def CrossPreserving : Subgroup (E3 ≃ₗᵢ[ℝ] E3) where
  carrier := {g | ∀ u v : E3, g (cross3 u v) = cross3 (g u) (g v)}
  one_mem' := by intro u v; rfl
  mul_mem' := by
    intro f g hf hg u v
    show f (g (cross3 u v)) = cross3 (f (g u)) (f (g v))
    rw [hg u v, hf (g u) (g v)]
  inv_mem' := by
    intro g hg u v
    apply (g : E3 ≃ₗᵢ[ℝ] E3).injective
    show g (g⁻¹ (cross3 u v)) = g (cross3 (g⁻¹ u) (g⁻¹ v))
    rw [hg (g⁻¹ u) (g⁻¹ v)]
    show (g * g⁻¹) (cross3 u v) = cross3 ((g * g⁻¹) u) ((g * g⁻¹) v)
    rw [mul_inv_cancel]
    rfl

lemma rotZ_mem_crossPreserving (w : Circle) : rotZ w ∈ CrossPreserving := by
  intro u v
  have h := circle_sq w
  refine ext3 ?_ ?_ ?_ <;> simp <;> linear_combination (u 0 * v 1 - u 1 * v 0) * h

lemma rotX_mem_crossPreserving (w : Circle) : rotX w ∈ CrossPreserving := by
  intro u v
  have h := circle_sq w
  refine ext3 ?_ ?_ ?_ <;> simp <;> linear_combination (u 1 * v 2 - u 2 * v 1) * h

/-! ### Fixed points -/

/-- A cross-product-preserving isometry fixing two distinct, non-antipodal unit vectors is the
identity. -/
theorem eq_one_of_fixes_two {g : E3 ≃ₗᵢ[ℝ] E3} (hg : g ∈ CrossPreserving) {u v : E3}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u ≠ v) (huv' : u ≠ -v)
    (hgu : g u = u) (hgv : g v = v) : g = 1 := by
  set t : ℝ := ⟪u, v⟫ with ht
  -- `|t| < 1`
  have hCS : |t| ≤ 1 := by
    have := abs_real_inner_le_norm u v
    rwa [hu, hv, one_mul] at this
  have hsub : ‖u - v‖ ^ 2 = 2 - 2 * t := by
    rw [norm_sub_sq_real, hu, hv, ← ht]; ring
  have hadd : ‖u + v‖ ^ 2 = 2 + 2 * t := by
    rw [norm_add_sq_real, hu, hv, ← ht]; ring
  have ht1 : t ≠ 1 := by
    intro h
    apply huv
    have h0 : ‖u - v‖ ^ 2 = 0 := by rw [hsub, h]; ring
    have h1 : u - v = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact sub_eq_zero.mp h1
  have ht2 : t ≠ -1 := by
    intro h
    apply huv'
    have h0 : ‖u + v‖ ^ 2 = 0 := by rw [hadd, h]; ring
    have h1 : u + v = 0 := norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact eq_neg_of_add_eq_zero_left h1
  have htsq : t ^ 2 < 1 := by
    rcases lt_or_eq_of_le hCS with h | h
    · nlinarith [abs_nonneg t, sq_abs t]
    · exact absurd (abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h) (by
        rintro (rfl | rfl) <;> simp_all)
  -- the third vector
  set w : E3 := cross3 u v with hw
  have hwnorm : ‖w‖ ^ 2 = 1 - t ^ 2 := by rw [hw, norm_cross3_sq, hu, hv, ← ht]; ring
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hwnorm
    simp at hwnorm
    nlinarith
  have hgw : g w = w := by rw [hw, hg u v, hgu, hgv]
  -- the second, orthogonalized vector
  set v' : E3 := v - t • u with hv'
  have hgv' : g v' = v' := by rw [hv', map_sub, map_smul, hgu, hgv]
  have hinner_uv' : ⟪u, v'⟫ = 0 := by
    rw [hv', inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu, ← ht]
    ring
  have hv'ne : v' ≠ 0 := by
    intro h
    have : v = t • u := by
      have := sub_eq_zero.mp (by rw [← hv']; exact h)
      exact this
    rw [this, norm_smul, hu] at hv
    simp at hv
    nlinarith [sq_abs t]
  have hinner_uw : ⟪u, w⟫ = 0 := inner_cross3_left u v
  have hinner_v'w : ⟪v', w⟫ = 0 := by
    rw [hv', inner_sub_left, real_inner_smul_left, hw, inner_cross3_right, inner_cross3_left]
    ring
  -- linear independence
  have hli : LinearIndependent ℝ ![u, v', w] := by
    refine linearIndependent_of_ne_zero_of_inner_eq_zero ?_ ?_
    · intro i
      fin_cases i
      · intro h; rw [h] at hu; simp at hu
      · exact hv'ne
      · exact hwne
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all <;>
        first
          | exact hinner_uv'
          | exact hinner_uw
          | exact hinner_v'w
          | (rw [real_inner_comm]; assumption)
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ E3 := by
    simp [finrank_euclideanSpace]
  have hspan : Submodule.span ℝ (Set.range ![u, v', w]) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank hcard
  -- conclude
  have hfix : ∀ x : E3, g x = x := by
    have hsub : Submodule.span ℝ (Set.range ![u, v', w]) ≤
        LinearMap.eqLocus (g : E3 →ₗ[ℝ] E3) LinearMap.id := by
      rw [Submodule.span_le]
      rintro x ⟨i, rfl⟩
      fin_cases i
      · exact hgu
      · exact hgv'
      · exact hgw
    intro x
    have : x ∈ LinearMap.eqLocus (g : E3 →ₗ[ℝ] E3) LinearMap.id := by
      rw [hspan] at hsub; exact hsub trivial
    exact this
  exact LinearIsometryEquiv.ext hfix

/-- The fixed points on the unit sphere of a nontrivial cross-product-preserving isometry form a
countable (indeed, at most two-element) set. -/
theorem countable_fixedPoints {g : E3 ≃ₗᵢ[ℝ] E3} (hg : g ∈ CrossPreserving) (hne : g ≠ 1) :
    {x : E3 | ‖x‖ = 1 ∧ g x = x}.Countable := by
  rcases Set.eq_empty_or_nonempty {x : E3 | ‖x‖ = 1 ∧ g x = x} with h | ⟨u, hu⟩
  · rw [h]; exact Set.countable_empty
  · have hsub : {x : E3 | ‖x‖ = 1 ∧ g x = x} ⊆ {u, -u} := by
      intro v hv
      by_contra hcon
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
      exact hne (eq_one_of_fixes_two hg hu.1 hv.1 (fun h => hcon.1 h.symm)
        (fun h => hcon.2 (by rw [h]; simp)) hu.2 hv.2)
    exact (Set.Finite.subset (Set.finite_insert u (Set.finite_singleton (-u))) hsub).countable

end BT

import RequestProject.BT.Basic
import RequestProject.BT.FreeComb

/-!
# Free actions of the free group of rank two are paradoxical

If a group `G` acting on `X` contains a free group of rank two acting freely on an invariant
subset `E`, then `E` is `G`-paradoxical.
-/

open Set Pointwise BT.FreeComb

namespace BT

/-- If the free group of rank two acts freely on an invariant set `E` (through a group `G`),
then `E` is `G`-paradoxical. -/
theorem isParadoxical_of_freeAction {X G : Type*} [Group G] [MulAction G X]
    (φ : F →* G) (E : Set X)
    (hinv : ∀ (w : F) {x : X}, x ∈ E → φ w • x ∈ E)
    (hfree : ∀ (w : F) {x : X}, x ∈ E → w ≠ 1 → φ w • x ≠ x) :
    IsParadoxical G E := by
  classical
  -- the orbit equivalence relation
  let s : Setoid X :=
    { r := fun x y => ∃ w : F, φ w • x = y
      iseqv :=
        { refl := fun x => ⟨1, by simp⟩
          symm := by
            rintro x y ⟨w, rfl⟩
            exact ⟨w⁻¹, by rw [map_inv, inv_smul_smul]⟩
          trans := by
            rintro x y z ⟨w₁, rfl⟩ ⟨w₂, rfl⟩
            exact ⟨w₂ * w₁, by rw [map_mul, mul_smul]⟩ } }
  set rep : X → X := fun x => (Quotient.mk s x).out with hrep_def
  have hrep_rel : ∀ x : X, ∃ w : F, φ w • rep x = x := by
    intro x
    exact Quotient.exact (Quotient.out_eq (Quotient.mk s x))
  have hrep_eq : ∀ x y : X, (∃ w : F, φ w • x = y) → rep x = rep y := by
    intro x y h
    simp only [hrep_def]
    congr 1
    exact Quotient.sound h
  set ww : X → F := fun x => (hrep_rel x).choose with hww_def
  have hww : ∀ x : X, φ (ww x) • rep x = x := fun x => (hrep_rel x).choose_spec
  have hrepE : ∀ {x : X}, x ∈ E → rep x ∈ E := by
    intro x hx
    obtain ⟨w, hw⟩ := hrep_rel x
    have hx' : rep x = φ w⁻¹ • x := by
      conv_rhs => rw [← hw]
      rw [map_inv, inv_smul_smul]
    rw [hx']
    exact hinv _ hx
  have huniq : ∀ {m : X}, m ∈ E → ∀ u v : F, φ u • m = φ v • m → u = v := by
    intro m hm u v huv
    have h1 : φ (v⁻¹ * u) • m = m := by
      rw [map_mul, mul_smul, huv, map_inv, inv_smul_smul]
    by_contra hne
    exact hfree (v⁻¹ * u) hm (fun h0 => hne (inv_mul_eq_one.mp h0).symm) h1
  have hww_smul : ∀ (u : F) {x : X}, x ∈ E → ww (φ u • x) = u * ww x := by
    intro u x hx
    have h1 : rep (φ u • x) = rep x := (hrep_eq x (φ u • x) ⟨u, rfl⟩).symm
    have h2 : φ (ww (φ u • x)) • rep x = φ u • x := by
      rw [← h1]; exact hww _
    have h3 : φ (u * ww x) • rep x = φ u • x := by rw [map_mul, mul_smul, hww x]
    exact huniq (hrepE hx) _ _ (h2.trans h3.symm)
  -- pieces of `E` indexed by subsets of the free group
  set P : Set F → Set X := fun S => {x | x ∈ E ∧ ww x ∈ S} with hP_def
  have hP_sub : ∀ S, P S ⊆ E := fun S x hx => hx.1
  have hP_smul : ∀ (u : F) (S : Set F), φ u • P S = P (u • S) := by
    intro u S
    ext y
    constructor
    · rintro ⟨x, ⟨hxE, hxS⟩, rfl⟩
      refine ⟨hinv _ hxE, ?_⟩
      rw [hww_smul u hxE]
      exact ⟨ww x, hxS, rfl⟩
    · rintro ⟨hyE, v, hvS, hv⟩
      have hv' : u * v = ww y := hv
      refine ⟨φ u⁻¹ • y, ⟨hinv _ hyE, ?_⟩, ?_⟩
      · rw [hww_smul u⁻¹ hyE, ← hv']
        simpa using hvS
      · show φ u • (φ u⁻¹ • y) = y
        rw [map_inv, smul_inv_smul]
  have hP_disj : ∀ S T : Set F, Disjoint S T → Disjoint (P S) (P T) := by
    intro S T hST
    rw [Set.disjoint_left]
    rintro x ⟨-, hxS⟩ ⟨-, hxT⟩
    exact (hST.le_bot ⟨hxS, hxT⟩ : ww x ∈ (⊥ : Set F))
  obtain ⟨A, B, C, D, hcover, hAB, hCD, hABCD, hcovA, hdisA, hcovC, hdisC⟩ :=
    exists_paradoxical_partition
  refine ⟨P A ∪ P B, P C ∪ P D, ?_, ?_, ?_, ?_⟩
  · -- the two parts cover `E`
    apply Set.Subset.antisymm
    · rintro x ((hx | hx) | (hx | hx)) <;> exact hx.1
    · intro x hx
      rcases hcover (ww x) with h | h | h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inl (Or.inr ⟨hx, h⟩)
      · exact Or.inr (Or.inl ⟨hx, h⟩)
      · exact Or.inr (Or.inr ⟨hx, h⟩)
  · -- the two parts are disjoint
    rw [Set.disjoint_left]
    rintro x hx hx'
    have h1 : ww x ∈ A ∪ B := by
      rcases hx with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    have h2 : ww x ∈ C ∪ D := by
      rcases hx' with h | h
      · exact Or.inl h.2
      · exact Or.inr h.2
    exact (hABCD.le_bot ⟨h1, h2⟩ : ww x ∈ (⊥ : Set F))
  · -- first part is equidecomposable with `E`
    refine Equidecomposable.ofTwoPieces (1 : G) (φ ga) (hP_disj _ _ hAB) ?_ ?_
    · rw [MulAction.one_smul, hP_smul]
      exact hP_disj _ _ hdisA
    · rw [MulAction.one_smul, hP_smul]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hcovA (ww x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (hx | hx) <;> exact hx.1
  · -- second part is equidecomposable with `E`
    refine Equidecomposable.ofTwoPieces (1 : G) (φ gb) (hP_disj _ _ hCD) ?_ ?_
    · rw [MulAction.one_smul, hP_smul]
      exact hP_disj _ _ hdisC
    · rw [MulAction.one_smul, hP_smul]
      apply Set.Subset.antisymm
      · intro x hx
        rcases hcovC (ww x) with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
      · rintro x (hx | hx) <;> exact hx.1

end BT

import Mathlib

/-!
# Equidecomposability and paradoxical sets

Basic definitions and API used in the formalization of the Banach–Tarski paradox.
-/

open Set Pointwise

namespace BT

/-- The isometry group of a metric space acts on the space. -/
instance isometryEquivAction (M : Type*) [PseudoEMetricSpace M] : MulAction (M ≃ᵢ M) M where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma isometryEquiv_smul_def {M : Type*} [PseudoEMetricSpace M] (g : M ≃ᵢ M) (x : M) :
    g • x = g x := rfl

/-- The group of linear isometry equivalences of a normed space acts on the space. -/
instance linearIsometryEquivAction (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E] :
    MulAction (E ≃ₗᵢ[ℝ] E) E where
  smul g x := g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] lemma linearIsometryEquiv_smul_def {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] (g : E ≃ₗᵢ[ℝ] E) (x : E) : g • x = g x := rfl

variable {X : Type*} (G : Type*) [Group G] [MulAction G X]

/-- Two sets `A B : Set X` are *equidecomposable* with respect to a group `G` acting on `X`
if there is a bijection `A → B` which is obtained by cutting `A` into finitely many pieces
and moving each piece by a single element of `G`.  This is expressed by requiring a bijection
`f : A → B` and a *finite* set `S` of group elements such that every point of `A` is moved by
some element of `S`. -/
def Equidecomposable (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Finset G), Set.BijOn f A B ∧ ∀ a ∈ A, ∃ g ∈ S, f a = g • a

/-- A set `S` is `G`-paradoxical if it can be split into two disjoint pieces, each of which is
equidecomposable with the whole of `S`. -/
def IsParadoxical (S : Set X) : Prop :=
  ∃ A B : Set X, A ∪ B = S ∧ Disjoint A B ∧ Equidecomposable G A S ∧ Equidecomposable G B S

variable {G}

lemma Equidecomposable.refl (A : Set X) : Equidecomposable G A A :=
  ⟨id, {1}, Set.bijOn_id A, fun a _ => ⟨1, by simp⟩⟩

lemma Equidecomposable.symm {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable G B A := by
  classical
  obtain ⟨f, S, hbij, hS⟩ := h
  rcases isEmpty_or_nonempty X with hX | hX
  · rw [Set.eq_empty_of_isEmpty A, Set.eq_empty_of_isEmpty B]
    exact Equidecomposable.refl _
  refine ⟨Function.invFunOn f A, S⁻¹, hbij.invOn_invFunOn.symm.bijOn
    hbij.surjOn.mapsTo_invFunOn hbij.mapsTo, ?_⟩
  · intro b hb
    have hex : ∃ a ∈ A, f a = b := (Set.mem_image _ _ _).mp (hbij.surjOn hb)
    have hmem : Function.invFunOn f A b ∈ A := Function.invFunOn_mem hex
    have hfb : f (Function.invFunOn f A b) = b := Function.invFunOn_eq hex
    obtain ⟨g, hg, hgb⟩ := hS _ hmem
    refine ⟨g⁻¹, by simpa using hg, ?_⟩
    conv_rhs => rw [← hfb, hgb]
    rw [inv_smul_smul]

lemma Equidecomposable.trans {A B C : Set X} (h₁ : Equidecomposable G A B)
    (h₂ : Equidecomposable G B C) : Equidecomposable G A C := by
  classical
  obtain ⟨f, S, hbij, hS⟩ := h₁
  obtain ⟨f', S', hbij', hS'⟩ := h₂
  refine ⟨f' ∘ f, S' * S, hbij'.comp hbij, ?_⟩
  intro a ha
  obtain ⟨g, hg, hga⟩ := hS a ha
  obtain ⟨g', hg', hg'a⟩ := hS' (f a) (hbij.mapsTo ha)
  refine ⟨g' * g, Finset.mul_mem_mul hg' hg, ?_⟩
  show f' (f a) = (g' * g) • a
  rw [hg'a, hga, mul_smul]

/-- Restricting an equidecomposition to a subset. -/
lemma Equidecomposable.mono_left {A B A' : Set X} {f : X → X} {S : Finset G}
    (hbij : Set.BijOn f A B) (hS : ∀ a ∈ A, ∃ g ∈ S, f a = g • a) (hA' : A' ⊆ A) :
    Equidecomposable G A' (f '' A') :=
  ⟨f, S, (hbij.injOn.mono hA').bijOn_image, fun a ha => hS a (hA' ha)⟩

/-- Building an equidecomposition out of two pieces. -/
lemma Equidecomposable.ofTwoPieces {A₁ A₂ B : Set X} (g₁ g₂ : G)
    (hdisj : Disjoint A₁ A₂) (hdisj' : Disjoint (g₁ • A₁) (g₂ • A₂))
    (hB : B = g₁ • A₁ ∪ g₂ • A₂) :
    Equidecomposable G (A₁ ∪ A₂) B := by
  classical
  refine ⟨fun x => if x ∈ A₁ then g₁ • x else g₂ • x, {g₁, g₂}, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro x (hx | hx)
    · simp only [hx, if_true, hB]
      exact Or.inl ⟨x, hx, rfl⟩
    · have hx1 : x ∉ A₁ := fun h => (hdisj.le_bot ⟨h, hx⟩ : x ∈ (⊥ : Set X))
      simp only [hx1, if_false, hB]
      exact Or.inr ⟨x, hx, rfl⟩
  · intro x hx y hy hxy
    by_cases hx1 : x ∈ A₁ <;> by_cases hy1 : y ∈ A₁
    · simp only [hx1, hy1, if_true] at hxy
      exact MulAction.injective g₁ hxy
    · have hy2 : y ∈ A₂ := hy.resolve_left hy1
      simp only [hx1, hy1, if_true, if_false] at hxy
      exact absurd ⟨⟨x, hx1, rfl⟩, ⟨y, hy2, hxy.symm⟩⟩
        (fun h => (hdisj'.le_bot h : (g₁ • x) ∈ (⊥ : Set X)))
    · have hx2 : x ∈ A₂ := hx.resolve_left hx1
      simp only [hx1, hy1, if_true, if_false] at hxy
      exact absurd ⟨⟨y, hy1, rfl⟩, ⟨x, hx2, hxy⟩⟩
        (fun h => (hdisj'.le_bot h : (g₁ • y) ∈ (⊥ : Set X)))
    · simp only [hx1, hy1, if_false] at hxy
      exact MulAction.injective g₂ hxy
  · rintro y hy
    rw [hB] at hy
    rcases hy with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact ⟨x, Or.inl hx, by simp [hx]⟩
    · have hx1 : x ∉ A₁ := fun h => (hdisj.le_bot ⟨h, hx⟩ : x ∈ (⊥ : Set X))
      exact ⟨x, Or.inr hx, by simp [hx1]⟩
  · rintro x (hx | hx)
    · exact ⟨g₁, by simp, by simp [hx]⟩
    · by_cases hx1 : x ∈ A₁
      · exact ⟨g₁, by simp, by simp [hx1]⟩
      · exact ⟨g₂, by simp, by simp [hx1]⟩

/-- Equidecomposability can be transported along a group hom compatible with the actions. -/
lemma Equidecomposable.map {H : Type*} [Group H] [MulAction H X] (φ : G →* H)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) {A B : Set X} (h : Equidecomposable G A B) :
    Equidecomposable H A B := by
  classical
  obtain ⟨f, S, hbij, hS⟩ := h
  refine ⟨f, S.image φ, hbij, fun a ha => ?_⟩
  obtain ⟨g, hg, hga⟩ := hS a ha
  exact ⟨φ g, Finset.mem_image_of_mem _ hg, by rw [hφ]; exact hga⟩

lemma IsParadoxical.map {H : Type*} [Group H] [MulAction H X] (φ : G →* H)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) {S : Set X} (h : IsParadoxical G S) :
    IsParadoxical H S := by
  obtain ⟨A, B, hunion, hdisj, hA, hB⟩ := h
  exact ⟨A, B, hunion, hdisj, hA.map φ hφ, hB.map φ hφ⟩

/-- Paradoxicality is invariant under equidecomposability. -/
lemma IsParadoxical.congr {S T : Set X} (hST : Equidecomposable G S T)
    (h : IsParadoxical G S) : IsParadoxical G T := by
  obtain ⟨A, B, hunion, hdisj, hA, hB⟩ := h
  obtain ⟨f, F, hbij, hF⟩ := id hST
  have hA' : A ⊆ S := hunion ▸ subset_union_left
  have hB' : B ⊆ S := hunion ▸ subset_union_right
  refine ⟨f '' A, f '' B, ?_, ?_, ?_, ?_⟩
  · rw [← Set.image_union, hunion, hbij.image_eq]
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩
    have : a = b := hbij.injOn (hA' ha) (hB' hb) hab.symm
    exact (hdisj.le_bot ⟨ha, this ▸ hb⟩ : a ∈ (⊥ : Set X))
  · exact ((Equidecomposable.mono_left hbij hF hA').symm.trans hA).trans hST
  · exact ((Equidecomposable.mono_left hbij hF hB').symm.trans hB).trans hST

end BT

import Mathlib

/-!
# A paradoxical partition of the free group of rank two

The free group `F₂` on two generators `a`, `b` can be partitioned into four pieces
`A`, `B`, `C`, `D` such that `F₂ = A ⊔ a • B = C ⊔ b • D`.  This is the combinatorial
heart of the Banach–Tarski paradox.
-/

open FreeGroup Set Pointwise

namespace BT.FreeComb

/-- The free group on two generators. -/
abbrev F := FreeGroup (Fin 2)

/-- The first generator. -/
def ga : F := FreeGroup.of 0

/-- The second generator. -/
def gb : F := FreeGroup.of 1

lemma ga_eq : ga = FreeGroup.mk [(0, true)] := rfl

lemma gb_eq : gb = FreeGroup.mk [(1, true)] := rfl

lemma ga_inv_eq : ga⁻¹ = FreeGroup.mk [((0 : Fin 2), false)] := by
  rw [ga_eq, FreeGroup.inv_mk]; simp [FreeGroup.invRev]

lemma gb_inv_eq : gb⁻¹ = FreeGroup.mk [((1 : Fin 2), false)] := by
  rw [gb_eq, FreeGroup.inv_mk]; simp [FreeGroup.invRev]

section Words

variable {α : Type} [DecidableEq α]

/-- Multiplying on the left by a letter which does not cancel prepends it to the word. -/
lemma toWord_letter_mul {p : α × Bool} {w : FreeGroup α}
    (h : ∀ q, w.toWord.head? = some q → (p.1 = q.1 → p.2 = q.2)) :
    (FreeGroup.mk [p] * w).toWord = p :: w.toWord := by
  have h1 : FreeGroup.mk [p] * w = FreeGroup.mk (p :: w.toWord) := by
    rw [← FreeGroup.mk_toWord (x := w), FreeGroup.mul_mk]; simp
  rw [h1, FreeGroup.toWord_mk]
  refine FreeGroup.IsReduced.reduce_eq ?_
  cases hw : w.toWord with
  | nil => simp
  | cons q t =>
      rw [FreeGroup.isReduced_cons_cons]
      refine ⟨h q (by simp [hw]), ?_⟩
      rw [← hw]; exact FreeGroup.isReduced_toWord

/-- Multiplying on the left by the inverse of the first letter deletes it. -/
lemma toWord_letter_mul_cancel {p : α × Bool} {t : List (α × Bool)} {w : FreeGroup α}
    (hw : w.toWord = (p.1, !p.2) :: t) :
    (FreeGroup.mk [p] * w).toWord = t := by
  have h1 : FreeGroup.mk [p] * w = FreeGroup.mk (p :: (p.1, !p.2) :: t) := by
    rw [← FreeGroup.mk_toWord (x := w), hw, FreeGroup.mul_mk]; simp
  have h2 : FreeGroup.mk (p :: (p.1, !p.2) :: t) = FreeGroup.mk t := by
    have hstep : FreeGroup.Red.Step (p :: (p.1, !p.2) :: t) t := by
      have := @FreeGroup.Red.Step.not α [] t p.1 p.2
      simpa using this
    exact Quot.sound hstep
  have h3 : FreeGroup.IsReduced t := by
    have hred := FreeGroup.isReduced_toWord (x := w)
    rw [hw] at hred
    exact hred.infix (List.infix_cons (List.infix_refl t))
  rw [h1, h2, FreeGroup.toWord_mk, h3.reduce_eq]

end Words

/-- The set of elements whose reduced word starts with the letter `p`. -/
def St (p : Fin 2 × Bool) : Set F := {w : F | w.toWord.head? = some p}

/-- The set of nonpositive powers of the first generator. -/
def PowA : Set F := {w : F | ∃ n : ℕ, w.toWord = List.replicate n (0, false)}

/-- The first piece. -/
def setA : Set F := St (0, true) ∪ PowA

/-- The second piece. -/
def setB : Set F := St (0, false) \ PowA

/-- The third piece. -/
def setC : Set F := St (1, true)

/-- The fourth piece. -/
def setD : Set F := St (1, false)

lemma mem_St {p : Fin 2 × Bool} {w : F} : w ∈ St p ↔ w.toWord.head? = some p := Iff.rfl

lemma St_disjoint {p q : Fin 2 × Bool} (hpq : p ≠ q) : Disjoint (St p) (St q) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_St] at hw hw'
  exact hpq (Option.some_injective _ (hw.symm.trans hw'))

lemma PowA_head {w : F} (hw : w ∈ PowA) :
    w.toWord.head? = none ∨ w.toWord.head? = some (0, false) := by
  obtain ⟨n, hn⟩ := hw
  cases n with
  | zero => left; simp [hn]
  | succ m => right; simp [hn, List.replicate_succ]

lemma PowA_disjoint_St {p : Fin 2 × Bool} (hp : p ≠ (0, false)) : Disjoint PowA (St p) := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rw [mem_St] at hw'
  rcases PowA_head hw with h | h <;> rw [hw'] at h
  · simp at h
  · exact hp (Option.some_injective _ h)

/-- The four pieces cover the group. -/
lemma cover (w : F) : w ∈ setA ∨ w ∈ setB ∨ w ∈ setC ∨ w ∈ setD := by
  by_cases hP : w ∈ PowA
  · exact Or.inl (Or.inr hP)
  cases hw : w.toWord with
  | nil =>
      exact absurd (show w ∈ PowA from ⟨0, by rw [hw]; rfl⟩) hP
  | cons q t =>
      obtain ⟨i, β⟩ := q
      have hhead : w.toWord.head? = some (i, β) := by rw [hw]; rfl
      fin_cases i <;> cases β
      · exact Or.inr (Or.inl ⟨show w.toWord.head? = _ from hhead, hP⟩)
      · exact Or.inl (Or.inl (show w.toWord.head? = _ from hhead))
      · exact Or.inr (Or.inr (Or.inr (show w.toWord.head? = _ from hhead)))
      · exact Or.inr (Or.inr (Or.inl (show w.toWord.head? = _ from hhead)))

lemma disjoint_AB : Disjoint setA setB := by
  rw [Set.disjoint_left]
  rintro w (hw | hw) ⟨hw', hw''⟩
  · exact (St_disjoint (by decide)).le_bot ⟨hw, hw'⟩
  · exact hw'' hw

lemma disjoint_CD : Disjoint setC setD :=
  St_disjoint (by decide)

lemma disjoint_AB_CD : Disjoint (setA ∪ setB) (setC ∪ setD) := by
  rw [Set.disjoint_left]
  rintro w hw hw'
  simp only [setC, setD] at hw'
  have hw0 : w.toWord.head? = some (0, true) ∨ w.toWord.head? = some (0, false) := by
    rcases hw with (hw | hw) | ⟨hw, -⟩
    · exact Or.inl hw
    · rcases PowA_head hw with h | h
      · exfalso
        rcases hw' with hw' | hw' <;> rw [hw'] at h <;> simp at h
      · exact Or.inr h
    · exact Or.inr hw
  rcases hw' with hw' | hw' <;> rcases hw0 with h | h <;>
    rw [hw'] at h <;> exact absurd (Option.some_injective _ h) (by decide)

/-- The key identity `F = A ⊔ a • B`. -/
lemma coverA (w : F) : w ∈ setA ∨ w ∈ ga • setB := by
  by_cases hA : w ∈ setA
  · exact Or.inl hA
  right
  have hnotSt : w.toWord.head? ≠ some (0, true) := fun h => hA (Or.inl h)
  have hnotPow : w ∉ PowA := fun h => hA (Or.inr h)
  refine ⟨ga⁻¹ * w, ⟨?_, ?_⟩, by simp⟩
  · -- `ga⁻¹ * w` starts with `(0, false)`
    have : (ga⁻¹ * w).toWord = ((0 : Fin 2), false) :: w.toWord := by
      rw [ga_inv_eq]
      refine toWord_letter_mul ?_
      rintro ⟨i, β⟩ hq hi
      simp only at hi
      subst hi
      cases β
      · rfl
      · exact absurd hq hnotSt
    rw [mem_St, this]
    simp
  · rintro ⟨n, hn⟩
    have hthis : (ga⁻¹ * w).toWord = ((0 : Fin 2), false) :: w.toWord := by
      rw [ga_inv_eq]
      refine toWord_letter_mul ?_
      rintro ⟨i, β⟩ hq hi
      simp only at hi
      subst hi
      cases β
      · rfl
      · exact absurd hq hnotSt
    rw [hthis] at hn
    cases n with
    | zero => simp at hn
    | succ m =>
        rw [List.replicate_succ] at hn
        exact hnotPow ⟨m, (List.cons.injEq _ _ _ _ ▸ hn).2⟩

lemma disjointA : Disjoint setA (ga • setB) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨v, ⟨hv1, hv2⟩, rfl⟩
  rw [mem_St] at hv1
  obtain ⟨t, ht⟩ : ∃ t, v.toWord = ((0 : Fin 2), false) :: t := by
    cases hvw : v.toWord with
    | nil => rw [hvw] at hv1; simp at hv1
    | cons q t =>
        rw [hvw] at hv1
        simp only [List.head?_cons, Option.some_inj] at hv1
        exact ⟨t, by rw [hv1]⟩
  have hmul : (ga • v).toWord = t := by
    rw [smul_eq_mul, ga_eq]
    exact toWord_letter_mul_cancel (p := ((0 : Fin 2), true)) (by simpa using ht)
  have hred : FreeGroup.IsReduced (((0 : Fin 2), false) :: t) := by
    rw [← ht]; exact FreeGroup.isReduced_toWord
  rcases hw with hw | hw
  · rw [mem_St, hmul] at hw
    cases t with
    | nil => simp at hw
    | cons q t' =>
        simp only [List.head?_cons, Option.some_inj] at hw
        rw [FreeGroup.isReduced_cons_cons] at hred
        have := hred.1 (by rw [hw])
        simp [hw] at this
  · obtain ⟨n, hn⟩ := hw
    rw [hmul] at hn
    exact hv2 ⟨n + 1, by rw [ht, hn, List.replicate_succ]⟩

/-- The key identity `F = C ⊔ b • D`. -/
lemma coverC (w : F) : w ∈ setC ∨ w ∈ gb • setD := by
  by_cases hC : w ∈ setC
  · exact Or.inl hC
  right
  have hnotSt : w.toWord.head? ≠ some (1, true) := hC
  refine ⟨gb⁻¹ * w, ?_, by simp⟩
  have : (gb⁻¹ * w).toWord = ((1 : Fin 2), false) :: w.toWord := by
    rw [gb_inv_eq]
    refine toWord_letter_mul ?_
    rintro ⟨i, β⟩ hq hi
    simp only at hi
    subst hi
    cases β
    · rfl
    · exact absurd hq hnotSt
  rw [setD, mem_St, this]
  simp

lemma disjointC : Disjoint setC (gb • setD) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨v, hv, rfl⟩
  rw [setD, mem_St] at hv
  obtain ⟨t, ht⟩ : ∃ t, v.toWord = ((1 : Fin 2), false) :: t := by
    cases hvw : v.toWord with
    | nil => rw [hvw] at hv; simp at hv
    | cons q t =>
        rw [hvw] at hv
        simp only [List.head?_cons, Option.some_inj] at hv
        exact ⟨t, by rw [hv]⟩
  have hmul : (gb • v).toWord = t := by
    rw [smul_eq_mul, gb_eq]
    exact toWord_letter_mul_cancel (p := ((1 : Fin 2), true)) (by simpa using ht)
  have hred : FreeGroup.IsReduced (((1 : Fin 2), false) :: t) := by
    rw [← ht]; exact FreeGroup.isReduced_toWord
  rw [setC, mem_St, hmul] at hw
  cases t with
  | nil => simp at hw
  | cons q t' =>
      simp only [List.head?_cons, Option.some_inj] at hw
      rw [FreeGroup.isReduced_cons_cons] at hred
      have := hred.1 (by rw [hw])
      simp [hw] at this

/-- **Paradoxical decomposition of the free group of rank two.** -/
theorem exists_paradoxical_partition :
    ∃ A B C D : Set F,
      (∀ w : F, w ∈ A ∨ w ∈ B ∨ w ∈ C ∨ w ∈ D) ∧
      Disjoint A B ∧ Disjoint C D ∧ Disjoint (A ∪ B) (C ∪ D) ∧
      (∀ w : F, w ∈ A ∨ w ∈ ga • B) ∧ Disjoint A (ga • B) ∧
      (∀ w : F, w ∈ C ∨ w ∈ gb • D) ∧ Disjoint C (gb • D) :=
  ⟨setA, setB, setC, setD, cover, disjoint_AB, disjoint_CD, disjoint_AB_CD,
    coverA, disjointA, coverC, disjointC⟩

end BT.FreeComb

