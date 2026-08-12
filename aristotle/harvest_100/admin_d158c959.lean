import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/
noncomputable def ballShift : BT.E := !₂[3, 0, 0]

theorem norm_ballShift : ‖ballShift‖ = 3 := by
  rw [EuclideanSpace.norm_eq]
  simp [ballShift, Fin.sum_univ_three]

theorem disjoint_balls :
    Disjoint (closedBall (0 : BT.E) 1) (closedBall ballShift 1) := by
  refine Set.disjoint_left.2 ?_
  intro y hy hy'
  rw [Metric.mem_closedBall, dist_zero_right] at hy
  rw [Metric.mem_closedBall, dist_eq_norm] at hy'
  have h3 : ‖ballShift‖ ≤ ‖y‖ + ‖y - ballShift‖ := by
    calc ‖ballShift‖ = ‖y - (y - ballShift)‖ := by congr 1; abel
      _ ≤ ‖y‖ + ‖y - ballShift‖ := norm_sub_le _ _
  rw [norm_ballShift] at h3
  linarith

theorem equidec_ball_shift :
    BT.Equidec (BT.E ≃ᵢ BT.E) (closedBall (0 : BT.E) 1) (closedBall ballShift 1) := by
  have h := BT.Equidec.smul_set (IsometryEquiv.addRight ballShift) (closedBall (0 : BT.E) 1)
  have himg : (IsometryEquiv.addRight ballShift) • (closedBall (0 : BT.E) 1)
      = closedBall ballShift 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖x + ballShift - ballShift‖ ≤ 1
      simpa using hx
    · intro hy
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      refine ⟨y - ballShift, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right]; exact hy
      · show y - ballShift + ballShift = y
        abel
  rwa [himg] at h

/-- **The Banach-Tarski paradox.**  The closed unit ball of `ℝ³` can be partitioned into
finitely many pieces which, after moving each piece by an isometry of `ℝ³`, form a partition
of two disjoint copies of the closed unit ball. -/
theorem Banach_Tarski :
    ∃ (n : ℕ) (P : Fin n → Set BT.E) (g : Fin n → (BT.E ≃ᵢ BT.E)),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧
      (⋃ i, P i) = closedBall (0 : BT.E) 1 ∧
      (∀ i j, i ≠ j → Disjoint (g i '' P i) (g j '' P j)) ∧
      (⋃ i, g i '' P i) = closedBall (0 : BT.E) 1 ∪ closedBall ballShift 1 ∧
      Disjoint (closedBall (0 : BT.E) 1) (closedBall ballShift 1) := by
  have hdouble : BT.Equidec (BT.E ≃ᵢ BT.E) (closedBall (0 : BT.E) 1)
      (closedBall (0 : BT.E) 1 ∪ closedBall ballShift 1) :=
    BT.paradoxical_ball.doubling equidec_ball_shift disjoint_balls
  obtain ⟨n, P, g, hPdisj, hPunion, hgdisj, hgunion⟩ := hdouble.exists_partition
  have hsmul : ∀ i, g i • P i = g i '' P i := fun i => rfl
  refine ⟨n, P, g, hPdisj, hPunion, ?_, ?_, disjoint_balls⟩
  · intro i j hij
    have := hgdisj i j hij
    rwa [hsmul, hsmul] at this
  · rw [← hgunion]
    exact iUnion_congr fun i => (hsmul i).symm

end Frontier

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

/-
Existence of a rotation of `ℝ³` whose iterates move a given countable subset of the sphere
off itself.  This is the ingredient which lets one absorb the countable set of poles.
-/
import RequestProject.BT.Rotations

open scoped Pointwise

namespace BT

/-- For fixed `A B : ℝ`, the set of angles `u` with `cos u = A` and `sin u = B` is countable. -/
theorem countable_cos_sin_eq (A B : ℝ) :
    {u : ℝ | Real.cos u = A ∧ Real.sin u = B}.Countable := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | Real.cos u = A ∧ Real.sin u = B} with h | ⟨u₀, hu₀⟩
  · rw [h]; exact Set.countable_empty
  · obtain ⟨hu1, hu2⟩ := hu₀
    have hAB : A ^ 2 + B ^ 2 = 1 := by
      subst hu1; subst hu2
      exact Real.cos_sq_add_sin_sq u₀
    refine Set.Countable.mono ?_ (Set.countable_range fun k : ℤ => u₀ + k * (2 * Real.pi))
    rintro u ⟨hc, hs⟩
    have hcos : Real.cos (u - u₀) = 1 := by
      rw [Real.cos_sub, hc, hs, hu1, hu2]
      nlinarith [hAB]
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (u - u₀)).1 hcos
    exact ⟨k, by simp only []; linarith [hk]⟩

/-- Preimages of a countable set under multiplication by a nonzero constant are countable. -/
theorem countable_preimage_mul {n : ℕ} (hn : 0 < n) {S : Set ℝ} (hS : S.Countable) :
    {t : ℝ | (n : ℝ) * t ∈ S}.Countable := by
  have hinj : Function.Injective fun t : ℝ => (n : ℝ) * t := by
    intro a b hab
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    exact mul_left_cancel₀ hn' hab
  exact hS.preimage hinj

/-- A rotation about the `z`-axis whose iterates move a countable set avoiding the `z`-axis
off itself. -/
theorem exists_absorbing_rotZ (D : Set E) (hD : D.Countable)
    (haxis : ∀ x ∈ D, ¬ (x 0 = 0 ∧ x 1 = 0)) :
    ∃ g : E ≃ₗᵢ[ℝ] E, ∀ n : ℕ, 0 < n → Disjoint ((g ^ n) • D) D := by
  classical
  -- the set of "bad" angles
  set Bad : Set ℝ := ⋃ n ∈ {n : ℕ | 0 < n}, ⋃ x ∈ D, ⋃ y ∈ D,
    {t : ℝ | Real.cos ((n : ℝ) * t) * x 0 - Real.sin ((n : ℝ) * t) * x 1 = y 0 ∧
      Real.sin ((n : ℝ) * t) * x 0 + Real.cos ((n : ℝ) * t) * x 1 = y 1} with hBad
  have hBadCountable : Bad.Countable := by
    refine Set.Countable.biUnion (Set.to_countable _) fun n hn => ?_
    refine Set.Countable.biUnion hD fun x hx => ?_
    refine Set.Countable.biUnion hD fun y hy => ?_
    have hx2 : x 0 ^ 2 + x 1 ^ 2 ≠ 0 := by
      intro h
      obtain ⟨h0, h1⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).1 h
      exact haxis x hx ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0,
        pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h1⟩
    set c₀ : ℝ := (x 0 * y 0 + x 1 * y 1) / (x 0 ^ 2 + x 1 ^ 2) with hc₀
    set s₀ : ℝ := (x 0 * y 1 - x 1 * y 0) / (x 0 ^ 2 + x 1 ^ 2) with hs₀
    have hsub : {t : ℝ | Real.cos ((n : ℝ) * t) * x 0 - Real.sin ((n : ℝ) * t) * x 1 = y 0 ∧
        Real.sin ((n : ℝ) * t) * x 0 + Real.cos ((n : ℝ) * t) * x 1 = y 1} ⊆
        {t : ℝ | (n : ℝ) * t ∈ {u : ℝ | Real.cos u = c₀ ∧ Real.sin u = s₀}} := by
      rintro t ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rw [hc₀, eq_div_iff hx2]
        linear_combination (x 0) * h1 + (x 1) * h2
      · rw [hs₀, eq_div_iff hx2]
        linear_combination (-(x 1)) * h1 + (x 0) * h2
    exact Set.Countable.mono hsub (countable_preimage_mul hn (countable_cos_sin_eq c₀ s₀))
  -- pick a good angle
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    exact Cardinal.not_countable_real (hBadCountable.mono fun x _ => hcon x)
  refine ⟨rotZ (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t), fun n hn => ?_⟩
  refine Set.disjoint_left.2 ?_
  rintro z ⟨x, hx, rfl⟩ hz
  refine ht ?_
  rw [hBad]
  refine Set.mem_biUnion (show n ∈ {n : ℕ | 0 < n} from hn) ?_
  refine Set.mem_biUnion hx ?_
  refine Set.mem_biUnion hz ?_
  have hpow : (rotZ (Real.cos t) (Real.sin t) (Real.cos_sq_add_sin_sq t)) ^ n
      = rotZ (Real.cos ((n : ℝ) * t)) (Real.sin ((n : ℝ) * t)) (Real.cos_sq_add_sin_sq _) :=
    rotZ_pow t n _ _
  constructor
  · have := congrArg (fun v : E => v 0) (congrArg (fun (h : E ≃ₗᵢ[ℝ] E) => h x) hpow)
    simpa using this.symm
  · have := congrArg (fun v : E => v 1) (congrArg (fun (h : E ≃ₗᵢ[ℝ] E) => h x) hpow)
    simpa using this.symm

theorem countable_smul_set (g : E ≃ₗᵢ[ℝ] E) {D : Set E} (hD : D.Countable) :
    (g • D).Countable := hD.image _

/-- A rotation whose iterates move a countable subset of the unit sphere off itself. -/
theorem exists_absorbing_rotation (D : Set E) (hD : D.Countable)
    (hDS : D ⊆ Metric.sphere (0 : E) 1) :
    ∃ g : E ≃ₗᵢ[ℝ] E, ∀ n : ℕ, 0 < n → Disjoint ((g ^ n) • D) D := by
  classical
  -- choose an axis avoiding `D`
  have hbad : {b : ℝ | (!₂[0, -Real.sin b, Real.cos b] : E) ∈ D ∨
      (!₂[0, Real.sin b, -Real.cos b] : E) ∈ D}.Countable := by
    have hsub : {b : ℝ | (!₂[0, -Real.sin b, Real.cos b] : E) ∈ D ∨
        (!₂[0, Real.sin b, -Real.cos b] : E) ∈ D} ⊆
        (⋃ d ∈ D, {b : ℝ | Real.cos b = d 2 ∧ Real.sin b = -(d 1)}) ∪
        (⋃ d ∈ D, {b : ℝ | Real.cos b = -(d 2) ∧ Real.sin b = d 1}) := by
      rintro b (hb | hb)
      · refine Or.inl (Set.mem_biUnion hb ⟨?_, ?_⟩) <;> simp
      · refine Or.inr (Set.mem_biUnion hb ⟨?_, ?_⟩) <;> simp
    refine Set.Countable.mono hsub (Set.Countable.union ?_ ?_) <;>
      exact Set.Countable.biUnion hD fun d _ => countable_cos_sin_eq _ _
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b ∉ {b : ℝ | (!₂[0, -Real.sin b, Real.cos b] : E) ∈ D ∨
      (!₂[0, Real.sin b, -Real.cos b] : E) ∈ D} := by
    by_contra hcon
    push_neg at hcon
    exact Cardinal.not_countable_real (hbad.mono fun x _ => hcon x)
  simp only [Set.mem_setOf_eq, not_or] at hb
  set rho : E ≃ₗᵢ[ℝ] E := rotX (Real.cos b) (Real.sin b) (Real.cos_sq_add_sin_sq b) with hrho
  set D' : Set E := rho⁻¹ • D with hD'
  have hD'c : D'.Countable := hD.image _
  have hmem : ∀ x ∈ D', rho x ∈ D := by
    rintro x ⟨y, hy, rfl⟩
    simpa using hy
  have hD'S : ∀ x ∈ D', ‖x‖ = 1 := by
    rintro x ⟨y, hy, rfl⟩
    have := hDS hy
    rw [mem_sphere_iff_norm, sub_zero] at this
    simpa using this
  have haxis : ∀ x ∈ D', ¬ (x 0 = 0 ∧ x 1 = 0) := by
    rintro x hx ⟨hx0, hx1⟩
    have hnorm : ‖x‖ = 1 := hD'S x hx
    have hx2 : x 2 = 1 ∨ x 2 = -1 := by
      have : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
        have h := congrArg (fun r => r ^ 2) hnorm
        simp only [one_pow] at h
        rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)] at h
        simpa [Fin.sum_univ_three, sq_abs] using h
      rw [hx0, hx1] at this
      have hsq : x 2 * x 2 = 1 := by nlinarith [this]
      exact mul_self_eq_one_iff.1 hsq
    have hxe : x = !₂[0, 0, x 2] := by
      ext i
      fin_cases i <;> simp [hx0, hx1]
    rcases hx2 with h2 | h2
    · refine hb.1 ?_
      have : rho x = !₂[0, -Real.sin b, Real.cos b] := by
        rw [hxe, h2]
        ext i
        fin_cases i <;> simp [hrho]
      rw [← this]
      exact hmem x hx
    · refine hb.2 ?_
      have : rho x = !₂[0, Real.sin b, -Real.cos b] := by
        rw [hxe, h2]
        ext i
        fin_cases i <;> simp [hrho]
      rw [← this]
      exact hmem x hx
  obtain ⟨h, hh⟩ := exists_absorbing_rotZ D' hD'c haxis
  have hconj : ∀ n : ℕ, (rho * h * rho⁻¹) ^ n = rho * h ^ n * rho⁻¹ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, pow_succ]; group
  have hDD' : rho • D' = D := by
    rw [hD']
    ext y
    constructor
    · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
      simpa using hv
    · intro hy
      exact ⟨rho⁻¹ • y, ⟨y, hy, rfl⟩, by simp⟩
  refine ⟨rho * h * rho⁻¹, fun n hn => ?_⟩
  rw [hconj n]
  refine Set.disjoint_left.2 ?_
  intro z hz hz'
  rw [mul_smul, mul_smul, ← hD'] at hz
  rw [← hDD'] at hz'
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨v, hv, hvz⟩ := hz'
  have : u = v := rho.injective hvz.symm
  subst this
  exact Set.disjoint_left.1 (hh n hn) hu hv

end BT

/-
Explicit rotations of `ℝ³` about the coordinate axes, as linear isometry equivalences.
-/
import Mathlib

open scoped Pointwise

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of linear isometries of `ℝ³` acts on `ℝ³`. -/
instance : SMul (E ≃ₗᵢ[ℝ] E) E := ⟨fun f x => f x⟩

@[simp] theorem linIso_smul_def (f : E ≃ₗᵢ[ℝ] E) (x : E) : f • x = f x := rfl

instance : MulAction (E ≃ₗᵢ[ℝ] E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The group of isometries of `ℝ³` acts on `ℝ³`. -/
instance : SMul (E ≃ᵢ E) E := ⟨fun f x => f x⟩

@[simp] theorem iso_smul_def (f : E ≃ᵢ E) (x : E) : f • x = f x := rfl

instance : MulAction (E ≃ᵢ E) E where
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- Every linear isometry of `ℝ³` is an isometry of `ℝ³`; as a group homomorphism. -/
def toIso : (E ≃ₗᵢ[ℝ] E) →* (E ≃ᵢ E) where
  toFun f := f.toIsometryEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem toIso_smul (f : E ≃ₗᵢ[ℝ] E) (x : E) : toIso f • x = f • x := rfl

theorem norm_eq_of_sq {x y : E} (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) :
    ‖x‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, sq_abs, Real.norm_eq_abs]
  simpa using h

/-- The linear map given by the rotation matrix about the `z`-axis with cosine `c`, sine `s`. -/
def rotZlin (c s : ℝ) : E →ₗ[ℝ] E where
  toFun x := !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

/-- The linear map given by the rotation matrix about the `x`-axis with cosine `c`, sine `s`. -/
def rotXlin (c s : ℝ) : E →ₗ[ℝ] E where
  toFun x := !₂[x 0, c * x 1 - s * x 2, s * x 1 + c * x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

@[simp] theorem rotZlin_apply (c s : ℝ) (x : E) :
    rotZlin c s x = !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2] := rfl

@[simp] theorem rotXlin_apply (c s : ℝ) (x : E) :
    rotXlin c s x = !₂[x 0, c * x 1 - s * x 2, s * x 1 + c * x 2] := rfl

/-- Rotation of `ℝ³` about the `z`-axis, with cosine `c` and sine `s`. -/
def rotZ (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := LinearEquiv.ofLinear (rotZlin c s) (rotZlin c (-s))
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 0) * h
      · linear_combination (x 1) * h)
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 0) * h
      · linear_combination (x 1) * h)
  norm_map' x := by
    show ‖rotZlin c s x‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, sq_abs, rotZlin]
    nlinarith [h]

/-- Rotation of `ℝ³` about the `x`-axis, with cosine `c` and sine `s`. -/
def rotX (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := LinearEquiv.ofLinear (rotXlin c s) (rotXlin c (-s))
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 1) * h
      · linear_combination (x 2) * h)
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 1) * h
      · linear_combination (x 2) * h)
  norm_map' x := by
    show ‖rotXlin c s x‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, sq_abs, rotXlin]
    nlinarith [h]

@[simp] theorem rotZ_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (x : E) :
    rotZ c s h x = !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2] := rfl

@[simp] theorem rotX_apply (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (x : E) :
    rotX c s h x = !₂[x 0, c * x 1 - s * x 2, s * x 1 + c * x 2] := rfl

theorem rotZ_one (h : (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1) : rotZ 1 0 h = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp

theorem rotX_one (h : (1 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1) : rotX 1 0 h = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp

theorem rotZ_mul (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1)
    (h'' : (c * c' - s * s') ^ 2 + (s * c' + c * s') ^ 2 = 1) :
    rotZ c s h * rotZ c' s' h' = rotZ (c * c' - s * s') (s * c' + c * s') h'' := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp <;> ring

theorem rotX_mul (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1)
    (h'' : (c * c' - s * s') ^ 2 + (s * c' + c * s') ^ 2 = 1) :
    rotX c s h * rotX c' s' h' = rotX (c * c' - s * s') (s * c' + c * s') h'' := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp <;> ring

theorem rotZ_symm (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c ^ 2 + (-s) ^ 2 = 1) :
    (rotZ c s h)⁻¹ = rotZ c (-s) h' := by
  have key : rotZ c (-s) h' * rotZ c s h = 1 := by
    have e1 : c * c - -s * s = 1 := by nlinarith [h]
    have e2 : -s * c + c * s = 0 := by ring
    have h'' : (c * c - -s * s) ^ 2 + (-s * c + c * s) ^ 2 = 1 := by rw [e1, e2]; norm_num
    rw [rotZ_mul c (-s) c s h' h h'']
    simp only [e1, e2]
    exact rotZ_one _
  exact inv_eq_of_mul_eq_one_left key

theorem rotX_symm (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c ^ 2 + (-s) ^ 2 = 1) :
    (rotX c s h)⁻¹ = rotX c (-s) h' := by
  have key : rotX c (-s) h' * rotX c s h = 1 := by
    have e1 : c * c - -s * s = 1 := by nlinarith [h]
    have e2 : -s * c + c * s = 0 := by ring
    have h'' : (c * c - -s * s) ^ 2 + (-s * c + c * s) ^ 2 = 1 := by rw [e1, e2]; norm_num
    rw [rotX_mul c (-s) c s h' h h'']
    simp only [e1, e2]
    exact rotX_one _
  exact inv_eq_of_mul_eq_one_left key

/-- The powers of a rotation about the `z`-axis. -/
theorem rotZ_pow (t : ℝ) (n : ℕ) (h : Real.cos t ^ 2 + Real.sin t ^ 2 = 1)
    (hn : Real.cos (n * t) ^ 2 + Real.sin (n * t) ^ 2 = 1) :
    (rotZ (Real.cos t) (Real.sin t) h) ^ n = rotZ (Real.cos (n * t)) (Real.sin (n * t)) hn := by
  induction n with
  | zero =>
    apply LinearIsometryEquiv.ext
    intro x
    ext i
    fin_cases i <;> simp
  | succ n ih =>
    have hn' : Real.cos (n * t) ^ 2 + Real.sin (n * t) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    rw [pow_succ, ih hn']
    apply LinearIsometryEquiv.ext
    intro x
    have key : ((n : ℝ) + 1) * t = (n : ℝ) * t + t := by ring
    ext i
    fin_cases i <;> simp [key, Real.cos_add, Real.sin_add] <;> ring

end BT

/-
Two rotations of `ℝ³` by the angle `arccos (1/3)` about the `z`- and `x`-axes generate a
free group of rank two.
-/
import RequestProject.BT.Rotations

namespace BT

open Real

theorem cos_sin_one_third : (1 / 3 : ℝ) ^ 2 + (2 * Real.sqrt 2 / 3) ^ 2 = 1 := by
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [h]

/-- Rotation about the `z`-axis by the angle `arccos (1/3)`. -/
noncomputable def rotA : E ≃ₗᵢ[ℝ] E := rotZ (1 / 3) (2 * Real.sqrt 2 / 3) cos_sin_one_third

/-- Rotation about the `x`-axis by the angle `arccos (1/3)`. -/
noncomputable def rotB : E ≃ₗᵢ[ℝ] E := rotX (1 / 3) (2 * Real.sqrt 2 / 3) cos_sin_one_third

/-- The homomorphism from the free group of rank two sending the two generators to `rotA`
and `rotB`. -/
noncomputable def phi : FreeGroup (Fin 2) →* (E ≃ₗᵢ[ℝ] E) := FreeGroup.lift ![rotA, rotB]

@[simp] theorem phi_of_zero : phi (FreeGroup.of 0) = rotA := by simp [phi]

@[simp] theorem phi_of_one : phi (FreeGroup.of 1) = rotB := by simp [phi]

/-! ### The integer recursion

Applying the generators to the vector `v₀ = (0,1,0)` produces vectors of the form
`(A √2, B, C √2)/3^k` with `A B C : ℤ`, and for a reduced word `B` is never divisible by `3`. -/

/-- `√2`. -/
noncomputable def sq2 : ℝ := Real.sqrt 2

theorem sq2_sq : sq2 * sq2 = 2 := by
  rw [sq2]
  exact Real.mul_self_sqrt (by norm_num)

/-- The sign attached to a letter: `+1` for a generator, `-1` for its inverse. -/
def sgnZ (b : Bool) : ℤ := if b then 1 else -1

/-- The real sign attached to a letter. -/
noncomputable def sgnR (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgnZ_cast (b : Bool) : ((sgnZ b : ℤ) : ℝ) = sgnR b := by
  cases b <;> simp [sgnZ, sgnR]

theorem sgnZ_mul_self (b : Bool) : sgnZ b * sgnZ b = 1 := by cases b <;> simp [sgnZ]

/-- One step of the integer recursion, corresponding to applying one generator. -/
def stp (l : Fin 2 × Bool) (v : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if l.1 = 0 then (v.1 - 2 * sgnZ l.2 * v.2.1, v.2.1 + 4 * sgnZ l.2 * v.1, 3 * v.2.2)
  else (3 * v.1, v.2.1 - 4 * sgnZ l.2 * v.2.2, v.2.2 + 2 * sgnZ l.2 * v.2.1)

/-- The integer triple attached to a word. -/
def evalW (L : List (Fin 2 × Bool)) : ℤ × ℤ × ℤ := L.foldr stp (0, 1, 0)

@[simp] theorem evalW_nil : evalW [] = (0, 1, 0) := rfl

@[simp] theorem evalW_cons (x : Fin 2 × Bool) (L : List (Fin 2 × Bool)) :
    evalW (x :: L) = stp x (evalW L) := rfl

/-- If the first letter of `L` is of type `b`, then the first coordinate is divisible by 3. -/
theorem three_dvd_fst {y : Fin 2 × Bool} {t : List (Fin 2 × Bool)} (hy : y.1 = 1) :
    (3 : ℤ) ∣ (evalW (y :: t)).1 := by
  rw [evalW_cons, stp, if_neg (by rw [hy]; decide)]
  exact ⟨_, rfl⟩

/-- If the first letter of `L` is of type `a`, then the third coordinate is divisible by 3. -/
theorem three_dvd_thd {y : Fin 2 × Bool} {t : List (Fin 2 × Bool)} (hy : y.1 = 0) :
    (3 : ℤ) ∣ (evalW (y :: t)).2.2 := by
  rw [evalW_cons, stp, if_pos hy]
  exact ⟨_, rfl⟩

theorem fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by omega

/-- **The key arithmetic lemma**: for a nonempty reduced word the middle coordinate is never
divisible by three. -/
theorem not_three_dvd_snd : ∀ (L : List (Fin 2 × Bool)), FreeGroup.IsReduced L → L ≠ [] →
    ¬ ((3 : ℤ) ∣ (evalW L).2.1) := by
  intro L
  induction L with
  | nil => intro _ h; exact absurd rfl h
  | cons x L' ih =>
    intro hred _
    cases L' with
    | nil =>
      rcases fin2_eq_zero_or_one x.1 with hx | hx
      · simp only [evalW_cons, evalW_nil, stp, if_pos hx]
        cases hb : x.2 <;> simp [sgnZ]
      · simp only [evalW_cons, evalW_nil, stp, if_neg (by rw [hx]; decide : ¬ x.1 = 0)]
        cases hb : x.2 <;> simp [sgnZ]
    | cons y t =>
      have hred2 := FreeGroup.isReduced_cons_cons.1 hred
      have hsame : x.1 = y.1 → x.2 = y.2 := hred2.1
      have hB' : ¬ ((3:ℤ) ∣ (evalW (y :: t)).2.1) := ih hred2.2 (by simp)
      have hx1 : ¬ x.1 = 0 ↔ x.1 = 1 := by
        constructor
        · intro h; rcases fin2_eq_zero_or_one x.1 with h' | h'
          · exact absurd h' h
          · exact h'
        · intro h; rw [h]; decide
      have hy1 : ¬ y.1 = 0 ↔ y.1 = 1 := by
        constructor
        · intro h; rcases fin2_eq_zero_or_one y.1 with h' | h'
          · exact absurd h' h
          · exact h'
        · intro h; rw [h]; decide
      rcases fin2_eq_zero_or_one x.1 with hx | hx <;>
        rcases fin2_eq_zero_or_one y.1 with hy | hy
      · have hb : x.2 = y.2 := hsame (hx.trans hy.symm)
        simp only [evalW_cons, stp, if_pos hx, if_pos hy, hb] at hB' ⊢
        cases hy2 : y.2 <;> norm_num [sgnZ, hy2] at hB' ⊢ <;> omega
      · simp only [evalW_cons, stp, if_pos hx, if_neg (hy1.2 hy)] at hB' ⊢
        cases hx2 : x.2 <;> cases hy2 : y.2 <;>
          norm_num [sgnZ, hx2, hy2] at hB' ⊢ <;> omega
      · simp only [evalW_cons, stp, if_neg (hx1.2 hx), if_pos hy] at hB' ⊢
        cases hx2 : x.2 <;> cases hy2 : y.2 <;>
          norm_num [sgnZ, hx2, hy2] at hB' ⊢ <;> omega
      · have hb : x.2 = y.2 := hsame (hx.trans hy.symm)
        simp only [evalW_cons, stp, if_neg (hx1.2 hx), if_neg (hy1.2 hy), hb] at hB' ⊢
        cases hy2 : y.2 <;> norm_num [sgnZ, hy2] at hB' ⊢ <;> omega

/-! ### The analytic side -/

/-- The image of a letter under the representation. -/
noncomputable def genR (x : Fin 2 × Bool) : E ≃ₗᵢ[ℝ] E :=
  cond x.2 (![rotA, rotB] x.1) (![rotA, rotB] x.1)⁻¹

theorem phi_mk (L : List (Fin 2 × Bool)) : phi (FreeGroup.mk L) = (L.map genR).prod :=
  FreeGroup.lift_mk

theorem genR_zero_apply (b : Bool) (v : E) :
    genR (0, b) v = !₂[(1/3) * v 0 - (sgnR b * (2 * sq2 / 3)) * v 1,
                       (sgnR b * (2 * sq2 / 3)) * v 0 + (1/3) * v 1, v 2] := by
  have h' : (1/3 : ℝ) ^ 2 + (-(2 * Real.sqrt 2 / 3)) ^ 2 = 1 := by
    rw [neg_pow]; simpa using cos_sin_one_third
  cases b
  · have hg : genR ((0 : Fin 2), false) = (rotA)⁻¹ := rfl
    rw [hg, rotA, rotZ_symm _ _ _ h', rotZ_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]
  · have hg : genR ((0 : Fin 2), true) = rotA := rfl
    rw [hg, rotA, rotZ_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]

theorem genR_one_apply (b : Bool) (v : E) :
    genR (1, b) v = !₂[v 0, (1/3) * v 1 - (sgnR b * (2 * sq2 / 3)) * v 2,
                       (sgnR b * (2 * sq2 / 3)) * v 1 + (1/3) * v 2] := by
  have h' : (1/3 : ℝ) ^ 2 + (-(2 * Real.sqrt 2 / 3)) ^ 2 = 1 := by
    rw [neg_pow]; simpa using cos_sin_one_third
  cases b
  · have hg : genR ((1 : Fin 2), false) = (rotB)⁻¹ := rfl
    rw [hg, rotB, rotX_symm _ _ _ h', rotX_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]
  · have hg : genR ((1 : Fin 2), true) = rotB := rfl
    rw [hg, rotB, rotX_apply]
    ext i; fin_cases i <;> simp [sgnR, sq2]

theorem genR_zero_smul (b : Bool) (A B C : ℤ) :
    (3:ℝ) • genR (0, b) (!₂[(A:ℝ) * sq2, (B:ℝ), (C:ℝ) * sq2])
      = !₂[((stp (0, b) (A, B, C)).1 : ℝ) * sq2, ((stp (0, b) (A, B, C)).2.1 : ℝ),
           ((stp (0, b) (A, B, C)).2.2 : ℝ) * sq2] := by
  rw [genR_zero_apply]
  have hs2 : sq2 ^ 2 = 2 := by rw [pow_two]; exact sq2_sq
  ext i
  fin_cases i <;> cases b <;>
    simp [stp, sgnZ, sgnR] <;> ring_nf
  all_goals rw [hs2]; ring

theorem genR_one_smul (b : Bool) (A B C : ℤ) :
    (3:ℝ) • genR (1, b) (!₂[(A:ℝ) * sq2, (B:ℝ), (C:ℝ) * sq2])
      = !₂[((stp (1, b) (A, B, C)).1 : ℝ) * sq2, ((stp (1, b) (A, B, C)).2.1 : ℝ),
           ((stp (1, b) (A, B, C)).2.2 : ℝ) * sq2] := by
  rw [genR_one_apply]
  have hs2 : sq2 ^ 2 = 2 := by rw [pow_two]; exact sq2_sq
  ext i
  fin_cases i <;> cases b <;>
    simp [stp, sgnZ, sgnR] <;> ring_nf
  all_goals rw [hs2]; ring

/-- The starting vector `(0,1,0)` of the recursion. -/
noncomputable def v0 : E := !₂[0, 1, 0]

/-- The image of `v₀` under the rotation attached to a word, in terms of the integer
recursion. -/
theorem phi_eval (L : List (Fin 2 × Bool)) :
    (3:ℝ) ^ L.length • (phi (FreeGroup.mk L) v0) =
      !₂[((evalW L).1 : ℝ) * sq2, ((evalW L).2.1 : ℝ), ((evalW L).2.2 : ℝ) * sq2] := by
  induction L with
  | nil =>
    have h1 : phi (FreeGroup.mk ([] : List (Fin 2 × Bool))) = 1 := by rw [phi_mk]; simp
    simp only [List.length_nil, pow_zero, one_smul, evalW_nil, h1]
    ext i
    fin_cases i <;> simp [v0]
  | cons x L' ih =>
    have hstep : phi (FreeGroup.mk (x :: L')) v0 = genR x (phi (FreeGroup.mk L') v0) := by
      rw [phi_mk, phi_mk, List.map_cons, List.prod_cons]; rfl
    rw [hstep, List.length_cons, pow_succ]
    have hlin : ((3:ℝ) ^ L'.length * 3) • genR x (phi (FreeGroup.mk L') v0)
        = (3:ℝ) • genR x ((3:ℝ) ^ L'.length • (phi (FreeGroup.mk L') v0)) := by
      rw [map_smul, smul_smul]
      congr 1
      ring
    rw [hlin, ih]
    obtain ⟨i, b⟩ := x
    rcases fin2_eq_zero_or_one i with hi | hi <;> subst hi
    · exact genR_zero_smul b _ _ _
    · exact genR_one_smul b _ _ _

/-- The two rotations `rotA` and `rotB` generate a free group of rank two. -/
theorem phi_injective : Function.Injective phi := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  have hL : FreeGroup.mk w.toWord = w := FreeGroup.mk_toWord
  have hLne : w.toWord ≠ [] := fun h => hne (FreeGroup.toWord_eq_nil_iff.1 h)
  have heval := phi_eval w.toWord
  rw [hL, hw] at heval
  have h1 := congrArg (fun v : E => v 1) heval
  simp only [v0] at h1
  have hB : ((evalW w.toWord).2.1 : ℝ) = 3 ^ w.toWord.length := by
    simpa using h1.symm
  have hBZ : (evalW w.toWord).2.1 = 3 ^ w.toWord.length := by
    exact_mod_cast hB
  refine not_three_dvd_snd w.toWord FreeGroup.isReduced_toWord hLne ?_
  rw [hBZ]
  exact dvd_pow_self 3 (by simpa [List.length_eq_zero_iff] using hLne)

end BT

/-
General theory of equidecomposability, used in the proof of the Banach-Tarski theorem.
-/
import Mathlib

open Set Function
open scoped Pointwise

namespace BT

variable {X : Type*} {G H : Type*} [Group G] [MulAction G X] [Group H] [MulAction H X]
variable {A B C A₁ A₂ B₁ B₂ : Set X}

/-- `A` and `B` are equidecomposable with respect to the action of `G` on `X`: there is a
bijection from `A` to `B` which is piecewise given by finitely many elements of `G`. -/
def Equidec (G : Type*) [Group G] [MulAction G X] (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Finset G), Set.BijOn f A B ∧ Equidecomp.IsDecompOn f A S

namespace Equidec

theorem refl (A : Set X) : Equidec G A A :=
  ⟨id, {1}, Set.bijOn_id A, fun a _ => ⟨1, by simp⟩⟩

theorem symm [Nonempty X] (h : Equidec G A B) : Equidec G B A := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨invFunOn f A, S⁻¹, hbij.symm hbij.invOn_invFunOn.symm, ?_⟩
  have := hdec.of_leftInvOn hbij.injOn.leftInvOn_invFunOn
  rwa [hbij.image_eq] at this

theorem trans (h₁ : Equidec G A B) (h₂ : Equidec G B C) : Equidec G A C := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h₁
  obtain ⟨f', S', hbij', hdec'⟩ := h₂
  exact ⟨f' ∘ f, S' * S, hbij'.comp hbij, hdec'.comp hdec hbij.mapsTo⟩

theorem smul_set (g : G) (A : Set X) : Equidec G A (g • A) := by
  refine ⟨fun x => g • x, {g}, ⟨fun x hx => ⟨x, hx, rfl⟩, fun x _ y _ h => by
    simpa using congrArg (fun z => g⁻¹ • z) h, fun x hx => ?_⟩, fun a _ => ⟨g, by simp⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

/-- Transport an equidecomposition along a group homomorphism compatible with the actions. -/
theorem map (φ : G →* H) (hφ : ∀ (g : G) (x : X), φ g • x = g • x) (h : Equidec G A B) :
    Equidec H A B := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨f, S.image φ, hbij, fun a ha => ?_⟩
  obtain ⟨g, hg, hfa⟩ := hdec a ha
  exact ⟨φ g, Finset.mem_image_of_mem _ hg, by rw [hfa, hφ]⟩

/-- Restricting an equidecomposition to a subset. -/
theorem image (h : Equidec G A B) (hA : A₁ ⊆ A) :
    ∃ B₁ ⊆ B, Equidec G A₁ B₁ ∧ Equidec G (A \ A₁) (B \ B₁) := by
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨f '' A₁, hbij.image_eq ▸ Set.image_mono hA, ⟨f, S, (hbij.injOn.mono hA).bijOn_image,
    hdec.mono hA fun _ _ => rfl⟩, ⟨f, S, ?_, hdec.mono Set.diff_subset fun _ _ => rfl⟩⟩
  have : f '' (A \ A₁) = B \ f '' A₁ := by
    rw [← hbij.image_eq, Set.image_diff_of_injOn hbij.injOn hA]
  rw [← this]
  exact (hbij.injOn.mono Set.diff_subset).bijOn_image

theorem union (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂)
    (h₁ : Equidec G A₁ B₁) (h₂ : Equidec G A₂ B₂) : Equidec G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h₁
  obtain ⟨f', S', hbij', hdec'⟩ := h₂
  have hval : ∀ z ∈ A₁ ∪ A₂, (z ∈ A₁ ∧ Set.piecewise A₁ f f' z = f z) ∨
      (z ∈ A₂ ∧ z ∉ A₁ ∧ Set.piecewise A₁ f f' z = f' z) := by
    rintro z (hz | hz)
    · exact Or.inl ⟨hz, by simp [Set.piecewise, hz]⟩
    · have hz' : z ∉ A₁ := fun h => (hA.le_bot ⟨h, hz⟩).elim
      exact Or.inr ⟨hz, hz', by simp [Set.piecewise, hz']⟩
  refine ⟨Set.piecewise A₁ f f', S ∪ S', ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    rcases hval x hx with ⟨hx1, hxe⟩ | ⟨hx2, _, hxe⟩
    · exact Or.inl (hxe ▸ hbij.mapsTo hx1)
    · exact Or.inr (hxe ▸ hbij'.mapsTo hx2)
  · intro x hx y hy hxy
    rcases hval x hx with ⟨hx1, hxe⟩ | ⟨hx2, _, hxe⟩ <;>
      rcases hval y hy with ⟨hy1, hye⟩ | ⟨hy2, _, hye⟩
    · exact hbij.injOn hx1 hy1 (by rw [← hxe, ← hye]; exact hxy)
    · refine ((Set.disjoint_left.mp hB (hbij.mapsTo hx1) ?_)).elim
      exact (by rw [← hxe, hxy, hye] : f x = f' y) ▸ hbij'.mapsTo hy2
    · refine ((Set.disjoint_left.mp hB (hbij.mapsTo hy1) ?_)).elim
      exact (by rw [← hye, ← hxy, hxe] : f y = f' x) ▸ hbij'.mapsTo hx2
    · exact hbij'.injOn hx2 hy2 (by rw [← hxe, ← hye]; exact hxy)
  · rintro y (hy | hy)
    · obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
      exact ⟨x, Or.inl hx, by simp [Set.piecewise, hx]⟩
    · obtain ⟨x, hx, rfl⟩ := hbij'.surjOn hy
      have hx' : x ∉ A₁ := fun h => (hA.le_bot ⟨h, hx⟩).elim
      exact ⟨x, Or.inr hx, by simp [Set.piecewise, hx']⟩
  · rintro a (ha | ha)
    · obtain ⟨g, hg, hga⟩ := hdec a ha
      exact ⟨g, Finset.mem_union_left _ hg, by simpa [Set.piecewise, ha] using hga⟩
    · have ha' : a ∉ A₁ := fun h => (hA.le_bot ⟨h, ha⟩).elim
      obtain ⟨g, hg, hga⟩ := hdec' a ha
      exact ⟨g, Finset.mem_union_right _ hg, by simpa [Set.piecewise, ha'] using hga⟩

/-- An equidecomposition, presented as an explicit finite partition of `A` into pieces which
are moved by single group elements to give a partition of `B`. -/
theorem exists_partition (h : Equidec G A B) :
    ∃ (n : ℕ) (P : Fin n → Set X) (g : Fin n → G),
      (∀ i j, i ≠ j → Disjoint (P i) (P j)) ∧ (⋃ i, P i) = A ∧
      (∀ i j, i ≠ j → Disjoint (g i • P i) (g j • P j)) ∧ (⋃ i, g i • P i) = B := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h
  -- choose, for each point of `A`, a group element realizing `f` there
  choose! γ hγS hγ using hdec
  set e : Fin S.card ≃ {x // x ∈ S} := S.equivFin.symm with he
  refine ⟨S.card, fun i => {a ∈ A | γ a = (e i : G)}, fun i => (e i : G), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro a ⟨-, ha⟩ ⟨-, ha'⟩
    exact hij (e.injective (Subtype.ext (ha ▸ ha')))
  · ext a
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · rintro ⟨i, ha, -⟩; exact ha
    · intro ha
      exact ⟨e.symm ⟨γ a, hγS a ha⟩, ha, by simp⟩
  · have himg : ∀ i : Fin S.card, ((e i : G)) • {a ∈ A | γ a = (e i : G)}
        = f '' {a ∈ A | γ a = (e i : G)} := by
      intro i
      ext y
      constructor
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
    intro i j hij
    rw [himg i, himg j]
    refine Set.disjoint_left.2 ?_
    rintro y ⟨a, ⟨ha, ha'⟩, rfl⟩ ⟨b, ⟨hb, hb'⟩, hb''⟩
    have : b = a := hbij.injOn hb ha hb''
    subst this
    exact hij (e.injective (Subtype.ext (ha'.symm.trans hb')))
  · have himg : ∀ i : Fin S.card, ((e i : G)) • {a ∈ A | γ a = (e i : G)}
        = f '' {a ∈ A | γ a = (e i : G)} := by
      intro i
      ext y
      constructor
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
      · rintro ⟨a, ⟨ha, ha'⟩, rfl⟩
        exact ⟨a, ⟨ha, ha'⟩, by rw [hγ a ha, ha']⟩
    ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hy⟩
      rw [himg i] at hy
      obtain ⟨a, ⟨ha, -⟩, rfl⟩ := hy
      exact hbij.mapsTo ha
    · intro hy
      obtain ⟨a, ha, rfl⟩ := hbij.surjOn hy
      refine ⟨e.symm ⟨γ a, hγS a ha⟩, ?_⟩
      rw [himg]
      exact ⟨a, ⟨ha, by simp⟩, rfl⟩

end Equidec

/-- A set is paradoxical if it can be split into two disjoint pieces, each of which is
equidecomposable with the whole set. -/
def Paradoxical (G : Type*) [Group G] [MulAction G X] (A : Set X) : Prop :=
  ∃ A₁ A₂ : Set X, A₁ ∪ A₂ = A ∧ Disjoint A₁ A₂ ∧ Equidec G A₁ A ∧ Equidec G A₂ A

namespace Paradoxical

/-- Paradoxicality transfers along equidecompositions. -/
theorem of_equidec [Nonempty X] (hP : Paradoxical G A) (h : Equidec G A B) :
    Paradoxical G B := by
  obtain ⟨A₁, A₂, hunion, hdisj, h₁, h₂⟩ := hP
  obtain ⟨B₁, hB₁sub, hb₁, hb₂⟩ := h.image (hunion ▸ Set.subset_union_left (t := A₂))
  refine ⟨B₁, B \ B₁, by simp [hB₁sub], disjoint_sdiff_right,
    (hb₁.symm.trans h₁).trans h, ?_⟩
  have hAA : A \ A₁ = A₂ := by
    rw [← hunion]
    ext x
    constructor
    · rintro ⟨hx | hx, hx'⟩
      · exact absurd hx hx'
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun h => (hdisj.le_bot ⟨h, hx⟩).elim⟩
  rw [hAA] at hb₂
  exact (hb₂.symm.trans h₂).trans h

/-- If `A` is paradoxical and `B` is a disjoint congruent copy of `A`, then `A` is
equidecomposable with `A ∪ B`: `A` can be doubled. -/
theorem doubling (hP : Paradoxical G A) (hAB : Equidec G A B) (hdisj : Disjoint A B) :
    Equidec G A (A ∪ B) := by
  obtain ⟨A₁, A₂, hunion, hd, h₁, h₂⟩ := hP
  have h := Equidec.union hd hdisj h₁ (h₂.trans hAB)
  rwa [hunion] at h

/-- Transport paradoxicality along a group homomorphism compatible with the actions. -/
theorem map (φ : G →* H) (hφ : ∀ (g : G) (x : X), φ g • x = g • x) (hP : Paradoxical G A) :
    Paradoxical H A := by
  obtain ⟨A₁, A₂, hunion, hd, h₁, h₂⟩ := hP
  exact ⟨A₁, A₂, hunion, hd, h₁.map φ hφ, h₂.map φ hφ⟩

end Paradoxical

/-- Absorbing a "small" set `D` into `A` using an element `g` whose iterates move `D` to
disjoint copies of itself inside `A`. -/
theorem Equidec.absorb (g : G) (D A : Set X) (hDA : ∀ n : ℕ, (g ^ n) • D ⊆ A)
    (hdisj : ∀ n : ℕ, 0 < n → Disjoint ((g ^ n) • D) D) : Equidec G A (A \ D) := by
  classical
  set U : Set X := ⋃ n : ℕ, (g ^ n) • D with hU
  have hUA : U ⊆ A := Set.iUnion_subset hDA
  have hDU : D ⊆ U := fun x hx => Set.mem_iUnion.2 ⟨0, by simpa using hx⟩
  have hgU : g • U = U \ D := by
    rw [hU, Set.smul_set_iUnion]
    ext x
    simp only [Set.mem_iUnion, Set.mem_diff]
    constructor
    · rintro ⟨n, hn⟩
      rw [smul_smul, ← pow_succ'] at hn
      exact ⟨⟨n + 1, hn⟩, fun hxD => (hdisj (n + 1) n.succ_pos).le_bot ⟨hn, hxD⟩⟩
    · rintro ⟨⟨n, hn⟩, hxD⟩
      match n with
      | 0 => exact absurd (by simpa using hn) hxD
      | (m + 1) => exact ⟨m, by rw [smul_smul, ← pow_succ']; exact hn⟩
  have hgUmem : ∀ x ∈ U, g • x ∈ U := by
    intro x hx
    have : g • x ∈ g • U := ⟨x, hx, rfl⟩
    rw [hgU] at this
    exact this.1
  refine ⟨Set.piecewise U (fun x => g • x) id, {g, 1}, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases hxU : x ∈ U
    · have hmem : g • x ∈ U \ D := hgU ▸ ⟨x, hxU, rfl⟩
      simpa [Set.piecewise, hxU] using ⟨hUA hmem.1, hmem.2⟩
    · refine ⟨by simpa [Set.piecewise, hxU] using hx, ?_⟩
      simpa [Set.piecewise, hxU] using fun hxD => hxU (hDU hxD)
  · intro x hx y hy hxy
    by_cases hxU : x ∈ U <;> by_cases hyU : y ∈ U
    · simp only [Set.piecewise, hxU, hyU, if_pos] at hxy
      simpa using congrArg (fun z => g⁻¹ • z) hxy
    · rw [Set.piecewise_eq_of_mem _ _ _ hxU, Set.piecewise_eq_of_notMem _ _ _ hyU, id_eq] at hxy
      exact absurd (hxy ▸ hgUmem x hxU) hyU
    · rw [Set.piecewise_eq_of_notMem _ _ _ hxU, Set.piecewise_eq_of_mem _ _ _ hyU, id_eq] at hxy
      exact absurd (hxy ▸ hgUmem y hyU) hxU
    · simpa [Set.piecewise, hxU, hyU] using hxy
  · rintro y ⟨hyA, hyD⟩
    by_cases hyU : y ∈ U
    · have hmem : y ∈ g • U := by rw [hgU]; exact ⟨hyU, hyD⟩
      obtain ⟨x, hxU, rfl⟩ := hmem
      exact ⟨x, hUA hxU, by simp [Set.piecewise, hxU]⟩
    · exact ⟨y, hyA, by simp [Set.piecewise, hyU]⟩
  · intro a _
    by_cases haU : a ∈ U
    · exact ⟨g, by simp, by simp [Set.piecewise, haU]⟩
    · exact ⟨1, by simp, by simp [Set.piecewise, haU]⟩

end BT

/-
The free group of rank two has a paradoxical decomposition into four pieces.
-/
import Mathlib

open scoped Pointwise

namespace BT

open FreeGroup

section Words

variable {α : Type*} [DecidableEq α]

/-- Reducing `x :: L` for an already reduced word `L`: either the first letter of `L` is
cancelled by `x`, or nothing happens. -/
theorem reduce_cons_of_isReduced {x : α × Bool} {L : List (α × Bool)} (h : IsReduced L) :
    reduce (x :: L) = if L.head? = some (x.1, !x.2) then L.tail else x :: L := by
  rw [FreeGroup.reduce.cons, h.reduce_eq]
  cases L with
  | nil => simp
  | cons hd tl =>
    have hiff : (x.1 = hd.1 ∧ x.2 = !hd.2) ↔ (hd = (x.1, !x.2)) := by
      obtain ⟨x1, x2⟩ := x
      obtain ⟨h1, h2⟩ := hd
      simp only [Prod.mk.injEq]
      cases x2 <;> cases h2 <;> simp [eq_comm]
    show (if x.1 = hd.1 ∧ x.2 = !hd.2 then tl else x :: hd :: tl) = _
    by_cases hx : hd = (x.1, !x.2)
    · rw [if_pos (hiff.2 hx)]
      simp [hx]
    · rw [if_neg (fun hc => hx (hiff.1 hc))]
      simp [hx]

/-- Multiplying a reduced word by a single letter on the left. -/
theorem toWord_letter_mul (x : α × Bool) (w : FreeGroup α) :
    (FreeGroup.mk [x] * w).toWord =
      if w.toWord.head? = some (x.1, !x.2) then w.toWord.tail else x :: w.toWord := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk, FreeGroup.reduce_singleton,
    List.singleton_append]
  exact reduce_cons_of_isReduced FreeGroup.isReduced_toWord

omit [DecidableEq α] in
/-- In a reduced word, the letter following `x` is never the inverse of `x`. -/
theorem head?_tail_ne {x : α × Bool} {t : List (α × Bool)} (h : IsReduced (x :: t)) :
    t.head? ≠ some (x.1, !x.2) := by
  cases t with
  | nil => simp
  | cons hd tl =>
    intro hc
    have hhd : hd = (x.1, !x.2) := by simpa using hc
    have h' := FreeGroup.isReduced_cons_cons.1 h
    have := h'.1 (by rw [hhd])
    rw [hhd] at this
    simp at this

end Words

/-- The set of elements of the free group whose reduced word starts with the letter `x`. -/
def Wstart (x : Fin 2 × Bool) : Set (FreeGroup (Fin 2)) :=
  {w | w.toWord.head? = some x}

/-- The set of nonpositive powers of the first generator, i.e. words of the form `a⁻ⁿ`. -/
def Nneg : Set (FreeGroup (Fin 2)) :=
  {w | ∃ n : ℕ, w.toWord = List.replicate n ((0 : Fin 2), false)}

/-- The set of strictly negative powers of the first generator. -/
def Nneg₁ : Set (FreeGroup (Fin 2)) :=
  {w | ∃ n : ℕ, 0 < n ∧ w.toWord = List.replicate n ((0 : Fin 2), false)}

theorem inv_of_eq_mk (i : Fin 2) : (FreeGroup.of i)⁻¹ = FreeGroup.mk [(i, false)] := by
  rw [FreeGroup.of, FreeGroup.inv_mk]
  rfl

/-- The four pieces of the paradoxical decomposition. -/
def piece : Fin 4 → Set (FreeGroup (Fin 2))
  | 0 => Wstart (0, true) ∪ Nneg
  | 1 => Wstart (0, false) \ Nneg₁
  | 2 => Wstart (1, true)
  | 3 => Wstart (1, false)

theorem head?_cases (w : FreeGroup (Fin 2)) :
    w.toWord = [] ∨ ∃ x : Fin 2 × Bool, w.toWord.head? = some x := by
  cases h : w.toWord with
  | nil => exact Or.inl rfl
  | cons hd tl => exact Or.inr ⟨hd, by simp⟩

theorem Nneg₁_subset_Nneg : Nneg₁ ⊆ Nneg := by
  rintro w ⟨n, _, hn⟩
  exact ⟨n, hn⟩

/-- Every element lies in one of the four pieces. -/
theorem iUnion_piece : (⋃ i, piece i) = Set.univ := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  rcases head?_cases w with h | ⟨x, hx⟩
  · exact ⟨0, Or.inr ⟨0, by simpa using h⟩⟩
  · obtain ⟨i, b⟩ := x
    fin_cases i
    · cases b
      · by_cases hN : w ∈ Nneg₁
        · exact ⟨0, Or.inr (Nneg₁_subset_Nneg hN)⟩
        · exact ⟨1, ⟨hx, hN⟩⟩
      · exact ⟨0, Or.inl hx⟩
    · cases b
      · exact ⟨3, hx⟩
      · exact ⟨2, hx⟩

theorem Nneg_head? {w : FreeGroup (Fin 2)} (hw : w ∈ Nneg) :
    w.toWord = [] ∨ w.toWord.head? = some ((0 : Fin 2), false) := by
  obtain ⟨n, hn⟩ := hw
  cases n with
  | zero => exact Or.inl (by simpa using hn)
  | succ m => exact Or.inr (by rw [hn]; simp [List.replicate_succ])

theorem Nneg_head_eq {w : FreeGroup (Fin 2)} (hw : w ∈ Nneg) {x : Fin 2 × Bool}
    (hx : w.toWord.head? = some x) : x = ((0 : Fin 2), false) := by
  rcases Nneg_head? hw with h | h
  · rw [h] at hx; simp at hx
  · rw [h] at hx; simpa using hx.symm

@[simp] theorem mem_Wstart {w : FreeGroup (Fin 2)} {x : Fin 2 × Bool} :
    w ∈ Wstart x ↔ w.toWord.head? = some x := Iff.rfl

theorem mem_piece_zero {w : FreeGroup (Fin 2)} :
    w ∈ piece 0 ↔ (w.toWord.head? = some ((0 : Fin 2), true) ∨ w ∈ Nneg) := Iff.rfl

theorem mem_piece_one {w : FreeGroup (Fin 2)} :
    w ∈ piece 1 ↔ (w.toWord.head? = some ((0 : Fin 2), false) ∧ w ∉ Nneg₁) := Iff.rfl

theorem mem_piece_two {w : FreeGroup (Fin 2)} :
    w ∈ piece 2 ↔ w.toWord.head? = some ((1 : Fin 2), true) := Iff.rfl

theorem mem_piece_three {w : FreeGroup (Fin 2)} :
    w ∈ piece 3 ↔ w.toWord.head? = some ((1 : Fin 2), false) := Iff.rfl

theorem Wstart_disjoint {x y : Fin 2 × Bool} (hxy : x ≠ y) : Disjoint (Wstart x) (Wstart y) := by
  rw [Set.disjoint_left]
  intro w hx hy
  rw [mem_Wstart] at hx hy
  exact hxy (Option.some_injective _ (hx.symm.trans hy))

theorem disjoint_01 : Disjoint (piece 0) (piece 1) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_piece_zero] at h1
  rw [mem_piece_one] at h2
  rcases h1 with h | h
  · exact absurd (Option.some_injective _ (h.symm.trans h2.1)) (by simp)
  · obtain ⟨n, hn⟩ := h
    refine h2.2 ⟨n, ?_, hn⟩
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [List.replicate_zero] at hn
      rw [hn] at h2
      simp at h2
    · exact hpos

theorem disjoint_02 : Disjoint (piece 0) (piece 2) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_piece_zero] at h1
  rw [mem_piece_two] at h2
  rcases h1 with h | h
  · exact absurd (Option.some_injective _ (h.symm.trans h2)) (by simp)
  · have := Nneg_head_eq h h2
    simp at this

theorem disjoint_03 : Disjoint (piece 0) (piece 3) := by
  rw [Set.disjoint_left]
  intro w h1 h2
  rw [mem_piece_zero] at h1
  rw [mem_piece_three] at h2
  rcases h1 with h | h
  · exact absurd (Option.some_injective _ (h.symm.trans h2)) (by simp)
  · have := Nneg_head_eq h h2
    simp at this

theorem disjoint_12 : Disjoint (piece 1) (piece 2) :=
  Set.disjoint_of_subset_left Set.diff_subset (Wstart_disjoint (by simp))

theorem disjoint_13 : Disjoint (piece 1) (piece 3) :=
  Set.disjoint_of_subset_left Set.diff_subset (Wstart_disjoint (by simp))

theorem disjoint_23 : Disjoint (piece 2) (piece 3) := Wstart_disjoint (by simp)

theorem pairwise_disjoint_piece : ∀ i j : Fin 4, i ≠ j → Disjoint (piece i) (piece j) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all <;>
    first
      | exact disjoint_01 | exact disjoint_02 | exact disjoint_03
      | exact disjoint_12 | exact disjoint_13 | exact disjoint_23
      | exact disjoint_01.symm | exact disjoint_02.symm | exact disjoint_03.symm
      | exact disjoint_12.symm | exact disjoint_13.symm | exact disjoint_23.symm

theorem toWord_inv_of_mul (i : Fin 2) (w : FreeGroup (Fin 2)) :
    ((FreeGroup.of i)⁻¹ * w).toWord =
      if w.toWord.head? = some (i, true) then w.toWord.tail else (i, false) :: w.toWord := by
  rw [inv_of_eq_mk, toWord_letter_mul]
  simp

theorem tail_head?_ne {w : FreeGroup (Fin 2)} {x : Fin 2 × Bool}
    (hx : w.toWord.head? = some x) : w.toWord.tail.head? ≠ some (x.1, !x.2) := by
  have hred : FreeGroup.IsReduced w.toWord := FreeGroup.isReduced_toWord
  cases hw : w.toWord with
  | nil => rw [hw] at hx; simp at hx
  | cons hd tl =>
    rw [hw] at hx hred
    have hhd : hd = x := by simpa using hx
    subst hhd
    simp only [List.tail_cons]
    exact head?_tail_ne hred

theorem mem_smul_iff {g w : FreeGroup (Fin 2)} {A : Set (FreeGroup (Fin 2))} :
    w ∈ g • A ↔ g⁻¹ * w ∈ A := by
  rw [Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]

theorem disjoint_piece_zero_smul : Disjoint (piece 0) (FreeGroup.of (0 : Fin 2) • piece 1) := by
  rw [Set.disjoint_left]
  intro w hw hmem
  rw [mem_smul_iff] at hmem
  rw [mem_piece_one, toWord_inv_of_mul] at hmem
  rcases mem_piece_zero.1 hw with h | h
  · rw [if_pos h] at hmem
    exact tail_head?_ne h (by simpa using hmem.1)
  · obtain ⟨n, hn⟩ := h
    have hne : w.toWord.head? ≠ some ((0 : Fin 2), true) := by
      intro hc
      have := Nneg_head_eq ⟨n, hn⟩ hc
      simp at this
    rw [if_neg hne] at hmem
    refine hmem.2 ⟨n + 1, Nat.succ_pos n, ?_⟩
    rw [toWord_inv_of_mul, if_neg hne, hn, List.replicate_succ]

theorem union_piece_zero_smul :
    piece 0 ∪ (FreeGroup.of (0 : Fin 2) • piece 1) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hw : w ∈ piece 0
  · exact Or.inl hw
  · right
    rw [mem_piece_zero] at hw
    push_neg at hw
    obtain ⟨h1, h2⟩ := hw
    rw [mem_smul_iff, mem_piece_one, toWord_inv_of_mul, if_neg h1]
    refine ⟨by simp, ?_⟩
    rintro ⟨n, hn, hrep⟩
    rw [toWord_inv_of_mul, if_neg h1] at hrep
    cases n with
    | zero => simp at hn
    | succ m =>
      rw [List.replicate_succ] at hrep
      exact h2 ⟨m, by simpa using hrep⟩

theorem disjoint_piece_two_smul : Disjoint (piece 2) (FreeGroup.of (1 : Fin 2) • piece 3) := by
  rw [Set.disjoint_left]
  intro w hw hmem
  rw [mem_smul_iff, mem_piece_three, toWord_inv_of_mul] at hmem
  have h : w.toWord.head? = some ((1 : Fin 2), true) := mem_piece_two.1 hw
  rw [if_pos h] at hmem
  exact tail_head?_ne h (by simpa using hmem)

theorem union_piece_two_smul :
    piece 2 ∪ (FreeGroup.of (1 : Fin 2) • piece 3) = Set.univ := by
  ext w
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hw : w ∈ piece 2
  · exact Or.inl hw
  · right
    rw [mem_piece_two] at hw
    rw [mem_smul_iff, mem_piece_three, toWord_inv_of_mul, if_neg hw]
    simp

/-- **Paradoxical decomposition of the free group of rank two.**  The free group `F` on two
generators `a = of 0` and `b = of 1` can be partitioned into four sets `A 0, A 1, A 2, A 3`
such that `A 0` together with `a • A 1` partitions `F`, and `A 2` together with `b • A 3`
partitions `F`. -/
theorem freeGroup_paradoxical :
    ∃ A : Fin 4 → Set (FreeGroup (Fin 2)),
      (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
      (⋃ i, A i) = Set.univ ∧
      Disjoint (A 0) (FreeGroup.of (0 : Fin 2) • A 1) ∧
      (A 0) ∪ (FreeGroup.of (0 : Fin 2) • A 1) = Set.univ ∧
      Disjoint (A 2) (FreeGroup.of (1 : Fin 2) • A 3) ∧
      (A 2) ∪ (FreeGroup.of (1 : Fin 2) • A 3) = Set.univ :=
  ⟨piece, pairwise_disjoint_piece, iUnion_piece, disjoint_piece_zero_smul,
    union_piece_zero_smul, disjoint_piece_two_smul, union_piece_two_smul⟩

end BT

/-
From the Hausdorff paradox to the Banach-Tarski paradox: the closed unit ball of `ℝ³`
is paradoxical for the action of the group of isometries.
-/
import RequestProject.BT.Sphere

open Set Function Metric
open scoped Pointwise

namespace BT

/-- The radial extension of a subset of the sphere: all points of the punctured closed unit
ball whose normalization lies in `A`. -/
def star (A : Set E) : Set E := {y : E | y ≠ 0 ∧ ‖y‖ ≤ 1 ∧ ‖y‖⁻¹ • y ∈ A}

theorem star_S2 : star S2 = closedBall (0 : E) 1 \ {0} := by
  ext y
  simp only [star, Set.mem_setOf_eq, Set.mem_diff, Metric.mem_closedBall, dist_zero_right,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy0, hy1, -⟩
    exact ⟨hy1, hy0⟩
  · rintro ⟨hy1, hy0⟩
    refine ⟨hy0, hy1, ?_⟩
    rw [mem_S2, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_norm]
    field_simp

theorem star_union (A B : Set E) : star (A ∪ B) = star A ∪ star B := by
  ext y
  simp only [star, Set.mem_setOf_eq, Set.mem_union]
  tauto

theorem star_disjoint {A B : Set E} (h : Disjoint A B) : Disjoint (star A) (star B) := by
  refine Set.disjoint_left.2 ?_
  rintro y ⟨-, -, hy⟩ ⟨-, -, hy'⟩
  exact Set.disjoint_left.1 h hy hy'

/-- Equidecomposability of subsets of the sphere extends radially. -/
theorem star_equidec {A B : Set E} (hA : A ⊆ S2) (hB : B ⊆ S2)
    (h : Equidec (E ≃ₗᵢ[ℝ] E) A B) : Equidec (E ≃ₗᵢ[ℝ] E) (star A) (star B) := by
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨fun y => ‖y‖ • f (‖y‖⁻¹ • y), S, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro y ⟨hy0, hy1, hyA⟩
    have hr : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    have hfx : ‖f (‖y‖⁻¹ • y)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hyA))
    have hnorm : ‖‖y‖ • f (‖y‖⁻¹ • y)‖ = ‖y‖ := by
      rw [norm_smul, hfx, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    show ‖y‖ • f (‖y‖⁻¹ • y) ∈ star B
    refine ⟨?_, ?_, ?_⟩
    · intro hzero
      rw [hzero, norm_zero] at hnorm
      exact hy0 (norm_eq_zero.1 hnorm.symm)
    · rw [hnorm]; exact hy1
    · rw [hnorm, inv_smul_smul₀ (ne_of_gt hr)]
      exact hbij.mapsTo hyA
  · rintro y ⟨hy0, hy1, hyA⟩ z ⟨hz0, hz1, hzA⟩ hyz'
    have hyz : ‖y‖ • f (‖y‖⁻¹ • y) = ‖z‖ • f (‖z‖⁻¹ • z) := hyz'
    have hry : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    have hrz : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
    have hfy : ‖f (‖y‖⁻¹ • y)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hyA))
    have hfz : ‖f (‖z‖⁻¹ • z)‖ = 1 := mem_S2.1 (hB (hbij.mapsTo hzA))
    have hnorm : ‖y‖ = ‖z‖ := by
      have := congrArg norm hyz
      rwa [norm_smul, norm_smul, hfy, hfz, mul_one, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hry, abs_of_pos hrz] at this
    have hyz2 : ‖z‖ • f (‖y‖⁻¹ • y) = ‖z‖ • f (‖z‖⁻¹ • z) := by
      have hswap : ‖z‖ • f (‖y‖⁻¹ • y) = ‖y‖ • f (‖y‖⁻¹ • y) := by rw [hnorm]
      rw [hswap]; exact hyz
    have hf : f (‖y‖⁻¹ • y) = f (‖z‖⁻¹ • z) := smul_right_injective E (ne_of_gt hrz) hyz2
    have hx : ‖y‖⁻¹ • y = ‖z‖⁻¹ • z := hbij.injOn hyA hzA hf
    have hxx := congrArg (fun v => ‖z‖ • v) hx
    simpa [hnorm, smul_smul, mul_inv_cancel₀ (ne_of_gt hrz)] using hxx
  · rintro z ⟨hz0, hz1, hzB⟩
    have hrz : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
    obtain ⟨x, hxA, hfx⟩ := hbij.surjOn hzB
    have hxnorm : ‖x‖ = 1 := mem_S2.1 (hA hxA)
    have hnz : ‖‖z‖ • x‖ = ‖z‖ := by
      rw [norm_smul, hxnorm, mul_one, Real.norm_eq_abs, abs_of_pos hrz]
    refine ⟨‖z‖ • x, ⟨?_, ?_, ?_⟩, ?_⟩
    · intro hzero
      rw [hzero, norm_zero] at hnz
      exact hz0 (norm_eq_zero.1 hnz.symm)
    · rw [hnz]; exact hz1
    · rw [hnz, inv_smul_smul₀ (ne_of_gt hrz)]; exact hxA
    · show ‖‖z‖ • x‖ • f (‖‖z‖ • x‖⁻¹ • (‖z‖ • x)) = z
      rw [hnz, inv_smul_smul₀ (ne_of_gt hrz), hfx, smul_inv_smul₀ (ne_of_gt hrz)]
  · rintro y ⟨hy0, hy1, hyA⟩
    have hry : (0 : ℝ) < ‖y‖ := norm_pos_iff.2 hy0
    obtain ⟨g, hgS, hg⟩ := hdec _ hyA
    refine ⟨g, hgS, ?_⟩
    show ‖y‖ • f (‖y‖⁻¹ • y) = g • y
    rw [hg]
    show ‖y‖ • (g (‖y‖⁻¹ • y)) = g y
    rw [map_smul, smul_smul, mul_inv_cancel₀ (ne_of_gt hry), one_smul]

/-- The punctured closed unit ball is paradoxical for the group of linear isometries. -/
theorem paradoxical_punctured_ball :
    Paradoxical (E ≃ₗᵢ[ℝ] E) (closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨A₁, A₂, hunion, hdisj, h₁, h₂⟩ := paradoxical_S2
  have hA₁ : A₁ ⊆ S2 := hunion ▸ Set.subset_union_left
  have hA₂ : A₂ ⊆ S2 := hunion ▸ Set.subset_union_right
  refine ⟨star A₁, star A₂, ?_, star_disjoint hdisj, ?_, ?_⟩
  · rw [← star_union, hunion, star_S2]
  · rw [← star_S2]; exact star_equidec hA₁ (fun _ h => h) h₁
  · rw [← star_S2]; exact star_equidec hA₂ (fun _ h => h) h₂

section Center

/-- The point about whose vertical axis we rotate in order to absorb the centre of the ball. -/
noncomputable def pHalf : E := !₂[1 / 2, 0, 0]

theorem norm_pHalf : ‖pHalf‖ = 1 / 2 := by
  rw [EuclideanSpace.norm_eq]
  simp [pHalf, Fin.sum_univ_three]

theorem cos_one_sin_one : Real.cos 1 ^ 2 + Real.sin 1 ^ 2 = 1 := Real.cos_sq_add_sin_sq 1

/-- The rotation by one radian about the vertical axis through `pHalf`. -/
noncomputable def gCenter : E ≃ᵢ E :=
  IsometryEquiv.addRight pHalf * toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one) *
    (IsometryEquiv.addRight pHalf)⁻¹

theorem addRight_inv_apply (b x : E) : (IsometryEquiv.addRight b)⁻¹ x = x - b := by
  have h : (IsometryEquiv.addRight b) ((IsometryEquiv.addRight b)⁻¹ x) = x :=
    IsometryEquiv.apply_inv_self _ _
  have h2 : (IsometryEquiv.addRight b) (x - b) = x := by
    show x - b + b = x
    abel
  exact (IsometryEquiv.addRight b).injective (h.trans h2.symm)

theorem gCenter_pow_apply (n : ℕ) : (gCenter ^ n) 0 =
    pHalf - (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf := by
  have hconj : gCenter ^ n = IsometryEquiv.addRight pHalf *
      (toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one)) ^ n *
      (IsometryEquiv.addRight pHalf)⁻¹ := by
    induction n with
    | zero => simp [gCenter]
    | succ n ih =>
      rw [pow_succ, ih, gCenter, pow_succ]
      group
  rw [hconj]
  show (IsometryEquiv.addRight pHalf)
    (((toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one)) ^ n)
      ((IsometryEquiv.addRight pHalf)⁻¹ 0)) = _
  rw [addRight_inv_apply]
  rw [← map_pow toIso, rotZ_pow 1 n cos_one_sin_one (Real.cos_sq_add_sin_sq _)]
  show ((rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) (0 - pHalf))
      + pHalf = _
  rw [zero_sub, map_neg]
  abel

theorem rotZ_pHalf_ne (n : ℕ) (hn : 0 < n) :
    (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf ≠ pHalf := by
  intro h
  have h0 : Real.cos (n * 1) * (1 / 2) - Real.sin (n * 1) * 0 = 1 / 2 := by
    have := congrArg (fun v : E => v 0) h
    simpa [pHalf] using this
  have hcos : Real.cos (n : ℝ) = 1 := by
    rw [mul_one] at h0
    linarith [h0]
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff (n : ℝ)).1 hcos
  have hkne : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact absurd hk.symm (Nat.cast_ne_zero.mpr hn.ne')
  refine irrational_pi ⟨(n : ℚ) / (2 * (k : ℚ)), ?_⟩
  have hkR : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hkne
  push_cast
  field_simp
  linear_combination (-1 : ℝ) * hk

theorem gCenter_pow_zero_ne (n : ℕ) (hn : 0 < n) : (gCenter ^ n) 0 ≠ 0 := by
  rw [gCenter_pow_apply n]
  intro h
  exact rotZ_pHalf_ne n hn (by
    have := sub_eq_zero.1 h
    exact this.symm)

theorem gCenter_pow_mem (n : ℕ) : (gCenter ^ n) 0 ∈ closedBall (0 : E) 1 := by
  rw [gCenter_pow_apply n]
  simp only [Metric.mem_closedBall, dist_zero_right]
  calc ‖pHalf - (rotZ (Real.cos (n * 1)) (Real.sin (n * 1)) (Real.cos_sq_add_sin_sq _)) pHalf‖
      ≤ ‖pHalf‖ + ‖(rotZ (Real.cos (n * 1)) (Real.sin (n * 1))
        (Real.cos_sq_add_sin_sq _)) pHalf‖ := norm_sub_le _ _
    _ = 1 := by rw [LinearIsometryEquiv.norm_map, norm_pHalf]; norm_num

/-- The closed unit ball is equidecomposable with the punctured closed unit ball. -/
theorem equidec_ball_punctured :
    Equidec (E ≃ᵢ E) (closedBall (0 : E) 1) (closedBall (0 : E) 1 \ {0}) := by
  have hsub : ∀ n : ℕ, (gCenter ^ n) • ({0} : Set E) ⊆ closedBall (0 : E) 1 := by
    rintro n x ⟨y, hy, rfl⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact gCenter_pow_mem n
  have hdisj : ∀ n : ℕ, 0 < n → Disjoint ((gCenter ^ n) • ({0} : Set E)) ({0} : Set E) := by
    intro n hn
    refine Set.disjoint_left.2 ?_
    rintro x ⟨y, hy, rfl⟩ hx0
    rw [Set.mem_singleton_iff] at hy hx0
    subst hy
    exact gCenter_pow_zero_ne n hn hx0
  exact Equidec.absorb gCenter {0} (closedBall (0 : E) 1) hsub hdisj

end Center

/-- **The closed unit ball of `ℝ³` is paradoxical.** -/
theorem paradoxical_ball : Paradoxical (E ≃ᵢ E) (closedBall (0 : E) 1) := by
  have h : Paradoxical (E ≃ᵢ E) (closedBall (0 : E) 1 \ {0}) :=
    paradoxical_punctured_ball.map toIso (fun g x => rfl)
  exact h.of_equidec equidec_ball_punctured.symm

end BT

/-
The Hausdorff paradox: the unit sphere in `ℝ³` is paradoxical for the action of the group of
linear isometries.
-/
import RequestProject.BT.Equidec
import RequestProject.BT.FreeRotations
import RequestProject.BT.FixedPoints
import RequestProject.BT.FreeGroupParadox
import RequestProject.BT.AbsorbAngles

open Set Function
open scoped Pointwise

namespace BT

/-- The unit sphere of `ℝ³`. -/
def S2 : Set E := Metric.sphere (0 : E) 1

theorem mem_S2 {x : E} : x ∈ S2 ↔ ‖x‖ = 1 := by
  simp [S2, mem_sphere_iff_norm]

theorem linIso_mem_S2 (g : E ≃ₗᵢ[ℝ] E) {x : E} (hx : x ∈ S2) : g x ∈ S2 := by
  rw [mem_S2] at hx ⊢
  rw [g.norm_map, hx]

/-- The set of poles: points of the sphere fixed by some nontrivial element of the free
group of rotations. -/
def poles : Set E := {x | x ∈ S2 ∧ ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ phi w x = x}

theorem poles_subset : poles ⊆ S2 := fun _ hx => hx.1

theorem freeGroup_countable : Countable (FreeGroup (Fin 2)) :=
  Function.Injective.countable FreeGroup.toWord_injective

theorem pow_two_ne_one {w : FreeGroup (Fin 2)} (hw : w ≠ 1) : w * w ≠ 1 := by
  intro h
  apply hw
  have h2 : w ^ 2 = (1 : FreeGroup (Fin 2)) ^ 2 := by
    rw [one_pow, pow_two]; exact h
  exact pow_left_injective (n := 2) (by norm_num) h2

theorem poles_countable : poles.Countable := by
  have hc : Countable (FreeGroup (Fin 2)) := freeGroup_countable
  have : poles ⊆ ⋃ w : {w : FreeGroup (Fin 2) // w ≠ 1},
      {x : E | x ∈ Metric.sphere (0 : E) 1 ∧ phi (w : FreeGroup (Fin 2)) x = x} := by
    rintro x ⟨hx, w, hw, hwx⟩
    exact mem_iUnion.2 ⟨⟨w, hw⟩, hx, hwx⟩
  refine Set.Countable.mono this (Set.countable_iUnion fun w => ?_)
  refine countable_fixedPoints (phi (w : FreeGroup (Fin 2))) ?_
  intro h
  refine pow_two_ne_one w.2 ?_
  have : phi ((w : FreeGroup (Fin 2)) * w) = phi 1 := by rw [map_mul, map_one, h]
  exact phi_injective this

/-- The sphere with the poles removed. -/
def SX : Set E := S2 \ poles

theorem SX_subset : SX ⊆ S2 := diff_subset

/-- The action of the free group preserves `SX`. -/
theorem phi_mapsTo (w : FreeGroup (Fin 2)) {x : E} (hx : x ∈ SX) : phi w x ∈ SX := by
  refine ⟨linIso_mem_S2 _ hx.1, ?_⟩
  rintro ⟨-, v, hv, hvx⟩
  refine hx.2 ⟨hx.1, w⁻¹ * v * w, ?_, ?_⟩
  · intro h
    apply hv
    have : v = w * w⁻¹ * v * w * w⁻¹ := by group
    rw [this]
    rw [show w * w⁻¹ * v * w * w⁻¹ = w * (w⁻¹ * v * w) * w⁻¹ by group, h]
    group
  · have : phi (w⁻¹ * v * w) x = (phi w)⁻¹ (phi v (phi w x)) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [this, hvx]
    exact (phi w).symm_apply_apply x

/-- The action of the free group on `SX` is free. -/
theorem phi_free {w : FreeGroup (Fin 2)} {x : E} (hx : x ∈ SX) (h : phi w x = x) : w = 1 := by
  by_contra hw
  exact hx.2 ⟨hx.1, w, hw, h⟩

section Selector

/-- The orbit equivalence of the free group action on `SX`. -/
def orbitSetoid : Setoid ↥SX where
  r x y := ∃ w : FreeGroup (Fin 2), phi w (x : E) = (y : E)
  iseqv := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨w, hw⟩
      refine ⟨w⁻¹, ?_⟩
      rw [map_inv, ← hw]
      exact (phi w).symm_apply_apply _
    · rintro x y z ⟨w, hw⟩ ⟨v, hv⟩
      exact ⟨v * w, by rw [map_mul]; simp only [LinearIsometryEquiv.coe_mul,
        Function.comp_apply, hw, hv]⟩

/-- A set of representatives for the orbits of the free group action on `SX`. -/
def M : Set E := Set.range fun q : Quotient orbitSetoid => ((Quotient.out q : ↥SX) : E)

theorem M_subset : M ⊆ SX := by
  rintro x ⟨q, rfl⟩
  exact (Quotient.out q).2

theorem exists_mem_M {x : E} (hx : x ∈ SX) : ∃ w : FreeGroup (Fin 2), ∃ m ∈ M, phi w m = x := by
  set q : Quotient orbitSetoid := Quotient.mk orbitSetoid ⟨x, hx⟩ with hq
  have hout : orbitSetoid.r (Quotient.out q) ⟨x, hx⟩ := Quotient.exact (Quotient.out_eq q)
  obtain ⟨w, hw⟩ := hout
  exact ⟨w, ((Quotient.out q : ↥SX) : E), ⟨q, rfl⟩, hw⟩

theorem M_unique {w w' : FreeGroup (Fin 2)} {m m' : E} (hm : m ∈ M) (hm' : m' ∈ M)
    (h : phi w m = phi w' m') : w = w' ∧ m = m' := by
  obtain ⟨q, rfl⟩ := hm
  obtain ⟨q', rfl⟩ := hm'
  have hrel : orbitSetoid.r (Quotient.out q) (Quotient.out q') := by
    refine ⟨w'⁻¹ * w, ?_⟩
    rw [map_mul, map_inv]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [h]
    exact (phi w').symm_apply_apply _
  have hqq : q = q' := by
    have := Quotient.sound hrel
    rwa [Quotient.out_eq, Quotient.out_eq] at this
  subst hqq
  have hfix : phi (w'⁻¹ * w) ((Quotient.out q : ↥SX) : E) = ((Quotient.out q : ↥SX) : E) := by
    rw [map_mul, map_inv]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply]
    rw [h]
    exact (phi w').symm_apply_apply _
  have hone := phi_free (M_subset ⟨q, rfl⟩) hfix
  exact ⟨(inv_mul_eq_one.mp hone).symm, rfl⟩

/-- The part of `SX` corresponding to a set of group elements. -/
def XA (A : Set (FreeGroup (Fin 2))) : Set E := ⋃ w ∈ A, (phi w) • M

theorem XA_subset (A : Set (FreeGroup (Fin 2))) : XA A ⊆ SX := by
  rintro x hx
  obtain ⟨w, hw, m, hm, rfl⟩ := by simpa [XA] using hx
  exact phi_mapsTo w (M_subset hm)

theorem mem_XA {A : Set (FreeGroup (Fin 2))} {x : E} :
    x ∈ XA A ↔ ∃ w ∈ A, ∃ m ∈ M, phi w m = x := by
  simp [XA, Set.mem_smul_set, eq_comm]

theorem XA_univ : XA Set.univ = SX := by
  apply Set.Subset.antisymm (XA_subset _)
  intro x hx
  obtain ⟨w, m, hm, hwm⟩ := exists_mem_M hx
  exact mem_XA.2 ⟨w, mem_univ w, m, hm, hwm⟩

theorem XA_mono {A B : Set (FreeGroup (Fin 2))} (h : A ⊆ B) : XA A ⊆ XA B := by
  intro x hx
  obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hx
  exact mem_XA.2 ⟨w, h hw, m, hm, hwm⟩

theorem XA_union (A B : Set (FreeGroup (Fin 2))) : XA (A ∪ B) = XA A ∪ XA B := by
  ext x
  simp only [mem_XA, Set.mem_union]
  constructor
  · rintro ⟨w, (hw | hw), m, hm, hwm⟩
    · exact Or.inl ⟨w, hw, m, hm, hwm⟩
    · exact Or.inr ⟨w, hw, m, hm, hwm⟩
  · rintro (⟨w, hw, m, hm, hwm⟩ | ⟨w, hw, m, hm, hwm⟩)
    · exact ⟨w, Or.inl hw, m, hm, hwm⟩
    · exact ⟨w, Or.inr hw, m, hm, hwm⟩

theorem XA_disjoint {A B : Set (FreeGroup (Fin 2))} (h : Disjoint A B) :
    Disjoint (XA A) (XA B) := by
  refine Set.disjoint_left.2 ?_
  intro x hx hx'
  obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hx
  obtain ⟨v, hv, m', hm', hvm⟩ := mem_XA.1 hx'
  obtain ⟨rfl, -⟩ := M_unique hm hm' (hwm.trans hvm.symm)
  exact Set.disjoint_left.1 h hw hv

theorem XA_smul (u : FreeGroup (Fin 2)) (A : Set (FreeGroup (Fin 2))) :
    (phi u) • XA A = XA ((fun w => u * w) '' A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨w, hw, m, hm, hwm⟩ := mem_XA.1 hy
    refine mem_XA.2 ⟨u * w, ⟨w, hw, rfl⟩, m, hm, ?_⟩
    rw [map_mul]
    simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply, hwm]
    rfl
  · intro hx
    obtain ⟨w', ⟨w, hw, rfl⟩, m, hm, hwm⟩ := mem_XA.1 hx
    refine ⟨phi w m, mem_XA.2 ⟨w, hw, m, hm, rfl⟩, ?_⟩
    rw [map_mul] at hwm
    simpa using hwm

end Selector

/-- **The Hausdorff paradox** (free part): the sphere minus the countable set of poles is
paradoxical. -/
theorem paradoxical_SX : Paradoxical (E ≃ₗᵢ[ℝ] E) SX := by
  obtain ⟨A, hdisj, hunion, hd1, hu1, hd2, hu2⟩ := freeGroup_paradoxical
  refine ⟨XA (A 0) ∪ XA (A 1), XA (A 2) ∪ XA (A 3), ?_, ?_, ?_, ?_⟩
  · rw [← XA_union, ← XA_union, ← XA_union, ← XA_univ]
    congr 1
    rw [← hunion]
    ext w
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro ((h | h) | (h | h))
      exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩]
    · rintro ⟨i, hi⟩
      fin_cases i
      exacts [Or.inl (Or.inl hi), Or.inl (Or.inr hi), Or.inr (Or.inl hi), Or.inr (Or.inr hi)]
  · rw [← XA_union, ← XA_union]
    refine XA_disjoint ?_
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hdisj 0 2 (by decide), hdisj 0 3 (by decide)⟩,
      hdisj 1 2 (by decide), hdisj 1 3 (by decide)⟩
  · have hsm : Equidec (E ≃ₗᵢ[ℝ] E) (XA (A 1)) ((phi (FreeGroup.of 0)) • XA (A 1)) :=
      Equidec.smul_set _ _
    have h := Equidec.union (XA_disjoint (hdisj 0 1 (by decide)))
      (by
        rw [XA_smul]
        refine XA_disjoint ?_
        have : (fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1 = FreeGroup.of (0 : Fin 2) • A 1 :=
          rfl
        rw [this]
        exact hd1)
      (Equidec.refl (XA (A 0))) hsm
    have heq : A 0 ∪ (fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1 = Set.univ := hu1
    have hunion2 : XA (A 0) ∪ XA ((fun w => FreeGroup.of (0 : Fin 2) * w) '' A 1) = SX := by
      rw [← XA_union, heq, XA_univ]
    rw [XA_smul, hunion2] at h
    exact h
  · have hsm : Equidec (E ≃ₗᵢ[ℝ] E) (XA (A 3)) ((phi (FreeGroup.of 1)) • XA (A 3)) :=
      Equidec.smul_set _ _
    have h := Equidec.union (XA_disjoint (hdisj 2 3 (by decide)))
      (by
        rw [XA_smul]
        refine XA_disjoint ?_
        have : (fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3 = FreeGroup.of (1 : Fin 2) • A 3 :=
          rfl
        rw [this]
        exact hd2)
      (Equidec.refl (XA (A 2))) hsm
    have heq : A 2 ∪ (fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3 = Set.univ := hu2
    have hunion2 : XA (A 2) ∪ XA ((fun w => FreeGroup.of (1 : Fin 2) * w) '' A 3) = SX := by
      rw [← XA_union, heq, XA_univ]
    rw [XA_smul, hunion2] at h
    exact h

/-- The sphere is equidecomposable with the sphere minus the poles. -/
theorem equidec_S2_SX : Equidec (E ≃ₗᵢ[ℝ] E) S2 SX := by
  obtain ⟨g, hg⟩ := exists_absorbing_rotation poles poles_countable poles_subset
  have hsub : ∀ n : ℕ, (g ^ n) • poles ⊆ S2 := by
    rintro n x ⟨y, hy, rfl⟩
    exact linIso_mem_S2 _ (poles_subset hy)
  exact Equidec.absorb g poles S2 hsub hg

/-- **The Hausdorff paradox**: the unit sphere in `ℝ³` is paradoxical. -/
theorem paradoxical_S2 : Paradoxical (E ≃ₗᵢ[ℝ] E) S2 :=
  paradoxical_SX.of_equidec equidec_S2_SX.symm

end BT

/-
The set of fixed points on the unit sphere of a linear isometry of `ℝ³` which is not an
involution is countable (in fact it has at most two elements).
-/
import RequestProject.BT.Rotations

open Module

namespace BT

/-- A linear isometry of `ℝ³` whose square is not the identity fixes at most two points of
the unit sphere; in particular its fixed point set on the sphere is countable. -/
theorem countable_fixedPoints (g : E ≃ₗᵢ[ℝ] E) (hg : g * g ≠ 1) :
    {x : E | x ∈ Metric.sphere (0 : E) 1 ∧ g x = x}.Countable := by
  classical
  set V : Submodule ℝ E := LinearMap.ker (g.toLinearEquiv.toLinearMap - LinearMap.id) with hV
  have hmemV : ∀ x : E, x ∈ V ↔ g x = x := by
    intro x
    simp [hV, LinearMap.mem_ker, sub_eq_zero]
  -- the fixed subspace has dimension at most one
  have hrank : finrank ℝ V ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : 2 ≤ finrank ℝ V := hcon
    have hsum : finrank ℝ V + finrank ℝ (Vᗮ : Submodule ℝ E) = 3 := by
      rw [Submodule.finrank_add_finrank_orthogonal V, finrank_euclideanSpace_fin]
    have hperp : finrank ℝ (Vᗮ : Submodule ℝ E) ≤ 1 := by omega
    have hinv : ∀ w ∈ Vᗮ, g w ∈ Vᗮ := by
      intro w hw
      rw [Submodule.mem_orthogonal]
      intro u hu
      have hgu : g u = u := (hmemV u).1 hu
      have : inner ℝ (g u) (g w) = inner ℝ u w := g.inner_map_map u w
      rw [hgu] at this
      rw [this]
      exact (Submodule.mem_orthogonal V w).1 hw u hu
    have hsq : ∀ w ∈ Vᗮ, g (g w) = w := by
      intro w hw
      rcases eq_or_ne w 0 with rfl | hw0
      · simp
      · have hle : (ℝ ∙ w) ≤ Vᗮ := by
          rw [Submodule.span_le, Set.singleton_subset_iff]
          exact hw
        have hspan : (ℝ ∙ w) = Vᗮ := by
          refine Submodule.eq_of_le_of_finrank_le hle ?_
          rw [finrank_span_singleton hw0]
          exact hperp
        have hgw : g w ∈ (ℝ ∙ w) := by
          rw [hspan]
          exact hinv w hw
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hgw
        have hnorm : ‖w‖ = |c| * ‖w‖ := by
          have : ‖g w‖ = ‖w‖ := g.norm_map w
          rw [← hc, norm_smul, Real.norm_eq_abs] at this
          exact this.symm
        have habs : |c| = 1 := by
          have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
          have h1 : |c| * ‖w‖ = 1 * ‖w‖ := by rw [one_mul]; exact hnorm.symm
          exact mul_right_cancel₀ (ne_of_gt hwpos) h1
        have hcc : c * c = 1 := by
          rw [← abs_mul_abs_self, habs]; norm_num
        rw [← hc]
        show g (c • w) = w
        rw [map_smul, ← hc, smul_smul, hcc, one_smul]
    have : g * g = 1 := by
      apply LinearIsometryEquiv.ext
      intro x
      have hcompl : IsCompl V (Vᗮ : Submodule ℝ E) :=
        Submodule.isCompl_orthogonal_of_hasOrthogonalProjection
      have hx : x ∈ V ⊔ Vᗮ := by rw [hcompl.sup_eq_top]; trivial
      obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.1 hx
      show g (g (v + w)) = v + w
      rw [map_add, map_add, (hmemV v).1 hv, (hmemV v).1 hv, hsq w hw]
    exact hg this
  -- hence at most two unit vectors are fixed
  rcases Set.eq_empty_or_nonempty {x : E | x ∈ Metric.sphere (0 : E) 1 ∧ g x = x} with h | ⟨x₀, hx₀⟩
  · rw [h]; exact Set.countable_empty
  · have hx₀norm : ‖x₀‖ = 1 := by
      have := hx₀.1
      rwa [mem_sphere_iff_norm, sub_zero] at this
    have hx₀0 : x₀ ≠ 0 := by
      intro h
      rw [h, norm_zero] at hx₀norm
      norm_num at hx₀norm
    have hx₀V : x₀ ∈ V := (hmemV x₀).2 hx₀.2
    have hspan : (ℝ ∙ x₀) = V := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact hx₀V
      · rw [finrank_span_singleton hx₀0]
        exact hrank
    refine Set.Countable.mono ?_ ((Set.countable_singleton (-x₀)).insert x₀)
    rintro y ⟨hy1, hy2⟩
    have hynorm : ‖y‖ = 1 := by rwa [mem_sphere_iff_norm, sub_zero] at hy1
    have hyV : y ∈ V := (hmemV y).2 hy2
    rw [← hspan] at hyV
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hyV
    have habs : |c| = 1 := by
      have : ‖y‖ = |c| * ‖x₀‖ := by rw [← hc, norm_smul, Real.norm_eq_abs]
      rw [hynorm, hx₀norm, mul_one] at this
      exact this.symm
    have hcases : c = 1 ∨ c = -1 := by
      have hcc : c * c = 1 := by rw [← abs_mul_abs_self, habs]; norm_num
      have h1 : (c - 1) * (c + 1) = 0 := by nlinarith
      rcases mul_eq_zero.1 h1 with h | h
      · left; linarith
      · right; linarith
    rcases hcases with h | h
    · left; rw [← hc, h, one_smul]
    · right; rw [Set.mem_singleton_iff, ← hc, h]; module

end BT

