import RequestProject.Paradoxical

/-!
# Banach Tarski: a free group of rotations of `ℝ³`
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

namespace Frontier

open Set Function

/-! ## A free group of rotations of `ℝ³`

Following the classical argument, the two rotations by `arccos (3/5)` about the `z`- and the
`x`-axis generate a free subgroup of `SO(3)`.  Freeness is proved by a `5`-adic argument:
a nonempty reduced word of length `n`, applied to the integral vector `(1,0,2)` and rescaled
by `5 ^ n`, gives an integral vector which is nonzero modulo `5`.
-/

namespace FreeRotations

open Matrix

/-- The special orthogonal group of `ℝ³`. -/
abbrev SO3 := Matrix.specialOrthogonalGroup (Fin 3) ℝ

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma coe_inv_SO3 (g : SO3) :
    ((g⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ := by
  ext i j; rfl

/-- Rotation by `arccos (3/5)` about the `z`-axis. -/
noncomputable def matA : Matrix (Fin 3) (Fin 3) ℝ := !![3/5, -4/5, 0; 4/5, 3/5, 0; 0, 0, 1]

/-- Rotation by `arccos (3/5)` about the `x`-axis. -/
noncomputable def matB : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; 0, 3/5, -4/5; 0, 4/5, 3/5]

lemma matA_mem : matA ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, by simp [matA, Matrix.det_fin_three]; norm_num⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matA, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

lemma matB_mem : matB ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, by simp [matB, Matrix.det_fin_three]; norm_num⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matB, Matrix.mul_apply, Fin.sum_univ_three] <;> norm_num

/-- The two generating rotations, as elements of `SO(3)`. -/
noncomputable def gen : Bool → SO3
  | false => ⟨matA, matA_mem⟩
  | true => ⟨matB, matB_mem⟩

/-- The group homomorphism from the free group of rank two to `SO(3)` sending the two
generators to the two rotations. -/
noncomputable def rho : FreeGroup Bool →* SO3 := FreeGroup.lift gen

/-- The matrix attached to a letter. -/
noncomputable def letterMat (x : Bool × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  ((cond x.2 (gen x.1) (gen x.1)⁻¹ : SO3) : Matrix (Fin 3) (Fin 3) ℝ)

/-- Five times the matrix of a letter, as an integral matrix. -/
def MI : Bool × Bool → Matrix (Fin 3) (Fin 3) ℤ
  | (false, true) => !![3, -4, 0; 4, 3, 0; 0, 0, 5]
  | (false, false) => !![3, 4, 0; -4, 3, 0; 0, 0, 5]
  | (true, true) => !![5, 0, 0; 0, 3, -4; 0, 4, 3]
  | (true, false) => !![5, 0, 0; 0, 3, 4; 0, -4, 3]

/-- The reduction of `MI` modulo `5`. -/
def Nm : Bool × Bool → Matrix (Fin 3) (Fin 3) (ZMod 5)
  | (false, true) => !![3, 1, 0; 4, 3, 0; 0, 0, 0]
  | (false, false) => !![3, 4, 0; 1, 3, 0; 0, 0, 0]
  | (true, true) => !![0, 0, 0; 0, 3, 1; 0, 4, 3]
  | (true, false) => !![0, 0, 0; 0, 3, 4; 0, 1, 3]

lemma map_MI_eq_Nm : ∀ x : Bool × Bool, (MI x).map (Int.cast : ℤ → ZMod 5) = Nm x := by decide

/-- The real matrix of a letter, as a real matrix with integral entries divided by five. -/
noncomputable def MIR (x : Bool × Bool) : Matrix (Fin 3) (Fin 3) ℝ :=
  (MI x).map (Int.cast : ℤ → ℝ)

lemma letterMat_eq (x : Bool × Bool) : letterMat x = (5 : ℝ)⁻¹ • MIR x := by
  rw [MIR]
  obtain ⟨c, s⟩ := x
  cases c <;> cases s <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [letterMat, gen, matA, matB, MI, coe_inv_SO3, Matrix.transpose_apply] <;> norm_num

/-- The starting integral vector. -/
def v0 : Fin 3 → ℤ := ![1, 0, 2]

/-- The integral vector attached to a word: `5 ^ (length) ⬝ w ⬝ v0`. -/
def iv : List (Bool × Bool) → (Fin 3 → ℤ) :=
  fun L => L.foldr (fun x v => (MI x).mulVec v) v0

@[simp] lemma iv_nil : iv [] = v0 := rfl

@[simp] lemma iv_cons (x : Bool × Bool) (L : List (Bool × Bool)) :
    iv (x :: L) = (MI x).mulVec (iv L) := rfl

/-- The reduction of `iv` modulo `5`. -/
def ivm (L : List (Bool × Bool)) : Fin 3 → ZMod 5 := fun i => ((iv L i : ℤ) : ZMod 5)

/-- `mulVec` commutes with the application of a ring homomorphism. -/
lemma mulVec_map_ringHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (M : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    (M.map f).mulVec (fun i => f (v i)) = fun i => f (M.mulVec v i) := by
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]

lemma ivm_cons (x : Bool × Bool) (L : List (Bool × Bool)) :
    ivm (x :: L) = (Nm x).mulVec (ivm L) := by
  have h := mulVec_map_ringHom (Int.castRingHom (ZMod 5)) (MI x) (iv L)
  simp only [Int.coe_castRingHom] at h
  rw [map_MI_eq_Nm] at h
  exact h.symm

/-- The vector attached to a single letter, modulo `5`. -/
def v0m : Fin 3 → ZMod 5 := ![1, 0, 2]

/-- The invariant direction attached to a letter. -/
def uu (x : Bool × Bool) : Fin 3 → ZMod 5 := (Nm x).mulVec v0m

lemma uu_ne_zero : ∀ x : Bool × Bool, uu x ≠ 0 := by decide

lemma Nm_mulVec_uu : ∀ x y : Bool × Bool, y ≠ (x.1, !x.2) →
    ∃ d : ZMod 5, d ≠ 0 ∧ (Nm x).mulVec (uu y) = d • uu x := by decide

lemma ivm_singleton (x : Bool × Bool) : ivm [x] = uu x := by
  have : ivm [] = v0m := by
    funext i; fin_cases i <;> simp [ivm, iv, v0, v0m]
  rw [ivm_cons, this, uu]

/-- **The key invariant**: for a nonempty reduced word, the associated integral vector is a
nonzero multiple of `uu` of its first letter, modulo `5`. -/
lemma ivm_invariant : ∀ (L : List (Bool × Bool)) (x : Bool × Bool),
    FreeGroup.IsReduced (x :: L) → ∃ c : ZMod 5, c ≠ 0 ∧ ivm (x :: L) = c • uu x := by
  intro L
  induction L with
  | nil => exact fun x _ => ⟨1, by decide, by rw [ivm_singleton, one_smul]⟩
  | cons y rest ih =>
      intro x hred
      rw [FreeGroup.isReduced_cons_cons] at hred
      obtain ⟨c, hc, hcy⟩ := ih y hred.2
      have hne : y ≠ (x.1, !x.2) := by
        intro hy
        have h1 : x.1 = y.1 := by rw [hy]
        have h2 := hred.1 h1
        rw [hy] at h2
        simp at h2
      obtain ⟨d, hd, hdy⟩ := Nm_mulVec_uu x y hne
      refine ⟨d * c, mul_ne_zero hd hc, ?_⟩
      rw [ivm_cons, hcy, Matrix.mulVec_smul, hdy, smul_smul, mul_comm c d]

/-- The real matrix of a word, in terms of the letters. -/
lemma rho_mk (L : List (Bool × Bool)) :
    ((rho (FreeGroup.mk L) : SO3) : Matrix (Fin 3) (Fin 3) ℝ) = (L.map letterMat).prod := by
  rw [rho, FreeGroup.lift_mk]
  induction L with
  | nil => simp
  | cons x L ih =>
      simp only [List.map_cons, List.prod_cons, Submonoid.coe_mul, ih]
      rfl

/-- The real vector attached to a word. -/
noncomputable def ivR (L : List (Bool × Bool)) : Fin 3 → ℝ := fun i => ((iv L i : ℤ) : ℝ)

lemma ivR_cons (x : Bool × Bool) (L : List (Bool × Bool)) :
    ivR (x :: L) = (MIR x).mulVec (ivR L) := by
  exact (mulVec_map_ringHom (Int.castRingHom ℝ) (MI x) (iv L)).symm

/-- The real matrix of a word applied to `v0`, rescaled by `5 ^ n`, is the integral vector
`iv`. -/
lemma prod_mulVec (L : List (Bool × Bool)) :
    ((5 : ℝ) ^ L.length) • ((L.map letterMat).prod.mulVec (fun i => ((v0 i : ℤ) : ℝ)))
      = ivR L := by
  induction L with
  | nil => simp; rfl
  | cons x L ih =>
      have h55 : (5:ℝ) ^ L.length * 5 * 5⁻¹ = 5 ^ L.length := by field_simp
      rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ← Matrix.mulVec_mulVec,
        letterMat_eq, smul_mulVec, smul_smul, h55, ivR_cons, ← ih, Matrix.mulVec_smul]

/-- **Freeness**: the homomorphism `rho` is injective, so the two rotations generate a free
group of rank two inside `SO(3)`. -/
theorem rho_injective : Function.Injective rho := by
  rw [injective_iff_map_eq_one]
  intro w hw
  by_contra hne
  -- the reduced word of `w`
  set L := w.toWord with hL
  have hLne : L ≠ [] := by
    simp only [hL, ne_eq, FreeGroup.toWord_eq_nil_iff]
    exact hne
  obtain ⟨x, L', hx⟩ : ∃ x L', L = x :: L' := by
    cases hcase : L with
    | nil => exact absurd hcase hLne
    | cons a l => exact ⟨a, l, rfl⟩
  have hred : FreeGroup.IsReduced L := by rw [hL]; exact FreeGroup.isReduced_toWord
  have hmk : FreeGroup.mk L = w := by rw [hL]; exact FreeGroup.mk_toWord
  -- the matrix of `w` is the identity
  have hmat : (L.map letterMat).prod = 1 := by
    rw [← rho_mk, hmk, hw]
    rfl
  -- hence the integral vector is `5 ^ n • v0`
  have hveq : (fun i => ((iv L i : ℤ) : ℝ)) = fun i => ((5 : ℝ) ^ L.length * ((v0 i : ℤ) : ℝ)) := by
    rw [show (fun i => ((iv L i : ℤ) : ℝ)) = ivR L from rfl, ← prod_mulVec, hmat]
    funext i
    simp [Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
  have hint : ∀ i, iv L i = 5 ^ L.length * v0 i := by
    intro i
    have := congrFun hveq i
    have h2 : ((iv L i : ℤ) : ℝ) = (((5 ^ L.length * v0 i : ℤ)) : ℝ) := by
      rw [this]; push_cast; ring
    exact_mod_cast h2
  have hzero : ivm L = 0 := by
    funext i
    have : iv L i = 5 ^ L.length * v0 i := hint i
    simp only [ivm, this, Pi.zero_apply]
    push_cast
    have h5 : ((5 : ZMod 5)) = 0 := by decide
    rw [h5]
    have : L.length ≠ 0 := by
      rw [hx]; simp
    rw [zero_pow this, zero_mul]
  obtain ⟨c, hc, hcv⟩ := ivm_invariant L' x (by rw [← hx]; exact hred)
  rw [← hx, hzero] at hcv
  have : uu x = 0 := by
    have hcinv : c⁻¹ * c = 1 := inv_mul_cancel₀ hc
    have := congrArg (fun v : Fin 3 → ZMod 5 => c⁻¹ • v) hcv.symm
    simpa [smul_smul, hcinv] using this
  exact uu_ne_zero x this

end FreeRotations

end Frontier

/-
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.FreeRotations

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
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

namespace Frontier

open Set Function

/-! ## The action of `SO(3)` by isometries of `ℝ³` -/

namespace Sphere

open Matrix FreeRotations

/-- Euclidean three-space. -/
abbrev E := EuclideanSpace ℝ (Fin 3)

/-- The group of isometries of `ℝ³`, as a subgroup of the group of permutations. -/
def IsomGroup : Subgroup (Equiv.Perm E) where
  carrier := {σ | Isometry σ}
  mul_mem' {a b} ha hb :=
    show Isometry ⇑(a * b) from (show Isometry ⇑a from ha).comp (show Isometry ⇑b from hb)
  one_mem' := isometry_id
  inv_mem' {a} ha := by
    refine Isometry.of_dist_eq (fun x y => ?_)
    have := ha.dist_eq (a.symm x) (a.symm y)
    simpa using this.symm

lemma transpose_mul_self (M : SO3) : (M.1)ᵀ * M.1 = 1 := by
  have h := M.2
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff'] at h
  simpa [Matrix.star_eq_conjTranspose] using h.1

lemma self_mul_transpose (M : SO3) : M.1 * (M.1)ᵀ = 1 := by
  have h := M.2
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff] at h
  simpa [Matrix.star_eq_conjTranspose] using h.1

lemma norm_eq_sqrt_dotProduct (x : E) : ‖x‖ = Real.sqrt (x.ofLp ⬝ᵥ x.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, Real.norm_eq_abs, pow_two]

lemma dotProduct_mulVec_self (M : SO3) (u : Fin 3 → ℝ) :
    (M.1 *ᵥ u) ⬝ᵥ (M.1 *ᵥ u) = u ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    transpose_mul_self, Matrix.one_mulVec]

/-- A rotation, viewed as a permutation of `ℝ³`. -/
def toPerm (M : SO3) : Equiv.Perm E where
  toFun v := WithLp.toLp 2 (M.1 *ᵥ v.ofLp)
  invFun v := WithLp.toLp 2 ((M.1)ᵀ *ᵥ v.ofLp)
  left_inv v := by
    show WithLp.toLp 2 ((M.1)ᵀ *ᵥ (M.1 *ᵥ v.ofLp)) = v
    rw [Matrix.mulVec_mulVec, transpose_mul_self, Matrix.one_mulVec]
  right_inv v := by
    show WithLp.toLp 2 (M.1 *ᵥ ((M.1)ᵀ *ᵥ v.ofLp)) = v
    rw [Matrix.mulVec_mulVec, self_mul_transpose, Matrix.one_mulVec]

@[simp] lemma toPerm_apply (M : SO3) (v : E) : toPerm M v = WithLp.toLp 2 (M.1 *ᵥ v.ofLp) := rfl

lemma toPerm_mul (M N : SO3) (v : E) : toPerm (M * N) v = toPerm M (toPerm N v) := by
  show WithLp.toLp 2 ((M.1 * N.1) *ᵥ v.ofLp) = WithLp.toLp 2 (M.1 *ᵥ (N.1 *ᵥ v.ofLp))
  rw [← Matrix.mulVec_mulVec]

lemma toPerm_one (v : E) : toPerm 1 v = v := by
  show WithLp.toLp 2 ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.ofLp) = v
  rw [Matrix.one_mulVec]

lemma toPerm_isometry (M : SO3) : Isometry (toPerm M) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm]
  have hsub : toPerm M x - toPerm M y = WithLp.toLp 2 (M.1 *ᵥ (x.ofLp - y.ofLp)) := by
    rw [Matrix.mulVec_sub]
    rfl
  rw [hsub, norm_eq_sqrt_dotProduct, norm_eq_sqrt_dotProduct]
  congr 1
  exact dotProduct_mulVec_self M _

/-- The rotation group of `ℝ³` inside the isometry group. -/
def toIsom : SO3 →* IsomGroup where
  toFun M := ⟨toPerm M, toPerm_isometry M⟩
  map_one' := Subtype.ext (Equiv.ext fun v => by
    show WithLp.toLp 2 ((1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ v.ofLp) = v
    rw [Matrix.one_mulVec])
  map_mul' M N := Subtype.ext (Equiv.ext fun v => by
    show WithLp.toLp 2 ((M.1 * N.1) *ᵥ v.ofLp) = WithLp.toLp 2 (M.1 *ᵥ (N.1 *ᵥ v.ofLp))
    rw [← Matrix.mulVec_mulVec])

lemma toIsom_injective : Function.Injective toIsom := by
  intro M N hMN
  have h : ∀ v : Fin 3 → ℝ, M.1 *ᵥ v = N.1 *ᵥ v := by
    intro v
    have := congrArg (fun (g : IsomGroup) => (g : Equiv.Perm E) (WithLp.toLp 2 v)) hMN
    simpa [toIsom, toPerm] using this
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-! ## Rotations about the coordinate axes, and absorption of a countable set -/

/-- Rotation by the angle `t` about the `z`-axis. -/
noncomputable def rotZmat (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos t, -Real.sin t, 0; Real.sin t, Real.cos t, 0; 0, 0, 1]

/-- Rotation by the angle `t` about the `x`-axis. -/
noncomputable def rotXmat (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos t, -Real.sin t; 0, Real.sin t, Real.cos t]

lemma rotZmat_mem (t : ℝ) : rotZmat t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, by simp [rotZmat, Matrix.det_fin_three]; nlinarith [Real.sin_sq_add_cos_sq t]⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZmat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

lemma rotXmat_mem (t : ℝ) : rotXmat t ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, by simp [rotXmat, Matrix.det_fin_three]; nlinarith [Real.sin_sq_add_cos_sq t]⟩
  rw [Matrix.mem_orthogonalGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotXmat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

/-- Rotation about the `z`-axis, as an element of `SO(3)`. -/
noncomputable def rotZ (t : ℝ) : SO3 := ⟨rotZmat t, rotZmat_mem t⟩

/-- Rotation about the `x`-axis, as an element of `SO(3)`. -/
noncomputable def rotX (t : ℝ) : SO3 := ⟨rotXmat t, rotXmat_mem t⟩

lemma rotZ_mul (a b : ℝ) : rotZ a * rotZ b = rotZ (a + b) := by
  apply Subtype.ext
  show rotZmat a * rotZmat b = rotZmat (a + b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZmat, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

lemma rotX_mul (a b : ℝ) : rotX a * rotX b = rotX (a + b) := by
  apply Subtype.ext
  show rotXmat a * rotXmat b = rotXmat (a + b)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotXmat, Matrix.mul_apply, Fin.sum_univ_three, Real.cos_add, Real.sin_add] <;> ring

lemma rotZ_zero : rotZ 0 = 1 := by
  apply Subtype.ext
  show rotZmat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZmat]

lemma rotX_zero : rotX 0 = 1 := by
  apply Subtype.ext
  show rotXmat 0 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotXmat]

lemma rotZ_pow (t : ℝ) (n : ℕ) : rotZ t ^ n = rotZ (n * t) := by
  induction n with
  | zero => simpa using rotZ_zero.symm
  | succ n ih =>
      rw [pow_succ, ih, rotZ_mul]
      congr 1
      push_cast
      ring

lemma rotX_pow (t : ℝ) (n : ℕ) : rotX t ^ n = rotX (n * t) := by
  induction n with
  | zero => simpa using rotX_zero.symm
  | succ n ih =>
      rw [pow_succ, ih, rotX_mul]
      congr 1
      push_cast
      ring

lemma rotZ_apply (t : ℝ) (v : E) (i : Fin 3) :
    (toPerm (rotZ t) v).ofLp i =
      ![Real.cos t * v.ofLp 0 - Real.sin t * v.ofLp 1,
        Real.sin t * v.ofLp 0 + Real.cos t * v.ofLp 1, v.ofLp 2] i := by
  show (rotZmat t *ᵥ v.ofLp) i = _
  fin_cases i <;> simp [rotZmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals ring

lemma rotX_apply (t : ℝ) (v : E) (i : Fin 3) :
    (toPerm (rotX t) v).ofLp i =
      ![v.ofLp 0, Real.cos t * v.ofLp 1 - Real.sin t * v.ofLp 2,
        Real.sin t * v.ofLp 1 + Real.cos t * v.ofLp 2] i := by
  show (rotXmat t *ᵥ v.ofLp) i = _
  fin_cases i <;> simp [rotXmat, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  all_goals ring

/-- The set of angles with prescribed cosine and sine is countable. -/
lemma countable_cos_sin (c s : ℝ) : {t : ℝ | Real.cos t = c ∧ Real.sin t = s}.Countable := by
  rcases Set.eq_empty_or_nonempty {t : ℝ | Real.cos t = c ∧ Real.sin t = s} with h | ⟨t₀, ht₀⟩
  · rw [h]; exact Set.countable_empty
  · refine Set.Countable.mono (s₂ := Set.range (fun k : ℤ => t₀ + k * (2 * Real.pi))) ?_
      (Set.countable_range _)
    rintro t ⟨hc, hs⟩
    have h1 : Real.cos (t - t₀) = 1 := by
      have hpy := Real.sin_sq_add_cos_sq t₀
      rw [ht₀.1, ht₀.2] at hpy
      rw [Real.cos_sub, hc, hs, ht₀.1, ht₀.2]
      nlinarith [hpy]
    rw [Real.cos_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    exact ⟨k, by linarith [hk]⟩

/-- For a point off the `z`-axis, only countably many rotations about the `z`-axis can send it
to a given point. -/
lemma countable_bad_Z (x y : E) (hx : (x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2 ≠ 0) :
    {t : ℝ | toPerm (rotZ t) x = y}.Countable := by
  set r : ℝ := (x.ofLp 0) ^ 2 + (x.ofLp 1) ^ 2 with hr
  refine Set.Countable.mono (s₂ := {t : ℝ | Real.cos t =
      (x.ofLp 0 * y.ofLp 0 + x.ofLp 1 * y.ofLp 1) / r ∧
      Real.sin t = (x.ofLp 0 * y.ofLp 1 - x.ofLp 1 * y.ofLp 0) / r}) ?_ (countable_cos_sin _ _)
  intro t ht
  have h0 : Real.cos t * x.ofLp 0 - Real.sin t * x.ofLp 1 = y.ofLp 0 := by
    have h2 : (toPerm (rotZ t) x).ofLp 0 = y.ofLp 0 := by rw [show toPerm (rotZ t) x = y from ht]
    rw [rotZ_apply] at h2
    simpa using h2
  have h1 : Real.sin t * x.ofLp 0 + Real.cos t * x.ofLp 1 = y.ofLp 1 := by
    have h2 : (toPerm (rotZ t) x).ofLp 1 = y.ofLp 1 := by rw [show toPerm (rotZ t) x = y from ht]
    rw [rotZ_apply] at h2
    simpa using h2
  constructor
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 0 * h0 + x.ofLp 1 * h1
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 0 * h1 - x.ofLp 1 * h0

/-- For a point off the `x`-axis, only countably many rotations about the `x`-axis can send it
to a given point. -/
lemma countable_bad_X (x y : E) (hx : (x.ofLp 1) ^ 2 + (x.ofLp 2) ^ 2 ≠ 0) :
    {t : ℝ | toPerm (rotX t) x = y}.Countable := by
  set r : ℝ := (x.ofLp 1) ^ 2 + (x.ofLp 2) ^ 2 with hr
  refine Set.Countable.mono (s₂ := {t : ℝ | Real.cos t =
      (x.ofLp 1 * y.ofLp 1 + x.ofLp 2 * y.ofLp 2) / r ∧
      Real.sin t = (x.ofLp 1 * y.ofLp 2 - x.ofLp 2 * y.ofLp 1) / r}) ?_ (countable_cos_sin _ _)
  intro t ht
  have h0 : Real.cos t * x.ofLp 1 - Real.sin t * x.ofLp 2 = y.ofLp 1 := by
    have h2 : (toPerm (rotX t) x).ofLp 1 = y.ofLp 1 := by rw [show toPerm (rotX t) x = y from ht]
    rw [rotX_apply] at h2
    simpa using h2
  have h1 : Real.sin t * x.ofLp 1 + Real.cos t * x.ofLp 2 = y.ofLp 2 := by
    have h2 : (toPerm (rotX t) x).ofLp 2 = y.ofLp 2 := by rw [show toPerm (rotX t) x = y from ht]
    rw [rotX_apply] at h2
    simpa using h2
  constructor
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 1 * h0 + x.ofLp 2 * h1
  · rw [eq_div_iff hx, hr]
    linear_combination x.ofLp 1 * h1 - x.ofLp 2 * h0

/-- Given a countable set `D` of starting points and a countable target set `C`, all but
countably many angles `t` have the property that no positive iterate of the rotation `rot t`
maps a point of `D` into `C`. -/
lemma exists_good_angle (rot : ℝ → SO3) (hpow : ∀ (t : ℝ) (n : ℕ), rot t ^ n = rot (n * t))
    (D : Set E) (hD : D.Countable) (C : Set E) (hC : C.Countable)
    (hcount : ∀ x ∈ D, ∀ y : E, {t : ℝ | toPerm (rot t) x = y}.Countable) :
    ∃ t : ℝ, ∀ x ∈ D, ∀ n : ℕ, 1 ≤ n → toPerm (rot t ^ n) x ∉ C := by
  classical
  have hbad : {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C}.Countable := by
    have hsub : {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C} ⊆
        ⋃ (x : D), ⋃ (n : {n : ℕ // 1 ≤ n}), ⋃ (y : C),
          {t : ℝ | toPerm (rot ((n : ℕ) * t)) (x : E) = (y : E)} := by
      rintro t ⟨x, hx, n, hn, hmem⟩
      refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, Set.mem_iUnion.2 ⟨⟨n, hn⟩, Set.mem_iUnion.2
        ⟨⟨toPerm (rot t ^ n) x, hmem⟩, ?_⟩⟩⟩
      show toPerm (rot ((n : ℕ) * t)) x = toPerm (rot t ^ n) x
      rw [hpow]
    refine Set.Countable.mono hsub ?_
    haveI := hD.to_subtype
    haveI := hC.to_subtype
    refine Set.countable_iUnion (fun x => Set.countable_iUnion (fun n =>
      Set.countable_iUnion (fun y => ?_)))
    have hinj : Function.Injective (fun t : ℝ => ((n : ℕ) : ℝ) * t) := by
      intro a b hab
      have hn0 : ((n : ℕ) : ℝ) ≠ 0 := by
        have : 0 < (n : ℕ) := n.2
        positivity
      exact mul_left_cancel₀ hn0 hab
    exact Set.Countable.preimage (hcount x x.2 y) hinj
  by_contra hcon
  push_neg at hcon
  refine Cardinal.not_countable_real ?_
  have : (Set.univ : Set ℝ) = {t : ℝ | ∃ x ∈ D, ∃ n : ℕ, 1 ≤ n ∧ toPerm (rot t ^ n) x ∈ C} := by
    symm
    apply Set.eq_univ_of_forall
    intro t
    obtain ⟨x, hx, n, hn, hmem⟩ := hcon t
    exact ⟨x, hx, n, hn, hmem⟩
  rw [this]
  exact hbad

/-! ## Fixed points of rotations, and the Hausdorff paradox -/

/-- The cross product of two vectors of `ℝ³`. -/
def cross3 (u v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

lemma dot_self_eq_zero {w : Fin 3 → ℝ} (h : w ⬝ᵥ w = 0) : w = 0 := by
  simp only [dotProduct, Fin.sum_univ_three] at h
  funext i
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1), sq_nonneg (w 2)]

lemma cross_eq_zero_cases {u v : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (h : cross3 u v = 0) : v = u ∨ v = -u := by
  have hlag : cross3 u v ⬝ᵥ cross3 u v = (u ⬝ᵥ u) * (v ⬝ᵥ v) - (u ⬝ᵥ v) ^ 2 := by
    simp [cross3, dotProduct, Fin.sum_univ_three]; ring
  rw [h, hu, hv] at hlag
  simp at hlag
  have ht : (u ⬝ᵥ v) ^ 2 = 1 := by linarith [hlag]
  set t := u ⬝ᵥ v with htdef
  have hw : (v - t • u) ⬝ᵥ (v - t • u) = 0 := by
    have h1 : (v - t • u) ⬝ᵥ (v - t • u) = v ⬝ᵥ v - 2 * t * (u ⬝ᵥ v) + t ^ 2 * (u ⬝ᵥ u) := by
      simp [dotProduct, Fin.sum_univ_three, Pi.sub_apply, Pi.smul_apply]; ring
    rw [h1, hu, hv, ← htdef]
    nlinarith [ht]
  have hvt : v = t • u := sub_eq_zero.mp (dot_self_eq_zero hw)
  have hfac : (t - 1) * (t + 1) = 0 := by nlinarith [ht]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · left; rw [hvt, show t = 1 by linarith, one_smul]
  · right; rw [hvt, show t = -1 by linarith]; simp

lemma eq_one_of_fixes {M : Matrix (Fin 3) (Fin 3) ℝ} {u v : Fin 3 → ℝ}
    (hu : M *ᵥ u = u) (hv : M *ᵥ v = v) (hc : M *ᵥ cross3 u v = cross3 u v)
    (hne : cross3 u v ⬝ᵥ cross3 u v ≠ 0) : M = 1 := by
  set c := cross3 u v with hcdef
  set P : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => (![u, v, c] j) i with hP
  have hdet : P.det = c ⬝ᵥ c := by
    simp [hP, Matrix.det_fin_three, hcdef, cross3, dotProduct, Fin.sum_univ_three]; ring
  have hNP : (M - 1) * P = 0 := by
    ext i j
    have hcol : ((M - 1) * P) i j = ((M - 1) *ᵥ (![u, v, c] j)) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hP]
    rw [hcol]
    fin_cases j <;> simp [Matrix.sub_mulVec, hu, hv, hc]
  have hPunit : IsUnit P.det := by rw [hdet]; exact isUnit_iff_ne_zero.mpr hne
  have h2 := congrArg (fun X => X * P⁻¹) hNP
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPunit, Matrix.mul_one,
    Matrix.zero_mul] at h2
  exact sub_eq_zero.mp h2

/-- A rotation fixes the cross product of two of its fixed vectors. -/
lemma cross_fixed (M : SO3) {u v : Fin 3 → ℝ} (hu : M.1 *ᵥ u = u) (hv : M.1 *ᵥ v = v) :
    M.1 *ᵥ cross3 u v = cross3 u v := by
  have hdet : M.1.det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp M.2).2
  have key : (M.1)ᵀ *ᵥ (cross3 (M.1 *ᵥ u) (M.1 *ᵥ v)) = (M.1.det) • cross3 u v := by
    funext i
    fin_cases i <;>
      simp [cross3, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three,
        Matrix.transpose_apply] <;> ring
  rw [hu, hv, hdet, one_smul] at key
  calc M.1 *ᵥ cross3 u v = M.1 *ᵥ ((M.1)ᵀ *ᵥ cross3 u v) := by rw [key]
    _ = (M.1 * (M.1)ᵀ) *ᵥ cross3 u v := Matrix.mulVec_mulVec _ _ _
    _ = cross3 u v := by rw [self_mul_transpose, Matrix.one_mulVec]

/-- A rotation fixing two unit vectors which are not equal or opposite is the identity. -/
lemma eq_one_of_two_fixed (M : SO3) {u v : Fin 3 → ℝ} (hu1 : u ⬝ᵥ u = 1) (hv1 : v ⬝ᵥ v = 1)
    (hu : M.1 *ᵥ u = u) (hv : M.1 *ᵥ v = v) (h1 : v ≠ u) (h2 : v ≠ -u) : M.1 = 1 := by
  have hc : cross3 u v ≠ 0 := by
    intro hc0
    rcases cross_eq_zero_cases hu1 hv1 hc0 with h | h
    · exact h1 h
    · exact h2 h
  have hcc : cross3 u v ⬝ᵥ cross3 u v ≠ 0 := fun h => hc (dot_self_eq_zero h)
  exact eq_one_of_fixes hu hv (cross_fixed M hu hv) hcc

/-- The unit sphere of `ℝ³`. -/
def sph : Set E := {v : E | v.ofLp ⬝ᵥ v.ofLp = 1}

/-- The set of points of the sphere fixed by a given rotation. -/
def fixSet (M : SO3) : Set E := {v ∈ sph | toPerm M v = v}

lemma mem_fixSet_iff (M : SO3) (v : E) :
    v ∈ fixSet M ↔ v.ofLp ⬝ᵥ v.ofLp = 1 ∧ M.1 *ᵥ v.ofLp = v.ofLp := by
  constructor
  · rintro ⟨hv, hfix⟩
    refine ⟨hv, ?_⟩
    have := congrArg (fun w : E => w.ofLp) hfix
    simpa using this
  · rintro ⟨hv, hfix⟩
    refine ⟨hv, ?_⟩
    have : WithLp.toLp 2 (M.1 *ᵥ v.ofLp) = WithLp.toLp 2 v.ofLp := by rw [hfix]
    simpa [toPerm] using this

/-- A rotation other than the identity fixes at most two points of the sphere. -/
lemma fixSet_subset_pair (M : SO3) (hM : M.1 ≠ 1) : ∃ a : E, fixSet M ⊆ {a, -a} := by
  by_cases hemp : (fixSet M) = ∅
  · exact ⟨0, by rw [hemp]; exact Set.empty_subset _⟩
  · obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hemp
    refine ⟨u, ?_⟩
    intro v hv
    rw [mem_fixSet_iff] at hu hv
    by_contra hcon
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    have h1 : v.ofLp ≠ u.ofLp := by
      intro h
      exact hcon.1 (by ext i; exact congrFun h i)
    have h2 : v.ofLp ≠ -u.ofLp := by
      intro h
      refine hcon.2 ?_
      ext i
      have := congrFun h i
      simpa using this
    exact hM (eq_one_of_two_fixed M hu.1 hv.1 hu.2 hv.2 h1 h2)

lemma fixSet_countable (M : SO3) (hM : M.1 ≠ 1) : (fixSet M).Countable := by
  obtain ⟨a, ha⟩ := fixSet_subset_pair M hM
  exact Set.Countable.mono ha ((Set.countable_singleton (-a)).insert a)

/-- The exceptional (countable) set of points of the sphere which are fixed by some nontrivial
element of the free group of rotations. -/
def badSet : Set E := {v ∈ sph | ∃ w : FreeGroup Bool, w ≠ 1 ∧ toPerm (rho w) v = v}

lemma rho_ne_one {w : FreeGroup Bool} (hw : w ≠ 1) : (rho w).1 ≠ 1 := by
  intro h
  exact hw (rho_injective (by
    apply Subtype.ext
    rw [h]
    rfl))

lemma badSet_countable : badSet.Countable := by
  have hsub : badSet ⊆ ⋃ (w : {w : FreeGroup Bool // w ≠ 1}), fixSet (rho w.1) := by
    rintro v ⟨hv, w, hw, hfix⟩
    exact Set.mem_iUnion.2 ⟨⟨w, hw⟩, ⟨hv, hfix⟩⟩
  refine Set.Countable.mono hsub ?_
  exact Set.countable_iUnion (fun w => fixSet_countable _ (rho_ne_one w.2))

lemma sph_invariant (M : SO3) {v : E} (hv : v ∈ sph) : toPerm M v ∈ sph := by
  have : (toPerm M v).ofLp = M.1 *ᵥ v.ofLp := rfl
  show (toPerm M v).ofLp ⬝ᵥ (toPerm M v).ofLp = 1
  rw [this, dotProduct_mulVec_self]
  exact hv

/-- **The Hausdorff paradox.** There is a countable subset `D` of the unit sphere such that the
complement of `D` in the sphere admits a paradoxical decomposition using rotations. -/
theorem hausdorff_paradox :
    ∃ D : Set E, D.Countable ∧ D ⊆ sph ∧ IsParadoxical SO3 (sph \ D) := by
  classical
  set psi : FreeGroup Bool →* SO3 := rho with hpsi
  letI : MulAction (FreeGroup Bool) E := MulAction.compHom E psi
  have hsmul : ∀ (w : FreeGroup Bool) (v : E), w • v = toPerm (rho w) v := fun w v => rfl
  refine ⟨badSet, badSet_countable, fun v hv => hv.1, ?_⟩
  have hpar : IsParadoxical (FreeGroup Bool) (sph \ badSet) := by
    refine isParadoxical_of_freeAction (H := FreeGroup Bool) (sph \ badSet) ?_ ?_
      FreeGroupParadox.freeGroup_isParadoxical
    · -- invariance
      rintro w v ⟨hv, hbad⟩
      refine ⟨by rw [hsmul]; exact sph_invariant _ hv, ?_⟩
      rintro ⟨-, u, hu, hufix⟩
      refine hbad ⟨hv, w⁻¹ * u * w, ?_, ?_⟩
      · intro hcon
        apply hu
        have huw : u = w * (w⁻¹ * u * w) * w⁻¹ := by group
        rw [huw, hcon]
        group
      · have h1 : toPerm (rho (w⁻¹ * u * w)) v
            = toPerm (rho w⁻¹) (toPerm (rho u) (toPerm (rho w) v)) := by
          rw [map_mul, map_mul, toPerm_mul, toPerm_mul]
        rw [hsmul] at hufix
        rw [h1, hufix, ← toPerm_mul, ← map_mul, inv_mul_cancel, map_one, toPerm_one]
    · -- freeness
      rintro w v ⟨hv, hbad⟩ hfix
      by_contra hw
      exact hbad ⟨hv, w, hw, by rw [← hsmul]; exact hfix⟩
  exact hpar.of_hom psi (fun h x => rfl)

/-! ## Absorbing the countable set: the whole sphere is paradoxical -/

/-- The north pole of the unit sphere. -/
noncomputable def e3 : E := WithLp.toLp 2 ![0, 0, 1]

lemma mem_pair_iff {x : E} : x ∈ ({e3, -e3} : Set E) ↔ x = e3 ∨ x = -e3 := by simp

/-- A point of the sphere lying on the `z`-axis is one of the two poles. -/
lemma eq_pole_of_axis {x : E} (hx : x ∈ sph) (h : x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 = 0) :
    x = e3 ∨ x = -e3 := by
  have h0 : x.ofLp 0 = 0 := by nlinarith [sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1)]
  have h1 : x.ofLp 1 = 0 := by nlinarith [sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1)]
  have hs : x.ofLp 0 * x.ofLp 0 + x.ofLp 1 * x.ofLp 1 + x.ofLp 2 * x.ofLp 2 = 1 := by
    simpa [sph, dotProduct, Fin.sum_univ_three] using hx
  have h2 : x.ofLp 2 = 1 ∨ x.ofLp 2 = -1 := by
    have hz : (x.ofLp 2 - 1) * (x.ofLp 2 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.1 hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases h2 with h2 | h2
  · refine Or.inl (PiLp.ext (fun i => ?_))
    fin_cases i <;> simp [e3, h0, h1, h2]
  · refine Or.inr (PiLp.ext (fun i => ?_))
    fin_cases i <;> simp [e3, h0, h1, h2]

lemma axis_ne_zero_of_ne_pole {x : E} (hx : x ∈ sph) (h1 : x ≠ e3) (h2 : x ≠ -e3) :
    x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 ≠ 0 := by
  intro h
  rcases eq_pole_of_axis hx h with h' | h'
  exacts [h1 h', h2 h']

lemma pole_off_xaxis {x : E} (hx : x = e3 ∨ x = -e3) : x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 ≠ 0 := by
  rcases hx with rfl | rfl <;> simp [e3]

lemma so3_smul (M : SO3) (x : E) : M • x = toPerm M x := rfl

/-- **Absorption of a countable set.** For any countable subset `D` of the unit sphere, the
sphere is equidecomposable with the sphere minus `D`. -/
lemma sph_equidecomp_sdiff (D : Set E) (hD : D.Countable) (hDsub : D ⊆ sph) :
    IsEquidecomposable SO3 sph (sph \ D) := by
  classical
  set P : Set E := {e3, -e3} with hP
  set D₁ : Set E := D \ P with hD1
  set D₂ : Set E := D ∩ P with hD2
  have hD1c : D₁.Countable := hD.mono Set.diff_subset
  have hD2c : D₂.Countable := hD.mono Set.inter_subset_left
  have hc1 : ∀ x ∈ D₁, ∀ y : E, {t : ℝ | toPerm (rotZ t) x = y}.Countable := by
    intro x hx y
    have hxP : x ∉ P := hx.2
    rw [hP, mem_pair_iff] at hxP
    push_neg at hxP
    exact countable_bad_Z x y (axis_ne_zero_of_ne_pole (hDsub hx.1) hxP.1 hxP.2)
  obtain ⟨t, ht⟩ := exists_good_angle rotZ rotZ_pow D₁ hD1c D₁ hD1c hc1
  have stage1 : IsEquidecomposable SO3 sph (sph \ D₁) := by
    refine isEquidecomposable_sdiff_of_iterates sph D₁ (rotZ t) ?_ ?_
    · intro n x hx
      rw [so3_smul]
      exact sph_invariant _ (hDsub hx.1)
    · intro n hn x hx
      rw [so3_smul]
      exact ht x hx n hn
  have hc2 : ∀ x ∈ D₂, ∀ y : E, {t : ℝ | toPerm (rotX t) x = y}.Countable := by
    intro x hx y
    have hxP : x ∈ P := hx.2
    rw [hP, mem_pair_iff] at hxP
    exact countable_bad_X x y (pole_off_xaxis hxP)
  obtain ⟨s, hs⟩ := exists_good_angle rotX rotX_pow D₂ hD2c (D₁ ∪ D₂) (hD1c.union hD2c) hc2
  have stage2 : IsEquidecomposable SO3 (sph \ D₁) ((sph \ D₁) \ D₂) := by
    refine isEquidecomposable_sdiff_of_iterates (sph \ D₁) D₂ (rotX s) ?_ ?_
    · intro n x hx
      rw [so3_smul]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [pow_zero, toPerm_one]
        exact ⟨hDsub hx.1, fun hmem => hmem.2 hx.2⟩
      · exact ⟨sph_invariant _ (hDsub hx.1), fun hmem => hs x hx n hn (Or.inl hmem)⟩
    · intro n hn x hx
      rw [so3_smul]
      exact fun hmem => hs x hx n hn (Or.inr hmem)
  have hunion : (sph \ D₁) \ D₂ = sph \ D := by
    ext v
    constructor
    · rintro ⟨⟨hv, h1⟩, h2⟩
      refine ⟨hv, fun hvD => ?_⟩
      by_cases hp : v ∈ P
      · exact h2 ⟨hvD, hp⟩
      · exact h1 ⟨hvD, hp⟩
    · rintro ⟨hv, hvD⟩
      exact ⟨⟨hv, fun h => hvD h.1⟩, fun h => hvD h.1⟩
  rw [← hunion]
  exact stage1.trans stage2

/-- **The unit sphere in `ℝ³` is paradoxical**, using rotations only. -/
theorem sph_isParadoxical : IsParadoxical SO3 sph := by
  obtain ⟨D, hDc, hDsub, hpar⟩ := hausdorff_paradox
  exact IsParadoxical.of_equidecomposable (sph_equidecomp_sdiff D hDc hDsub).symm hpar

/-! ## The cone construction: from the sphere to the punctured ball -/

lemma mem_sph_iff {x : E} : x ∈ sph ↔ ‖x‖ = 1 := by
  constructor
  · intro hx
    rw [norm_eq_sqrt_dotProduct, show x.ofLp ⬝ᵥ x.ofLp = 1 from hx, Real.sqrt_one]
  · intro hx
    have h := congrArg (fun r : ℝ => r ^ 2) (norm_eq_sqrt_dotProduct x)
    simp only at h
    have hnn : 0 ≤ x.ofLp ⬝ᵥ x.ofLp := by
      simp only [dotProduct, Fin.sum_univ_three]
      nlinarith [sq_nonneg (x.ofLp 0), sq_nonneg (x.ofLp 1), sq_nonneg (x.ofLp 2)]
    rw [hx, Real.sq_sqrt hnn] at h
    exact (by simpa [sph] using h.symm)

lemma so3_smul_real (M : SO3) (r : ℝ) (v : E) : M • (r • v) = r • (M • v) := by
  refine PiLp.ext (fun i => ?_)
  show (M.1 *ᵥ (r • v).ofLp) i = (r • (WithLp.toLp 2 (M.1 *ᵥ v.ofLp) : E)).ofLp i
  have h : (r • v).ofLp = r • v.ofLp := rfl
  rw [h, Matrix.mulVec_smul]
  rfl

/-- The cone over a subset of the sphere: all points of the punctured closed unit ball whose
radial projection lies in the set. -/
def cone (S : Set E) : Set E := {v : E | v ≠ 0 ∧ ‖v‖ ≤ 1 ∧ ‖v‖⁻¹ • v ∈ S}

/-- The radial extension of a self-map of the sphere. -/
noncomputable def rad (F : E → E) : E → E := fun v => ‖v‖ • F (‖v‖⁻¹ • v)

lemma norm_rad {F : E → E} {T : Set E} {v : E} (hv : v ≠ 0) (hT : T ⊆ sph)
    (hF : F (‖v‖⁻¹ • v) ∈ T) : ‖rad F v‖ = ‖v‖ := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hnorm : ‖F (‖v‖⁻¹ • v)‖ = 1 := mem_sph_iff.1 (hT hF)
  simp only [rad, norm_smul, hnorm, Real.norm_eq_abs, abs_of_pos hpos, mul_one]

lemma rad_mem_cone {F : E → E} {S T : Set E} {v : E} (hv : v ∈ cone S) (hT : T ⊆ sph)
    (hF : F (‖v‖⁻¹ • v) ∈ T) : rad F v ∈ cone T := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv.1
  have hradnorm : ‖rad F v‖ = ‖v‖ := norm_rad hv.1 hT hF
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    rw [h0, norm_zero] at hradnorm
    exact hpos.ne hradnorm
  · rw [hradnorm]; exact hv.2.1
  · rw [hradnorm]
    simp only [rad, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    exact hF

lemma rad_rad_apply {F G : E → E} {T : Set E} {v : E} (hv : v ≠ 0) (hT : T ⊆ sph)
    (hF : F (‖v‖⁻¹ • v) ∈ T) (hGF : G (F (‖v‖⁻¹ • v)) = ‖v‖⁻¹ • v) : rad G (rad F v) = v := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hradnorm : ‖rad F v‖ = ‖v‖ := norm_rad hv hT hF
  have h1 : ‖rad F v‖⁻¹ • rad F v = F (‖v‖⁻¹ • v) := by
    rw [hradnorm]
    simp only [rad, smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  show ‖rad F v‖ • G (‖rad F v‖⁻¹ • rad F v) = v
  rw [h1, hGF, hradnorm, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

/-- The cone construction turns an equidecomposition of subsets of the sphere into an
equidecomposition of the corresponding cones. -/
lemma cone_equidecomp {A B : Set E} (hA : A ⊆ sph) (hB : B ⊆ sph)
    (h : IsEquidecomposable SO3 A B) : IsEquidecomposable SO3 (cone A) (cone B) := by
  obtain ⟨f, hfs, hft⟩ := h
  obtain ⟨S, hS⟩ := f.isDecompOn'
  have hmapA : ∀ x ∈ A, f.toPartialEquiv x ∈ B := by
    intro x hx
    have := f.toPartialEquiv.map_source (show x ∈ f.source by rw [hfs]; exact hx)
    rwa [hft] at this
  have hmapB : ∀ y ∈ B, f.toPartialEquiv.symm y ∈ A := by
    intro y hy
    have := f.toPartialEquiv.map_target (show y ∈ f.target by rw [hft]; exact hy)
    rwa [hfs] at this
  have hleft : ∀ x ∈ A, f.toPartialEquiv.symm (f.toPartialEquiv x) = x := by
    intro x hx
    exact f.toPartialEquiv.left_inv (show x ∈ f.source by rw [hfs]; exact hx)
  have hright : ∀ y ∈ B, f.toPartialEquiv (f.toPartialEquiv.symm y) = y := by
    intro y hy
    exact f.toPartialEquiv.right_inv (show y ∈ f.target by rw [hft]; exact hy)
  refine ⟨⟨⟨rad (f.toPartialEquiv), rad (f.toPartialEquiv.symm), cone A, cone B,
    ?_, ?_, ?_, ?_⟩, ⟨S, ?_⟩⟩, rfl, rfl⟩
  · intro v hv
    exact rad_mem_cone hv hB (hmapA _ hv.2.2)
  · intro v hv
    exact rad_mem_cone hv hA (hmapB _ hv.2.2)
  · intro v hv
    exact rad_rad_apply hv.1 hB (hmapA _ hv.2.2) (hleft _ hv.2.2)
  · intro v hv
    exact rad_rad_apply hv.1 hA (hmapB _ hv.2.2) (hright _ hv.2.2)
  · intro v hv
    obtain ⟨g, hgS, hg⟩ := hS (‖v‖⁻¹ • v) (by rw [hfs]; exact hv.2.2)
    refine ⟨g, hgS, ?_⟩
    have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv.1
    show ‖v‖ • f.toPartialEquiv (‖v‖⁻¹ • v) = g • v
    rw [hg, so3_smul_real, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

lemma cone_mono {S T : Set E} (h : S ⊆ T) : cone S ⊆ cone T :=
  fun _ hv => ⟨hv.1, hv.2.1, h hv.2.2⟩

lemma cone_disjoint {S T : Set E} (h : Disjoint S T) : Disjoint (cone S) (cone T) := by
  rw [Set.disjoint_left]
  intro v hv hv'
  exact (Set.disjoint_left.1 h hv.2.2) hv'.2.2

lemma cone_sph_eq : cone sph = Metric.closedBall (0 : E) 1 \ {0} := by
  ext v
  constructor
  · rintro ⟨hv0, hv1, -⟩
    exact ⟨by simpa using hv1, hv0⟩
  · rintro ⟨hv1, hv0⟩
    have hv0' : v ≠ 0 := hv0
    have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv0'
    refine ⟨hv0', by simpa using hv1, ?_⟩
    rw [mem_sph_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos),
      inv_mul_cancel₀ hpos.ne']

/-- **The punctured closed unit ball is paradoxical**, using rotations only. -/
theorem punctured_ball_isParadoxical :
    IsParadoxical SO3 (Metric.closedBall (0 : E) 1 \ {0}) := by
  obtain ⟨A₁, A₂, hA₁, hA₂, hdisj, he₁, he₂⟩ := sph_isParadoxical
  rw [← cone_sph_eq]
  exact ⟨cone A₁, cone A₂, cone_mono hA₁, cone_mono hA₂, cone_disjoint hdisj,
    cone_equidecomp (hA₁.trans (subset_refl _)) (subset_refl _) he₁,
    cone_equidecomp (hA₂.trans (subset_refl _)) (subset_refl _) he₂⟩

/-! ## Absorbing the centre of the ball -/

/-- Translation by a vector, as a permutation of `ℝ³`. -/
noncomputable def transPerm (c : E) : Equiv.Perm E := Equiv.addRight c

lemma transPerm_isometry (c : E) : Isometry (transPerm c) := by
  refine Isometry.of_dist_eq (fun x y => ?_)
  simp only [transPerm, Equiv.coe_addRight, dist_eq_norm]
  congr 1
  abel

/-- Translation, as an element of the isometry group. -/
noncomputable def transIsom (c : E) : IsomGroup := ⟨transPerm c, transPerm_isometry c⟩

lemma isom_smul (g : IsomGroup) (x : E) : g • x = (g : Equiv.Perm E) x := rfl

/-- The centre of the rotation used to absorb the origin. -/
noncomputable def cvec : E := WithLp.toLp 2 ![1/2, 0, 0]

/-- A rotation by one radian about the vertical line through `cvec`. -/
noncomputable def shiftRot : IsomGroup := transIsom cvec * toIsom (rotZ 1) * transIsom (-cvec)

lemma shiftRot_pow_smul (n : ℕ) (x : E) :
    (shiftRot ^ n) • x = toPerm (rotZ 1 ^ n) (x - cvec) + cvec := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, one_smul, toPerm_one, sub_add_cancel]
  | succ m ih =>
      rw [pow_succ', SemigroupAction.mul_smul, ih]
      show (shiftRot : Equiv.Perm E) _ = _
      show transPerm cvec (toPerm (rotZ 1) (transPerm (-cvec)
        (toPerm (rotZ 1 ^ m) (x - cvec) + cvec))) = _
      have h1 : transPerm (-cvec) (toPerm (rotZ 1 ^ m) (x - cvec) + cvec)
          = toPerm (rotZ 1 ^ m) (x - cvec) := by
        show (toPerm (rotZ 1 ^ m) (x - cvec) + cvec) + -cvec = _
        rw [add_neg_cancel_right]
      rw [h1, ← toPerm_mul, ← pow_succ']
      rfl

lemma cos_nat_ne_one {n : ℕ} (hn : 1 ≤ n) : Real.cos (n : ℝ) ≠ 1 := by
  intro h
  rw [Real.cos_eq_one_iff] at h
  obtain ⟨k, hk⟩ := h
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at hk
    simp at hk
    exact hn0 hk.symm
  have hpi : Real.pi = (n : ℝ) / (2 * (k : ℝ)) := by
    field_simp
    linarith [hk]
  have hirr : Irrational ((n : ℝ) / (2 * (k : ℝ))) := hpi ▸ irrational_pi
  refine (Rat.not_irrational ((n : ℚ) / (2 * (k : ℚ)))) ?_
  have hcast : (((n : ℚ) / (2 * (k : ℚ)) : ℚ) : ℝ) = (n : ℝ) / (2 * (k : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  exact hirr

lemma shiftRot_orbit_coords (n : ℕ) (i : Fin 3) :
    ((shiftRot ^ n) • (0 : E)).ofLp i =
      ![(1 - Real.cos (n : ℝ)) / 2, -Real.sin (n : ℝ) / 2, 0] i := by
  rw [shiftRot_pow_smul, rotZ_pow]
  have hc : ((0 : E) - cvec).ofLp = ![-(1/2), 0, 0] := by
    funext j
    fin_cases j <;> simp [cvec]
  have hsum : ∀ j : Fin 3, (toPerm (rotZ ((n : ℝ) * 1)) ((0 : E) - cvec) + cvec).ofLp j
      = (toPerm (rotZ ((n : ℝ) * 1)) ((0 : E) - cvec)).ofLp j + cvec.ofLp j := fun j => rfl
  rw [hsum]
  have hrot := rotZ_apply ((n : ℝ) * 1) ((0 : E) - cvec) i
  rw [hrot, hc]
  have hn1 : (n : ℝ) * 1 = (n : ℝ) := mul_one _
  rw [hn1]
  fin_cases i <;> simp [cvec] <;> ring

lemma shiftRot_orbit_mem (n : ℕ) : (shiftRot ^ n) • (0 : E) ∈ Metric.closedBall (0 : E) 1 := by
  set w : E := (shiftRot ^ n) • (0 : E) with hw
  have hdot : w.ofLp ⬝ᵥ w.ofLp = (2 - 2 * Real.cos (n : ℝ)) / 4 := by
    have h0 := shiftRot_orbit_coords n 0
    have h1 := shiftRot_orbit_coords n 1
    have h2 := shiftRot_orbit_coords n 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    simp only [dotProduct, Fin.sum_univ_three, ← hw] at *
    rw [h0, h1, h2]
    nlinarith [Real.sin_sq_add_cos_sq (n : ℝ)]
  have hle : w.ofLp ⬝ᵥ w.ofLp ≤ 1 := by
    rw [hdot]
    nlinarith [Real.neg_one_le_cos (n : ℝ)]
  rw [mem_closedBall_zero_iff, norm_eq_sqrt_dotProduct]
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_le_sqrt hle

lemma shiftRot_orbit_ne_zero {n : ℕ} (hn : 1 ≤ n) : (shiftRot ^ n) • (0 : E) ≠ 0 := by
  intro h
  have h0 := shiftRot_orbit_coords n 0
  rw [h] at h0
  simp only [Matrix.cons_val_zero] at h0
  have : Real.cos (n : ℝ) = 1 := by
    have hz : (0 : E).ofLp 0 = 0 := rfl
    rw [hz] at h0
    linarith [h0]
  exact cos_nat_ne_one hn this

/-- The closed unit ball is equidecomposable with the ball minus its centre. -/
theorem ball_equidecomp_punctured :
    IsEquidecomposable IsomGroup (Metric.closedBall (0 : E) 1)
      (Metric.closedBall (0 : E) 1 \ {0}) := by
  refine isEquidecomposable_sdiff_of_iterates _ {0} shiftRot ?_ ?_
  · intro n x hx
    rw [show x = 0 from hx]
    exact shiftRot_orbit_mem n
  · intro n hn x hx
    rw [show x = 0 from hx]
    intro hmem
    exact shiftRot_orbit_ne_zero hn hmem

/-- **The closed unit ball in `ℝ³` is paradoxical.** -/
theorem ball_isParadoxical : IsParadoxical IsomGroup (Metric.closedBall (0 : E) 1) :=
  IsParadoxical.of_equidecomposable ball_equidecomp_punctured.symm
    (punctured_ball_isParadoxical.of_hom toIsom (fun _ _ => rfl))

end Sphere

/-- **The Banach–Tarski paradox.**  The closed unit ball of `ℝ³` admits a paradoxical
decomposition: it contains two disjoint subsets, each of which is equidecomposable, using
finitely many pieces moved by isometries of `ℝ³`, with the whole ball. -/
theorem Banach_Tarski :
    IsParadoxical Sphere.IsomGroup (Metric.closedBall (0 : Sphere.E) 1) :=
  Sphere.ball_isParadoxical

end Frontier


import Mathlib

/-!
# Banach Tarski: equidecomposability and paradoxical decompositions

The general framework: equidecomposability, paradoxicality, the paradoxical decomposition of
the free group of rank two, the transfer principle, and the absorption (Hilbert hotel) lemma.
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

namespace Frontier

open Set Function

/-! ## Equidecomposability and paradoxical decompositions

We use Mathlib's `Equidecomp X G` (`Mathlib/Algebra/Group/Action/Equidecomp.lean`), the type of
partial bijections of `X` which are obtained by cutting the source into finitely many pieces and
applying a single element of `G` to each piece.
-/

/-- Two subsets `A B` of a `G`-space `X` are *equidecomposable* if there is an equidecomposition
of `X` with source `A` and target `B`. -/
def IsEquidecomposable (G : Type*) {X : Type*} [Group G] [MulAction G X] (A B : Set X) : Prop :=
  ∃ f : Equidecomp X G, f.source = A ∧ f.target = B

/-- A subset `A` of a `G`-space `X` is *paradoxical* if it contains two disjoint subsets, each of
which is equidecomposable with all of `A`. -/
def IsParadoxical (G : Type*) {X : Type*} [Group G] [MulAction G X] (A : Set X) : Prop :=
  ∃ A₁ A₂ : Set X, A₁ ⊆ A ∧ A₂ ⊆ A ∧ Disjoint A₁ A₂ ∧
    IsEquidecomposable G A₁ A ∧ IsEquidecomposable G A₂ A

/-! ## The free group of rank 2 is paradoxical -/

namespace FreeGroupParadox

open FreeGroup

/-- The free group of rank two, on the generating set `Bool`. -/
abbrev FG : Type := FreeGroup Bool

/-- The one-letter element of the free group determined by the letter `x`. -/
def lt (x : Bool × Bool) : FG := FreeGroup.mk [x]

/-- The inverse letter of `x`. -/
def flip (x : Bool × Bool) : Bool × Bool := (x.1, !x.2)

/-- The set of elements of the free group whose reduced word starts with the letter `x`. -/
def W (x : Bool × Bool) : Set FG := {w : FG | w.toWord.head? = some x}

@[simp] lemma flip_flip (x : Bool × Bool) : flip (flip x) = x := by
  simp [flip]

lemma flip_ne (x : Bool × Bool) : flip x ≠ x := by
  simp [flip, Prod.ext_iff]

lemma toWord_lt (x : Bool × Bool) : (lt x).toWord = [x] := by
  simp [lt, FreeGroup.toWord_mk]

lemma lt_mul_lt (x : Bool × Bool) : lt (flip x) * lt x = 1 := by
  rw [lt, lt, FreeGroup.mul_mk, show (1 : FG) = FreeGroup.mk [] from FreeGroup.one_eq_mk]
  exact FreeGroup.reduce.exact (by simp [flip, FreeGroup.reduce.cons])

/-- Left multiplication by a letter `x`, when no cancellation occurs. -/
lemma toWord_lt_mul {x : Bool × Bool} {w : FG} (h : w.toWord.head? ≠ some (flip x)) :
    (lt x * w).toWord = x :: w.toWord := by
  conv_lhs => rw [lt, ← FreeGroup.mk_toWord (x := w)]
  rw [FreeGroup.mul_mk, FreeGroup.toWord_mk, List.singleton_append, FreeGroup.reduce.cons,
    FreeGroup.reduce_toWord]
  cases hw : w.toWord with
  | nil => simp
  | cons hd tl =>
      rw [hw] at h
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at h
      have hx : ¬ (x.1 = hd.1 ∧ x.2 = !hd.2) := by
        rintro ⟨h1, h2⟩
        exact h (by cases hd; simp_all [flip])
      simp [hx]

/-- The reduced word of an element determines a factorisation into its first letter and the rest. -/
lemma eq_lt_mul {x : Bool × Bool} {rest : List (Bool × Bool)} {w : FG} (hw : w.toWord = x :: rest) :
    w = lt x * FreeGroup.mk rest ∧ (FreeGroup.mk rest).toWord = rest := by
  have hred : FreeGroup.IsReduced (x :: rest) := by
    rw [← hw]; exact FreeGroup.isReduced_toWord
  have hrest : FreeGroup.IsReduced rest := hred.infix (List.infix_cons (List.infix_refl rest))
  have h2 : (FreeGroup.mk rest).toWord = rest := by
    rw [FreeGroup.toWord_mk, hrest.reduce_eq]
  refine ⟨?_, h2⟩
  conv_lhs => rw [← FreeGroup.mk_toWord (x := w), hw]
  rw [lt, FreeGroup.mul_mk, List.singleton_append]

/-- Cancellation: multiplying on the left by the inverse of the first letter. -/
lemma lt_flip_mul {x : Bool × Bool} {rest : List (Bool × Bool)} {w : FG}
    (hw : w.toWord = x :: rest) : lt (flip x) * w = FreeGroup.mk rest := by
  obtain ⟨h1, -⟩ := eq_lt_mul hw
  rw [h1, ← mul_assoc, lt_mul_lt, one_mul]

/-- The head letter of a reduced word `x :: rest` cannot be cancelled by the next one. -/
lemma head_ne_of_reduced {x : Bool × Bool} {rest : List (Bool × Bool)} {w : FG}
    (hw : w.toWord = x :: rest) : rest.head? ≠ some (flip x) := by
  have hred : FreeGroup.IsReduced (x :: rest) := by
    rw [← hw]; exact FreeGroup.isReduced_toWord
  cases rest with
  | nil => simp
  | cons hd tl =>
      rw [FreeGroup.isReduced_cons_cons] at hred
      intro hcon
      simp only [List.head?_cons, Option.some.injEq] at hcon
      subst hcon
      have := hred.1 rfl
      simp [flip] at this

/-- For each letter `y`, the set of elements starting with `y` or with `y⁻¹` is
equidecomposable with the whole free group. -/
lemma isEquidecomposable_union (y : Bool × Bool) :
    Frontier.IsEquidecomposable FG (W y ∪ W (flip y)) Set.univ := by
  classical
  refine ⟨⟨⟨fun w => if w.toWord.head? = some y then w else lt y * w,
      fun u => if u.toWord.head? = some y then u else lt (flip y) * u,
      W y ∪ W (flip y), Set.univ, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
  · intro w _; trivial
  · -- map_target
    intro u _
    by_cases hu : u.toWord.head? = some y
    · simp only [hu, if_true]
      exact Or.inl hu
    · simp only [hu, if_false]
      right
      have : u.toWord.head? ≠ some (flip (flip y)) := by rwa [flip_flip]
      show (lt (flip y) * u).toWord.head? = some (flip y)
      rw [toWord_lt_mul this]
      simp
  · -- left_inv
    intro w hw
    by_cases h : w.toWord.head? = some y
    · simp [h]
    · simp only [h, if_false]
      have hw' : w ∈ W (flip y) := hw.resolve_left h
      have hhead : w.toWord.head? = some (flip y) := hw'
      obtain ⟨rest, hrest⟩ : ∃ rest, w.toWord = flip y :: rest := by
        cases hcase : w.toWord with
        | nil => rw [hcase] at hhead; simp at hhead
        | cons hd tl =>
            rw [hcase] at hhead
            simp only [List.head?_cons, Option.some.injEq] at hhead
            exact ⟨tl, by simp [hhead]⟩
      have hcancel : lt y * w = FreeGroup.mk rest := by
        have := lt_flip_mul (x := flip y) hrest
        rwa [flip_flip] at this
      have hrestword : (FreeGroup.mk rest).toWord = rest := (eq_lt_mul hrest).2
      have hhead2 : rest.head? ≠ some y := by
        have := head_ne_of_reduced hrest
        rwa [flip_flip] at this
      rw [hcancel]
      have : (FreeGroup.mk rest).toWord.head? ≠ some y := by rw [hrestword]; exact hhead2
      simp only [this, if_false]
      rw [← hcancel, ← mul_assoc, lt_mul_lt, one_mul]
  · -- right_inv
    intro u _
    by_cases hu : u.toWord.head? = some y
    · simp [hu]
    · simp only [hu, if_false]
      have hne : u.toWord.head? ≠ some (flip (flip y)) := by rwa [flip_flip]
      have hword : (lt (flip y) * u).toWord = flip y :: u.toWord := toWord_lt_mul hne
      have : (lt (flip y) * u).toWord.head? ≠ some y := by
        rw [hword]
        simp only [List.head?_cons, ne_eq, Option.some.injEq]
        exact flip_ne y
      simp only [this, if_false]
      rw [← mul_assoc]
      have : lt y * lt (flip y) = 1 := by
        have := lt_mul_lt (flip y)
        rwa [flip_flip] at this
      rw [this, one_mul]
  · -- isDecompOn
    refine ⟨{1, lt y}, ?_⟩
    intro w _
    by_cases h : w.toWord.head? = some y
    · exact ⟨1, by simp, by simp [h]⟩
    · exact ⟨lt y, by simp, by simp [h]⟩

/-- **The free group of rank two is paradoxical**: it contains two disjoint subsets, each of
which is equidecomposable (using left translations) with the whole group. -/
theorem freeGroup_isParadoxical : Frontier.IsParadoxical FG (Set.univ : Set FG) := by
  refine ⟨W (false, true) ∪ W (false, false), W (true, true) ∪ W (true, false),
    Set.subset_univ _, Set.subset_univ _, ?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro w (hw | hw) (hw' | hw') <;>
      · simp only [W, Set.mem_setOf_eq] at hw hw'
        rw [hw] at hw'
        simp at hw'
  · have := isEquidecomposable_union (false, true)
    simpa [flip] using this
  · have := isEquidecomposable_union (true, true)
    simpa [flip] using this

end FreeGroupParadox

/-! ## Transfer of paradoxical decompositions -/

section Transfer

variable {H X : Type*} [Group H] [MulAction H X]

/-- Equidecomposability can be transported along a group homomorphism which is compatible with
the two actions; in particular from a subgroup to the ambient group. -/
theorem IsEquidecomposable.of_hom {G : Type*} [Group G] [MulAction G X] (psi : H →* G)
    (hpsi : ∀ (h : H) (x : X), psi h • x = h • x) {A B : Set X}
    (h : IsEquidecomposable H A B) : IsEquidecomposable G A B := by
  classical
  obtain ⟨f, hs, ht⟩ := h
  obtain ⟨S, hS⟩ := f.isDecompOn'
  refine ⟨⟨f.toPartialEquiv, ⟨S.image psi, ?_⟩⟩, hs, ht⟩
  intro a ha
  obtain ⟨g, hg, hga⟩ := hS a ha
  exact ⟨psi g, Finset.mem_image_of_mem _ hg, by rw [hpsi, hga]⟩

/-- Paradoxicality can be transported along a group homomorphism compatible with the actions. -/
theorem IsParadoxical.of_hom {G : Type*} [Group G] [MulAction G X] (psi : H →* G)
    (hpsi : ∀ (h : H) (x : X), psi h • x = h • x) {A : Set X}
    (h : IsParadoxical H A) : IsParadoxical G A := by
  obtain ⟨A₁, A₂, h₁, h₂, hd, he₁, he₂⟩ := h
  exact ⟨A₁, A₂, h₁, h₂, hd, he₁.of_hom psi hpsi, he₂.of_hom psi hpsi⟩

/-- **Transfer principle.** If a group `H` acts freely on an invariant set `Y` and `H` is
paradoxical as an `H`-set, then `Y` is paradoxical. -/
theorem isParadoxical_of_freeAction (Y : Set X)
    (hYinv : ∀ (h : H) {x : X}, x ∈ Y → h • x ∈ Y)
    (hfree : ∀ (h : H) {x : X}, x ∈ Y → h • x = x → h = 1)
    (hpar : IsParadoxical H (Set.univ : Set H)) : IsParadoxical H Y := by
  classical
  -- a choice of orbit representatives
  obtain ⟨rep, hrep_ex, hrep_smul⟩ :
      ∃ rep : X → X, (∀ x : X, ∃ h : H, x = h • rep x) ∧ (∀ (h : H) (x : X), rep (h • x) = rep x) := by
    refine ⟨fun x => Quotient.out (Quotient.mk (MulAction.orbitRel H X) x), ?_, ?_⟩
    · intro x
      have h0 : (MulAction.orbitRel H X) (Quotient.out (Quotient.mk (MulAction.orbitRel H X) x)) x :=
        Quotient.mk_out (s := MulAction.orbitRel H X) x
      rw [MulAction.orbitRel_apply] at h0
      obtain ⟨h, hh⟩ := h0
      exact ⟨h⁻¹, by simp [← hh]⟩
    · intro h x
      exact congrArg Quotient.out (Quotient.sound
        (show (MulAction.orbitRel H X) (h • x) x from (MulAction.orbitRel_apply).2 ⟨h, rfl⟩))
  choose elem helem using hrep_ex
  have hrep_eq : ∀ x : X, rep x = (elem x)⁻¹ • x := fun x =>
    eq_inv_smul_iff.mpr (helem x).symm
  have hrep_mem : ∀ {x : X}, x ∈ Y → rep x ∈ Y := by
    intro x hx; rw [hrep_eq]; exact hYinv _ hx
  -- the key equivariance property of the coefficient function `elem`
  have key : ∀ (h : H) {x : X}, x ∈ Y → elem (h • x) = h * elem x := by
    intro h x hx
    have h1 : h • x = elem (h • x) • rep x := by
      conv_lhs => rw [helem (h • x)]
      rw [hrep_smul]
    have h2 : h • x = (h * elem x) • rep x := by
      conv_lhs => rw [helem x]
      rw [mul_smul]
    have h3 : ((elem (h • x))⁻¹ * (h * elem x)) • rep x = rep x := by
      rw [mul_smul, ← h2, inv_smul_eq_iff]
      exact h1
    have h4 : (elem (h • x))⁻¹ * (h * elem x) = 1 := hfree _ (hrep_mem hx) h3
    have h5 := congrArg (fun z => elem (h • x) * z) h4
    simpa [← mul_assoc] using h5.symm
  -- the main construction
  have main : ∀ f : Equidecomp H H, f.target = Set.univ →
      IsEquidecomposable H {x | x ∈ Y ∧ elem x ∈ f.source} Y := by
    intro f hft
    have hmapY : ∀ {x : X}, x ∈ Y → ∀ c : H, c • x ∈ Y := fun hx c => hYinv c hx
    have hsrc : ∀ y : X, f.toPartialEquiv.symm (elem y) ∈ f.source := fun y =>
      f.toPartialEquiv.map_target (by rw [hft]; trivial)
    set F : X → X := fun x => (f (elem x) * (elem x)⁻¹) • x with hF
    set Fi : X → X := fun x => (f.toPartialEquiv.symm (elem x) * (elem x)⁻¹) • x with hFi
    have hFel : ∀ {x : X}, x ∈ Y → elem (F x) = f (elem x) := by
      intro x hx
      have := key (f (elem x) * (elem x)⁻¹) hx
      rw [hF]
      simpa [mul_assoc] using this
    have hFiel : ∀ {y : X}, y ∈ Y → elem (Fi y) = f.toPartialEquiv.symm (elem y) := by
      intro y hy
      have := key (f.toPartialEquiv.symm (elem y) * (elem y)⁻¹) hy
      rw [hFi]
      simpa [mul_assoc] using this
    refine ⟨⟨⟨F, Fi, {x | x ∈ Y ∧ elem x ∈ f.source}, Y, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
    · rintro x ⟨hx, -⟩; exact hmapY hx _
    · intro y hy
      exact ⟨hmapY hy _, by rw [hFiel hy]; exact hsrc y⟩
    · rintro x ⟨hx, hxs⟩
      have h1 : Fi (F x) = (f.toPartialEquiv.symm (elem (F x)) * (elem (F x))⁻¹) • F x := rfl
      rw [h1, hFel hx, f.toPartialEquiv.left_inv hxs, hF]
      simp only [← mul_smul]
      group
      simp
    · intro y hy
      have h1 : F (Fi y) = (f (elem (Fi y)) * (elem (Fi y))⁻¹) • Fi y := rfl
      rw [h1, hFiel hy, f.toPartialEquiv.right_inv (by rw [hft]; trivial), hFi]
      simp only [← mul_smul]
      group
      simp
    · refine ⟨f.witness, ?_⟩
      rintro x ⟨-, hxs⟩
      obtain ⟨g, hg, hgx⟩ := f.isDecompOn (elem x) hxs
      refine ⟨g, hg, ?_⟩
      show F x = g • x
      rw [hF]
      simp only [hgx, smul_eq_mul, mul_inv_cancel_right]
  obtain ⟨A₁, A₂, -, -, hdisj, ⟨f₁, hf₁s, hf₁t⟩, ⟨f₂, hf₂s, hf₂t⟩⟩ := hpar
  refine ⟨{x | x ∈ Y ∧ elem x ∈ f₁.source}, {x | x ∈ Y ∧ elem x ∈ f₂.source},
    fun x hx => hx.1, fun x hx => hx.1, ?_, main f₁ hf₁t, main f₂ hf₂t⟩
  rw [Set.disjoint_left]
  rintro x ⟨-, hx₁⟩ ⟨-, hx₂⟩
  rw [hf₁s] at hx₁
  rw [hf₂s] at hx₂
  exact (Set.disjoint_left.1 hdisj hx₁) hx₂

end Transfer

/-! ## Basic properties of equidecomposability -/

section Algebra

variable {G X : Type*} [Group G] [MulAction G X]

theorem IsEquidecomposable.symm {A B : Set X} (h : IsEquidecomposable G A B) :
    IsEquidecomposable G B A := by
  obtain ⟨f, hs, ht⟩ := h
  exact ⟨f.symm, by simpa using ht, by simpa using hs⟩

theorem IsEquidecomposable.trans {A B C : Set X} (h₁ : IsEquidecomposable G A B)
    (h₂ : IsEquidecomposable G B C) : IsEquidecomposable G A C := by
  obtain ⟨f, hfs, hft⟩ := h₁
  obtain ⟨g, hgs, hgt⟩ := h₂
  refine ⟨f.trans g, ?_, ?_⟩
  · show (f.toPartialEquiv.trans g.toPartialEquiv).source = A
    rw [PartialEquiv.trans_source, hfs]
    apply Set.inter_eq_self_of_subset_left
    intro x hx
    have : f.toPartialEquiv x ∈ f.target := f.toPartialEquiv.map_source (by rw [hfs]; exact hx)
    rw [hft, ← hgs] at this
    exact this
  · show (f.toPartialEquiv.trans g.toPartialEquiv).target = C
    rw [PartialEquiv.trans_target, hgt]
    apply Set.inter_eq_self_of_subset_left
    intro y hy
    have : g.toPartialEquiv.symm y ∈ g.source := g.toPartialEquiv.map_target (by rw [hgt]; exact hy)
    rw [hgs, ← hft] at this
    exact this

/-- The image of a subset under an equidecomposition is equidecomposable with it. -/
theorem IsEquidecomposable.image {A B A₁ : Set X} (h : IsEquidecomposable G A B) (hA₁ : A₁ ⊆ A) :
    ∃ B₁ ⊆ B, IsEquidecomposable G A₁ B₁ ∧
      ∀ A₂ ⊆ A, Disjoint A₁ A₂ → ∃ B₂ ⊆ B, IsEquidecomposable G A₂ B₂ ∧ Disjoint B₁ B₂ := by
  obtain ⟨f, hfs, hft⟩ := h
  have himg : ∀ S : Set X, S ⊆ A → IsEquidecomposable G S (f.toPartialEquiv '' S) ∧
      f.toPartialEquiv '' S ⊆ B := by
    intro S hS
    have hSsub : S ⊆ f.source := by rw [hfs]; exact hS
    refine ⟨⟨f.restr S, Equidecomp.source_restr f hSsub, ?_⟩, ?_⟩
    · show (f.toPartialEquiv.restr S).target = f.toPartialEquiv '' S
      rw [PartialEquiv.restr_target, f.toPartialEquiv.image_eq_target_inter_inv_preimage hSsub]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hft]
      exact f.toPartialEquiv.map_source (hSsub hx)
  obtain ⟨h₁, hb₁⟩ := himg A₁ hA₁
  refine ⟨f.toPartialEquiv '' A₁, hb₁, h₁, ?_⟩
  intro A₂ hA₂ hdisj
  obtain ⟨h₂, hb₂⟩ := himg A₂ hA₂
  refine ⟨f.toPartialEquiv '' A₂, hb₂, h₂, ?_⟩
  rw [Set.disjoint_left]
  rintro y ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, hx₂'⟩
  have hx₁s : x₁ ∈ f.source := by rw [hfs]; exact hA₁ hx₁
  have hx₂s : x₂ ∈ f.source := by rw [hfs]; exact hA₂ hx₂
  have : x₂ = x₁ := by
    have h1 := f.toPartialEquiv.left_inv hx₁s
    have h2 := f.toPartialEquiv.left_inv hx₂s
    rw [← h1, ← h2, hx₂']
  rw [this] at hx₂
  exact (Set.disjoint_left.1 hdisj hx₁) hx₂

/-- Paradoxicality is invariant under equidecomposability. -/
theorem IsParadoxical.of_equidecomposable {A B : Set X} (hAB : IsEquidecomposable G A B)
    (h : IsParadoxical G A) : IsParadoxical G B := by
  obtain ⟨A₁, A₂, hA₁, hA₂, hdisj, he₁, he₂⟩ := h
  obtain ⟨B₁, hB₁, hb₁, hrest⟩ := hAB.image hA₁
  obtain ⟨B₂, hB₂, hb₂, hdisjB⟩ := hrest A₂ hA₂ hdisj
  exact ⟨B₁, B₂, hB₁, hB₂, hdisjB, (hb₁.symm.trans he₁).trans hAB,
    (hb₂.symm.trans he₂).trans hAB⟩

/-- **Absorption lemma** (Hilbert hotel).  If `g` moves a subset `D` of `A` off itself in the
sense that all the iterates `gⁿ • D`, `n ≥ 1`, are disjoint from `D` and stay inside `A`, then
`A` is equidecomposable with `A \ D`. -/
theorem isEquidecomposable_sdiff_of_iterates (A D : Set X) (g : G)
    (hmem : ∀ (n : ℕ) (x : X), x ∈ D → (g ^ n) • x ∈ A)
    (hdisj : ∀ (n : ℕ), 1 ≤ n → ∀ x ∈ D, (g ^ n) • x ∉ D) :
    IsEquidecomposable G A (A \ D) := by
  classical
  set Es : Set X := ⋃ n : ℕ, (fun x => (g ^ n) • x) '' D with hEs
  have hmemE : ∀ y : X, y ∈ Es ↔ ∃ n : ℕ, ∃ x ∈ D, (g ^ n) • x = y := by
    intro y
    simp only [hEs, Set.mem_iUnion, Set.mem_image]
  have hDE : D ⊆ Es := by
    intro x hx
    rw [hmemE]
    exact ⟨0, x, hx, by simp⟩
  have hEA : Es ⊆ A := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    exact hmem n x hx
  have hgE : ∀ y ∈ Es, g • y ∈ Es ∧ g • y ∉ D := by
    intro y hy
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    have hnext : (g ^ (n + 1)) • x = g • (g ^ n) • x := by rw [pow_succ']; exact mul_smul _ _ _
    refine ⟨(hmemE _).2 ⟨n + 1, x, hx, hnext⟩, ?_⟩
    rw [← hnext]
    exact hdisj (n + 1) (by omega) x hx
  have hginv : ∀ y ∈ Es, y ∉ D → g⁻¹ • y ∈ Es := by
    intro y hy hyD
    obtain ⟨n, x, hx, rfl⟩ := (hmemE y).1 hy
    cases n with
    | zero => exact absurd (by simpa using hx) hyD
    | succ m =>
        have hnext : (g ^ (m + 1)) • x = g • (g ^ m) • x := by rw [pow_succ']; exact mul_smul _ _ _
        rw [hnext, inv_smul_smul]
        exact (hmemE _).2 ⟨m, x, hx, rfl⟩
  refine ⟨⟨⟨fun x => if x ∈ Es then g • x else x, fun y => if y ∈ Es then g⁻¹ • y else y,
      A, A \ D, ?_, ?_, ?_, ?_⟩, ?_⟩, rfl, rfl⟩
  · intro x hx
    by_cases hxE : x ∈ Es
    · simp only [hxE, if_true]
      exact ⟨hEA (hgE x hxE).1, (hgE x hxE).2⟩
    · simp only [hxE, if_false]
      exact ⟨hx, fun hxD => hxE (hDE hxD)⟩
  · rintro y ⟨hy, hyD⟩
    by_cases hyE : y ∈ Es
    · simp only [hyE, if_true]
      exact hEA (hginv y hyE hyD)
    · simp only [hyE, if_false]
      exact hy
  · intro x hx
    by_cases hxE : x ∈ Es
    · simp only [hxE, if_true, (hgE x hxE).1, inv_smul_smul]
    · simp only [hxE, if_false]
  · rintro y ⟨hy, hyD⟩
    by_cases hyE : y ∈ Es
    · simp only [hyE, if_true, hginv y hyE hyD, smul_inv_smul]
    · simp only [hyE, if_false]
  · refine ⟨{1, g}, ?_⟩
    intro x _
    by_cases hxE : x ∈ Es
    · exact ⟨g, by simp, by simp [hxE]⟩
    · exact ⟨1, by simp, by simp [hxE]⟩

end Algebra

end Frontier

