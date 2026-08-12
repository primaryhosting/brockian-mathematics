import Brockian.Weyl.DeficiencyODE

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
# Essential self-adjointness of Schrödinger operators via deficiency indices

This file develops, from scratch:

* a minimal framework for (possibly unbounded) operators on a complex Hilbert space,
  given as a linear map `T : D →ₗ[ℂ] H` out of a submodule `D` of `H`, together with
  their graphs, adjoint graphs, symmetry and essential self-adjointness;
* the *basic criterion* of essential self-adjointness: a densely defined symmetric
  operator whose deficiency spaces `ker (T* ∓ i)` are trivial is essentially
  self-adjoint;
* the deficiency ("Weyl limit point") analysis of the second order difference
  equation attached to a discrete Schrödinger operator, and the resulting
  essential self-adjointness of the discrete Schrödinger operator
  `(T u) n = u (n-1) + u (n+1) + V n * u n` on `ℓ²(ℤ, ℂ)`, defined on the
  (dense) span of the standard basis vectors, for an **arbitrary** real potential
  `V : ℤ → ℝ`.

The main theorem
`schrodinger_essentiallySelfAdjoint_of_weakRegularity` is unconditional: no regularity
(or boundedness) hypothesis on the potential is needed, so the classical weak regularity
assumption is discharged. Everything is proved from first principles on top of Mathlib;
in particular the framework for unbounded operators, their adjoints and essential
self-adjointness is built here.
-/

open scoped InnerProductSpace ComplexConjugate

namespace Brockian.Weyl.DeficiencyODE

/-! ## An abstract framework for unbounded operators -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The graph of an operator `T` defined on the submodule `D` of `H`. -/
def opGraph (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Submodule ℂ (H × H) :=
  LinearMap.range (LinearMap.prod D.subtype T)

lemma mem_opGraph {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {p : H × H} :
    p ∈ opGraph D T ↔ ∃ u : D, ((u : H), T u) = p := Iff.rfl

/-- The graph of the adjoint operator `T*`: the pairs `(v, w)` such that
`⟪T u, v⟫ = ⟪u, w⟫` for all `u` in the domain. -/
def adjGraph (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Submodule ℂ (H × H) where
  carrier := {p : H × H | ∀ u : D, ⟪T u, p.1⟫_ℂ = ⟪(u : H), p.2⟫_ℂ}
  add_mem' := by
    intro p q hp hq u
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hp u, hq u]
  zero_mem' := by intro u; simp
  smul_mem' := by
    intro c p hp u
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, hp u]

lemma mem_adjGraph {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {p : H × H} :
    p ∈ adjGraph D T ↔ ∀ u : D, ⟪T u, p.1⟫_ℂ = ⟪(u : H), p.2⟫_ℂ := Iff.rfl

/-- `T` is symmetric. -/
def IsSymmetricOp (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  ∀ u v : D, ⟪T u, (v : H)⟫_ℂ = ⟪(u : H), T v⟫_ℂ

/-- `T` is essentially self-adjoint: it is densely defined and the closure of its graph
coincides with the graph of its adjoint (equivalently, the closure of `T` is
self-adjoint). -/
def IsEssentiallySelfAdjoint (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) : Prop :=
  Dense (D : Set H) ∧ (opGraph D T).topologicalClosure = adjGraph D T

lemma isClosed_adjGraph (D : Submodule ℂ H) (T : D →ₗ[ℂ] H) :
    IsClosed ((adjGraph D T : Submodule ℂ (H × H)) : Set (H × H)) := by
  have h : ((adjGraph D T : Submodule ℂ (H × H)) : Set (H × H))
      = ⋂ u : D, {p : H × H | ⟪T u, p.1⟫_ℂ = ⟪(u : H), p.2⟫_ℂ} := by
    ext p
    simp only [Set.mem_iInter, Set.mem_setOf_eq, SetLike.mem_coe, mem_adjGraph]
  rw [h]
  refine isClosed_iInter fun u => isClosed_eq ?_ ?_
  · exact continuous_const.inner continuous_fst
  · exact continuous_const.inner continuous_snd

lemma opGraph_le_adjGraph {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} (h : IsSymmetricOp D T) :
    opGraph D T ≤ adjGraph D T := by
  rintro p ⟨u, rfl⟩ v
  exact h v u

lemma closure_le_adjGraph {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} (h : IsSymmetricOp D T) :
    (opGraph D T).topologicalClosure ≤ adjGraph D T :=
  Submodule.topologicalClosure_minimal _ (opGraph_le_adjGraph h) (isClosed_adjGraph D T)

lemma inner_self_symm_of_mem_closure {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (h : IsSymmetricOp D T) {p : H × H} (hp : p ∈ (opGraph D T).topologicalClosure) :
    ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ := by
  have hsub : ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H))
      ⊆ {q : H × H | ⟪q.2, q.1⟫_ℂ = ⟪q.1, q.2⟫_ℂ} := by
    rintro q ⟨u, rfl⟩
    exact h u u
  have hclosed : IsClosed {q : H × H | ⟪q.2, q.1⟫_ℂ = ⟪q.1, q.2⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_fst) (continuous_fst.inner continuous_snd)
  have hmin := closure_minimal hsub hclosed
  have hp' : p ∈ closure ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H)) := by
    rw [← Submodule.topologicalClosure_coe]
    exact hp
  exact hmin hp'

/-- If `⟪w, u⟫` is real and `z` is purely imaginary of modulus one, then
`‖w + z • u‖ ^ 2 = ‖w‖ ^ 2 + ‖u‖ ^ 2`. -/
lemma norm_add_smul_sq {u w : H} (h : ⟪w, u⟫_ℂ = ⟪u, w⟫_ℂ) {z : ℂ} (hz : z.re = 0)
    (hz1 : ‖z‖ = 1) : ‖w + z • u‖ ^ 2 = ‖w‖ ^ 2 + ‖u‖ ^ 2 := by
  have him : (⟪w, u⟫_ℂ).im = 0 := by
    have hc : conj (⟪w, u⟫_ℂ) = ⟪w, u⟫_ℂ := by
      rw [inner_conj_symm]
      exact h.symm
    simpa using (Complex.conj_eq_iff_im.mp hc)
  have hzu : ‖z • u‖ = ‖u‖ := by rw [norm_smul, hz1, one_mul]
  have hre : (RCLike.re (z * ⟪w, u⟫_ℂ) : ℝ) = 0 := by
    simp only [RCLike.re_to_complex, Complex.mul_re, hz, him]
    ring
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, hzu, hre]
  ring

/-- A densely defined operator is closable: the only `w` with `(0, w)` in the graph of the
adjoint is `w = 0`. -/
lemma eq_zero_of_mem_adjGraph_zero [CompleteSpace H] {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hdense : Dense (D : Set H)) {w : H} (h : ((0 : H), w) ∈ adjGraph D T) : w = 0 := by
  have h0 : ∀ u : D, ⟪(u : H), w⟫_ℂ = 0 := by
    intro u
    have := h u
    simpa using this.symm
  have hmem : w ∈ Dᗮ := fun u hu => h0 ⟨u, hu⟩
  have hbot : Dᗮ = ⊥ := by
    rw [← Submodule.topologicalClosure_eq_top_iff]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
  simpa [hbot] using hmem

/-- If `T` is symmetric and densely defined, the closure of its graph is again the graph of
an operator. -/
lemma eq_zero_of_mem_closure_zero [CompleteSpace H] {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hdense : Dense (D : Set H)) (hsymm : IsSymmetricOp D T) {w : H}
    (h : ((0 : H), w) ∈ (opGraph D T).topologicalClosure) : w = 0 :=
  eq_zero_of_mem_adjGraph_zero hdense (closure_le_adjGraph hsymm h)

/-- If `T` is symmetric and essentially self-adjoint, then its adjoint is symmetric as
well; that is, the closure of `T` really is a self-adjoint operator. -/
theorem inner_adjGraph_symm {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} (hsymm : IsSymmetricOp D T)
    (h : IsEssentiallySelfAdjoint D T) {p q : H × H} (hp : p ∈ adjGraph D T)
    (hq : q ∈ adjGraph D T) : ⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ := by
  set G : Set (H × H) := ((opGraph D T : Submodule ℂ (H × H)) : Set (H × H)) with hG
  have hpc : p ∈ closure G := by
    rw [hG, ← Submodule.topologicalClosure_coe, h.2]
    exact hp
  have hqc : q ∈ closure G := by
    rw [hG, ← Submodule.topologicalClosure_coe, h.2]
    exact hq
  have hS : IsClosed {r : (H × H) × (H × H) | ⟪r.1.2, r.2.1⟫_ℂ = ⟪r.1.1, r.2.2⟫_ℂ} :=
    isClosed_eq (Continuous.inner continuous_fst.snd continuous_snd.fst)
      (Continuous.inner continuous_fst.fst continuous_snd.snd)
  have hsub : G ×ˢ G ⊆ {r : (H × H) × (H × H) | ⟪r.1.2, r.2.1⟫_ℂ = ⟪r.1.1, r.2.2⟫_ℂ} := by
    rintro ⟨a, b⟩ ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
    exact hsymm u v
  have hmem : ((p, q) : (H × H) × (H × H)) ∈ closure (G ×ˢ G) := by
    rw [closure_prod_eq]
    exact ⟨hpc, hqc⟩
  exact closure_minimal hsub hS hmem

/-- The linear map `(u, w) ↦ w + z • u` on `H × H`. -/
def shiftMap (z : ℂ) : (H × H) →ₗ[ℂ] H where
  toFun p := p.2 + z • p.1
  map_add' p q := by simp only [Prod.fst_add, Prod.snd_add, smul_add]; abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_add, smul_comm c z]

@[simp] lemma shiftMap_apply (z : ℂ) (p : H × H) : shiftMap z p = p.2 + z • p.1 := rfl

lemma lipschitz_shiftMap (z : ℂ) : LipschitzWith (1 + ‖z‖₊) (shiftMap (H := H) z) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, shiftMap_apply]
  have h1 : ‖(p - q).2‖ ≤ ‖p - q‖ := le_max_right _ _
  have h2 : ‖(p - q).1‖ ≤ ‖p - q‖ := le_max_left _ _
  calc ‖(p - q).2 + z • (p - q).1‖ ≤ ‖(p - q).2‖ + ‖z‖ * ‖(p - q).1‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul]
      _ ≤ ‖p - q‖ + ‖z‖ * ‖p - q‖ := by gcongr
      _ = ((1 + ‖z‖₊ : NNReal) : ℝ) * ‖p - q‖ := by push_cast; ring

private lemma sqrt_le_aux (a b : ℝ) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith

/-- Vectors orthogonal to the range of `T + z` are deficiency vectors. -/
lemma mem_adjGraph_of_orthogonal {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ} (hz : z.re = 0)
    {y : H} (hy : ∀ u : D, ⟪T u + z • (u : H), y⟫_ℂ = 0) : (y, z • y) ∈ adjGraph D T := by
  intro u
  have h := hy u
  rw [inner_add_left, inner_smul_left] at h
  have hconj : (starRingEnd ℂ) z = -z := by
    apply Complex.ext <;> simp [hz]
  rw [hconj] at h
  rw [inner_smul_right]
  linear_combination h

variable [CompleteSpace H]

set_option maxHeartbeats 1000000 in
/-- The image of a closed subspace of `H × H` on which the inner product `⟪w, u⟫` is
real, under `(u, w) ↦ w + z • u`, is closed. -/
lemma isClosed_map_shiftMap {z : ℂ} (hz : z.re = 0) (hz1 : ‖z‖ = 1)
    (C : Submodule ℂ (H × H)) (hC : IsClosed (C : Set (H × H)))
    (hsym : ∀ p ∈ C, ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ) :
    IsClosed ((C.map (shiftMap z) : Submodule ℂ H) : Set H) := by
  haveI : CompleteSpace (C : Set (H × H)) := hC.completeSpace_coe
  have key : ∀ p q : C, dist (p : H × H) (q : H × H)
      ≤ 1 * dist (shiftMap z (p : H × H)) (shiftMap z (q : H × H)) := by
    intro p q
    have hmem : ((p : H × H) - (q : H × H)) ∈ C := C.sub_mem p.2 q.2
    have hs := hsym _ hmem
    have hnorm : ‖shiftMap z (p : H × H) - shiftMap z (q : H × H)‖ ^ 2
        = ‖((p : H × H) - (q : H × H)).2‖ ^ 2 + ‖((p : H × H) - (q : H × H)).1‖ ^ 2 := by
      rw [← map_sub, shiftMap_apply]
      exact norm_add_smul_sq hs hz hz1
    rw [dist_eq_norm, dist_eq_norm, one_mul, Prod.norm_def]
    refine max_le (sqrt_le_aux _ _ (norm_nonneg _) ?_) (sqrt_le_aux _ _ (norm_nonneg _) ?_)
    · rw [hnorm]
      nlinarith [norm_nonneg ((p : H × H) - (q : H × H)).2]
    · rw [hnorm]
      nlinarith [norm_nonneg ((p : H × H) - (q : H × H)).1]
  have hanti : AntilipschitzWith 1 (fun p : C => shiftMap z (p : H × H)) :=
    AntilipschitzWith.of_le_mul_dist (by intro x y; simpa using key x y)
  have hcont : UniformContinuous (fun p : C => shiftMap z (p : H × H)) :=
    ((lipschitz_shiftMap z).uniformContinuous).comp uniformContinuous_subtype_val
  have hrange : Set.range (fun p : C => shiftMap z (p : H × H))
      = ((C.map (shiftMap z) : Submodule ℂ H) : Set H) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨(p : H × H), p.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  rw [← hrange]
  exact hanti.isClosed_range hcont

/-- **Basic criterion** for essential self-adjointness: a densely defined symmetric
operator with trivial deficiency spaces is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_deficiency {D : Submodule ℂ H} {T : D →ₗ[ℂ] H}
    (hdense : Dense (D : Set H)) (hsymm : IsSymmetricOp D T)
    (hplus : ∀ v : H, (v, Complex.I • v) ∈ adjGraph D T → v = 0)
    (hminus : ∀ v : H, (v, (-Complex.I) • v) ∈ adjGraph D T → v = 0) :
    IsEssentiallySelfAdjoint D T := by
  classical
  set C := (opGraph D T).topologicalClosure with hCdef
  have hCclosed : IsClosed ((C : Submodule ℂ (H × H)) : Set (H × H)) :=
    (opGraph D T).isClosed_topologicalClosure
  have hCsym : ∀ p ∈ C, ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ := fun p hp =>
    inner_self_symm_of_mem_closure hsymm hp
  have hCadj : C ≤ adjGraph D T := closure_le_adjGraph hsymm
  have hgraph_le_C : opGraph D T ≤ C := Submodule.le_topologicalClosure _
  -- the range of `T + i` is all of `H`
  have hsurj : ∀ z : ℂ, z.re = 0 → ‖z‖ = 1 →
      (∀ v : H, (v, z • v) ∈ adjGraph D T → v = 0) →
      C.map (shiftMap z) = ⊤ := by
    intro z hz hz1 hker
    have hclosed := isClosed_map_shiftMap hz hz1 C hCclosed hCsym
    have horth : (C.map (shiftMap z))ᗮ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      refine hker y (mem_adjGraph_of_orthogonal hz ?_)
      intro u
      have hmem : (shiftMap z) ((u : H), T u) ∈ C.map (shiftMap z) :=
        ⟨((u : H), T u), hgraph_le_C ⟨u, rfl⟩, rfl⟩
      have h0 := hy _ hmem
      rw [shiftMap_apply] at h0
      exact h0
    have hclosure : (C.map (shiftMap z)).topologicalClosure
        = C.map (shiftMap z) :=
      IsClosed.submodule_topologicalClosure_eq hclosed
    have := Submodule.topologicalClosure_eq_top_iff.mpr horth
    rwa [hclosure] at this
  have hplusTop := hsurj Complex.I (by simp) (by simp) hplus
  refine ⟨hdense, le_antisymm hCadj ?_⟩
  intro p hp
  obtain ⟨v, w⟩ := p
  -- solve `(T̄ + i) u = w + i v`
  have hmem : w + Complex.I • v ∈ C.map (shiftMap Complex.I) := by
    rw [hplusTop]; trivial
  obtain ⟨q, hqC, hq⟩ := hmem
  have hdiff : ((v, w) - q) ∈ adjGraph D T := Submodule.sub_mem _ hp (hCadj hqC)
  have hz : ((v, w) - q).2 = (-Complex.I) • ((v, w) - q).1 := by
    have : q.2 + Complex.I • q.1 = w + Complex.I • v := hq
    have h2 : (w - q.2) = -(Complex.I • (v - q.1)) := by
      rw [smul_sub]
      linear_combination (norm := module) -this
    simpa [Prod.fst_sub, Prod.snd_sub, neg_smul] using h2
  have hzero : ((v, w) - q).1 = 0 := by
    refine hminus _ ?_
    have : ((v, w) - q) = (((v, w) - q).1, (-Complex.I) • ((v, w) - q).1) := by
      rw [← hz]
    rwa [this] at hdiff
  have hv : v = q.1 := by
    have h0 : v - q.1 = 0 := by simpa [Prod.fst_sub] using hzero
    exact sub_eq_zero.mp h0
  have hw : w = q.2 := by
    have h1 := hz
    rw [hzero] at h1
    simp only [Prod.snd_sub, smul_zero] at h1
    exact sub_eq_zero.mp h1
  have hpq : (v, w) = q := Prod.ext hv hw
  rw [hpq]
  exact hqC

end Abstract

/-! ## The deficiency equation and the Weyl limit point argument -/

section DifferenceEquation

open Filter Topology

/-- The Wronskian of an `ℓ²` solution of the deficiency equation against its complex
conjugate. -/
def wronskian (c : ℤ → ℂ) (n : ℤ) : ℂ := c (n + 1) * conj (c n) - conj (c (n + 1)) * c n

/-- The Wronskian increment identity: for a solution of `c (n-1) + c (n+1) + V n c n = z c n`
the Wronskian increases by `(z - conj z) |c n|²`. -/
lemma wronskian_diff {V : ℤ → ℝ} {z : ℂ} {c : ℤ → ℂ}
    (h : ∀ n, c (n - 1) + c (n + 1) + (V n : ℂ) * c n = z * c n) (n : ℤ) :
    wronskian c n - wronskian c (n - 1) = (z - conj z) * (c n * conj (c n)) := by
  have hc : conj (c (n - 1)) + conj (c (n + 1)) + (V n : ℂ) * conj (c n)
      = conj z * conj (c n) := by
    have := congrArg (starRingEnd ℂ) (h n)
    simpa [map_add, map_mul, Complex.conj_ofReal] using this
  have hn : n - 1 + 1 = n := by ring
  simp only [wronskian, hn]
  linear_combination conj (c n) * h n - c n * hc

/-- **Weyl limit point argument.** A solution of the second order difference equation
`c (n-1) + c (n+1) + V n * c n = z * c n` with non-real `z` which tends to `0` at both
ends of `ℤ` vanishes identically. -/
theorem eq_zero_of_l2_solution {V : ℤ → ℝ} {z : ℂ} (hz : z.im ≠ 0) {c : ℤ → ℂ}
    (hT : Tendsto c atTop (𝓝 0)) (hB : Tendsto c atBot (𝓝 0))
    (h : ∀ n, c (n - 1) + c (n + 1) + (V n : ℂ) * c n = z * c n) :
    ∀ n, c n = 0 := by
  have hnormsq : ∀ w : ℂ, ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
    intro w; rw [Complex.sq_norm]; simp [Complex.normSq_apply]
  set t : ℤ → ℝ := fun n => (wronskian c n).im / (2 * z.im) with ht
  have h2 : (2 : ℝ) * z.im ≠ 0 := by simpa using hz
  have hstep : ∀ n, t n = t (n - 1) + ‖c n‖ ^ 2 := by
    intro n
    have hd := wronskian_diff (V := V) h n
    have him : (wronskian c n).im - (wronskian c (n - 1)).im
        = 2 * z.im * ‖c n‖ ^ 2 := by
      have hh : ((wronskian c n - wronskian c (n - 1)) : ℂ).im
          = ((z - conj z) * (c n * conj (c n))).im := by rw [hd]
      rw [hnormsq]
      simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, Complex.sub_re] at hh ⊢
      linarith [hh]
    show (wronskian c n).im / (2 * z.im)
        = (wronskian c (n - 1)).im / (2 * z.im) + ‖c n‖ ^ 2
    field_simp
    linarith [him]
  have hmono : Monotone t := by
    refine monotone_int_of_le_succ fun n => ?_
    have hs := hstep (n + 1)
    simp only [add_sub_cancel_right] at hs
    nlinarith [sq_nonneg ‖c (n + 1)‖]
  have hconj : Tendsto (fun n => conj (c n)) atTop (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hT
  have hconjB : Tendsto (fun n => conj (c n)) atBot (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hB
  have hshiftT : Tendsto (fun n : ℤ => c (n + 1)) atTop (𝓝 0) :=
    hT.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have hshiftB : Tendsto (fun n : ℤ => c (n + 1)) atBot (𝓝 0) :=
    hB.comp (tendsto_atBot_add_const_right _ 1 tendsto_id)
  have hshiftconjT : Tendsto (fun n : ℤ => conj (c (n + 1))) atTop (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hshiftT
  have hshiftconjB : Tendsto (fun n : ℤ => conj (c (n + 1))) atBot (𝓝 0) := by
    simpa using (Complex.continuous_conj.tendsto (0 : ℂ)).comp hshiftB
  have hWT : Tendsto (fun n => wronskian c n) atTop (𝓝 0) := by
    simpa [wronskian] using (hshiftT.mul hconj).sub (hshiftconjT.mul hT)
  have hWB : Tendsto (fun n => wronskian c n) atBot (𝓝 0) := by
    simpa [wronskian] using (hshiftB.mul hconjB).sub (hshiftconjB.mul hB)
  have htT : Tendsto t atTop (𝓝 0) := by
    have := (Complex.continuous_im.tendsto (0 : ℂ)).comp hWT
    simpa [ht] using this.div_const (2 * z.im)
  have htB : Tendsto t atBot (𝓝 0) := by
    have := (Complex.continuous_im.tendsto (0 : ℂ)).comp hWB
    simpa [ht] using this.div_const (2 * z.im)
  have hzero : ∀ n, t n = 0 := by
    intro n
    have hle : t n ≤ 0 := ge_of_tendsto htT (by
      filter_upwards [eventually_ge_atTop n] with m hm using hmono hm)
    have hge : (0 : ℝ) ≤ t n := le_of_tendsto htB (by
      filter_upwards [eventually_le_atBot n] with m hm using hmono hm)
    linarith
  intro n
  have hs := hstep n
  rw [hzero n, hzero (n - 1)] at hs
  have hn0 : ‖c n‖ = 0 := by nlinarith [norm_nonneg (c n)]
  simpa using hn0

end DifferenceEquation

/-! ## The discrete Schrödinger operator -/

section Schrodinger

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The domain of the discrete Schrödinger operator: the (dense) span of the basis
vectors, i.e. the finitely supported vectors. -/
@[reducible] def finiteSpan (b : HilbertBasis ℤ ℂ H) : Submodule ℂ H :=
  Submodule.span ℂ (Set.range (b : ℤ → H))

lemma basis_mem (b : HilbertBasis ℤ ℂ H) (n : ℤ) : (b n) ∈ finiteSpan b :=
  Submodule.subset_span (Set.mem_range_self n)

/-- The discrete Schrödinger (Jacobi) operator with potential `V`, acting on the
finitely supported vectors by `b n ↦ b (n-1) + b (n+1) + V n • b n`. -/
noncomputable def schrodingerOp (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) :
    (finiteSpan b) →ₗ[ℂ] H :=
  (Finsupp.linearCombination ℂ (fun n : ℤ => b (n - 1) + b (n + 1) + (V n : ℂ) • b n)).comp
    (b.orthonormal.linearIndependent.repr)

@[simp] lemma schrodingerOp_basis (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) (n : ℤ) :
    schrodingerOp V b ⟨b n, basis_mem b n⟩ = b (n - 1) + b (n + 1) + (V n : ℂ) • b n := by
  have hrepr : b.orthonormal.linearIndependent.repr ⟨b n, basis_mem b n⟩
      = Finsupp.single n 1 := by
    apply LinearIndependent.repr_eq
    rw [Finsupp.linearCombination_single, one_smul]
  rw [schrodingerOp, LinearMap.comp_apply, hrepr, Finsupp.linearCombination_single, one_smul]

lemma schrodingerOp_isSymmetric (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) :
    IsSymmetricOp (finiteSpan b) (schrodingerOp V b) := by
  have hkey : ∀ i j : ℤ, ⟪b i, b j⟫_ℂ = if i = j then (1 : ℂ) else 0 :=
    fun i j => orthonormal_iff_ite.mp b.orthonormal i j
  have main : ∀ (x : H) (hx : x ∈ finiteSpan b) (y : H) (hy : y ∈ finiteSpan b),
      ⟪schrodingerOp V b ⟨x, hx⟩, y⟫_ℂ = ⟪x, schrodingerOp V b ⟨y, hy⟩⟫_ℂ := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hxs =>
        obtain ⟨n, rfl⟩ := hxs
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hys =>
            obtain ⟨m, rfl⟩ := hys
            rw [schrodingerOp_basis, schrodingerOp_basis]
            simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hkey,
              Complex.conj_ofReal, show (n = m - 1) ↔ (n + 1 = m) by omega,
              show (n = m + 1) ↔ (n - 1 = m) by omega]
            by_cases hnm : n = m
            · subst hnm; simp
            · simp [hnm]; ring
        | zero =>
            rw [show (⟨0, Submodule.zero_mem _⟩ : finiteSpan b) = 0 from rfl, map_zero,
              inner_zero_right]
            simp
        | add y1 y2 h1 h2 ih1 ih2 =>
            rw [show (⟨y1 + y2, Submodule.add_mem _ h1 h2⟩ : finiteSpan b)
                = ⟨y1, h1⟩ + ⟨y2, h2⟩ from rfl, map_add, inner_add_right, inner_add_right,
              ih1, ih2]
        | smul c y hy ih =>
            rw [show (⟨c • y, Submodule.smul_mem _ c hy⟩ : finiteSpan b) = c • ⟨y, hy⟩ from rfl,
              map_smul, inner_smul_right, inner_smul_right, ih]
    | zero =>
        intro y hy
        rw [show (⟨0, Submodule.zero_mem _⟩ : finiteSpan b) = 0 from rfl, map_zero]
        simp
    | add x1 x2 h1 h2 ih1 ih2 =>
        intro y hy
        rw [show (⟨x1 + x2, Submodule.add_mem _ h1 h2⟩ : finiteSpan b)
            = ⟨x1, h1⟩ + ⟨x2, h2⟩ from rfl, map_add, inner_add_left, inner_add_left,
          ih1 y hy, ih2 y hy]
    | smul c x hx ih =>
        intro y hy
        rw [show (⟨c • x, Submodule.smul_mem _ c hx⟩ : finiteSpan b) = c • ⟨x, hx⟩ from rfl,
          map_smul, inner_smul_left, inner_smul_left, ih y hy]
  intro u v
  exact main (u : H) u.2 (v : H) v.2

/-- Coordinatewise description of the discrete Schrödinger operator: its `n`-th
coefficient is `u (n-1) + u (n+1) + V n * u n`. -/
lemma inner_basis_schrodingerOp (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) (u : finiteSpan b) (n : ℤ) :
    ⟪b n, schrodingerOp V b u⟫_ℂ
      = ⟪b (n - 1), (u : H)⟫_ℂ + ⟪b (n + 1), (u : H)⟫_ℂ + (V n : ℂ) * ⟪b n, (u : H)⟫_ℂ := by
  have h := (schrodingerOp_isSymmetric V b ⟨b n, basis_mem b n⟩ u).symm
  rw [schrodingerOp_basis] at h
  simpa [inner_add_left, inner_smul_left, Complex.conj_ofReal] using h

lemma dense_finiteSpan (b : HilbertBasis ℤ ℂ H) : Dense ((finiteSpan b) : Set H) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

/-- The coefficients of any vector tend to `0` along the cofinite filter. -/
lemma tendsto_inner_basis_cofinite (b : HilbertBasis ℤ ℂ H) (v : H) :
    Tendsto (fun n : ℤ => ⟪b n, v⟫_ℂ) cofinite (𝓝 0) := by
  have hsum : Summable (fun i : ℤ => ⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) := b.summable_inner_mul_inner v v
  have h0 : Tendsto (fun i : ℤ => ⟪v, b i⟫_ℂ * ⟪b i, v⟫_ℂ) cofinite (𝓝 0) :=
    hsum.tendsto_cofinite_zero
  have h1 : Tendsto (fun i : ℤ => ‖⟪b i, v⟫_ℂ‖ ^ 2) cofinite (𝓝 0) := by
    have h := (continuous_norm.tendsto (0 : ℂ)).comp h0
    simp only [Function.comp_def, norm_zero] at h
    refine h.congr fun i => ?_
    have hc : ‖⟪v, b i⟫_ℂ‖ = ‖⟪b i, v⟫_ℂ‖ := by
      rw [← inner_conj_symm (b i) v, Complex.norm_conj]
    rw [norm_mul, hc, sq]
  have h2 : Tendsto (fun i : ℤ => ‖⟪b i, v⟫_ℂ‖) cofinite (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp h1
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h2

/-- A deficiency vector satisfies the deficiency difference equation. -/
lemma deficiency_difference_equation (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) {z : ℂ} {v : H}
    (hv : (v, z • v) ∈ adjGraph (finiteSpan b) (schrodingerOp V b)) (n : ℤ) :
    ⟪b (n - 1), v⟫_ℂ + ⟪b (n + 1), v⟫_ℂ + (V n : ℂ) * ⟪b n, v⟫_ℂ = z * ⟪b n, v⟫_ℂ := by
  have h := hv ⟨b n, basis_mem b n⟩
  rw [schrodingerOp_basis] at h
  simpa [inner_add_left, inner_smul_left, inner_smul_right, Complex.conj_ofReal] using h

/-- The deficiency spaces of the discrete Schrödinger operator are trivial. -/
lemma deficiency_eq_zero (V : ℤ → ℝ) (b : HilbertBasis ℤ ℂ H) {z : ℂ} (hz : z.im ≠ 0) {v : H}
    (hv : (v, z • v) ∈ adjGraph (finiteSpan b) (schrodingerOp V b)) : v = 0 := by
  have hcof := tendsto_inner_basis_cofinite b v
  have hTop : Tendsto (fun n : ℤ => ⟪b n, v⟫_ℂ) atTop (𝓝 0) := by
    refine hcof.mono_left ?_
    rw [Int.cofinite_eq]
    exact le_sup_right
  have hBot : Tendsto (fun n : ℤ => ⟪b n, v⟫_ℂ) atBot (𝓝 0) := by
    refine hcof.mono_left ?_
    rw [Int.cofinite_eq]
    exact le_sup_left
  have hzero := eq_zero_of_l2_solution (V := V) hz hTop hBot
    (deficiency_difference_equation V b hv)
  have hrepr : b.repr v = 0 := by
    ext n
    simp [HilbertBasis.repr_apply_apply, hzero n]
  have := congrArg b.repr.symm hrepr
  simpa using this

/-- **Essential self-adjointness of the discrete Schrödinger operator**, for an arbitrary
real potential. -/
theorem schrodingerOp_essentiallySelfAdjoint [CompleteSpace H] (V : ℤ → ℝ)
    (b : HilbertBasis ℤ ℂ H) :
    IsEssentiallySelfAdjoint (finiteSpan b) (schrodingerOp V b) :=
  isEssentiallySelfAdjoint_of_deficiency (dense_finiteSpan b) (schrodingerOp_isSymmetric V b)
    (fun _ hv => deficiency_eq_zero V b (by simp) hv)
    (fun _ hv => deficiency_eq_zero V b (by simp) hv)

end Schrodinger

/-! ## The discrete Schrödinger operator on `ℓ²(ℤ)` -/

section ell2

/-- The Hilbert space `ℓ²(ℤ, ℂ)`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

/-- The standard Hilbert basis of `ℓ²(ℤ, ℂ)`. -/
noncomputable def stdBasis : HilbertBasis ℤ ℂ L2Z := default

@[simp] lemma stdBasis_apply (n : ℤ) : stdBasis n = lp.single 2 n (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single stdBasis n]
  rfl

@[simp] lemma stdBasis_inner (n : ℤ) (x : L2Z) : ⟪stdBasis n, x⟫_ℂ = x n := by
  rw [← HilbertBasis.repr_apply_apply stdBasis x n]
  rfl

/-- On `ℓ²(ℤ)` the operator really is the discrete Schrödinger operator:
`(T u) n = u (n-1) + u (n+1) + V n * u n`. -/
lemma schrodingerOp_stdBasis_coord (V : ℤ → ℝ) (u : finiteSpan stdBasis) (n : ℤ) :
    (schrodingerOp V stdBasis u : L2Z) n
      = (u : L2Z) (n - 1) + (u : L2Z) (n + 1) + (V n : ℂ) * (u : L2Z) n := by
  have h := inner_basis_schrodingerOp V stdBasis u n
  rwa [stdBasis_inner, stdBasis_inner, stdBasis_inner, stdBasis_inner] at h

/-- **Essential self-adjointness of the discrete Schrödinger operator on `ℓ²(ℤ)`.**

The operator `(T u) n = u (n-1) + u (n+1) + V n * u n`, defined on the dense subspace of
finitely supported sequences, is essentially self-adjoint for *every* real potential
`V : ℤ → ℝ`; in particular no regularity whatsoever has to be assumed on `V`.
The proof goes through the deficiency criterion together with the Weyl limit point
analysis of the deficiency difference equation. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity (V : ℤ → ℝ) :
    IsEssentiallySelfAdjoint (finiteSpan stdBasis) (schrodingerOp V stdBasis) :=
  schrodingerOp_essentiallySelfAdjoint V stdBasis

end ell2

end Brockian.Weyl.DeficiencyODE

