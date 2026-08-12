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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

The first part of this file develops the abstract von Neumann / Weyl deficiency criterion for
essential self-adjointness of a densely defined symmetric operator on a complex Hilbert space.

The second part constructs the minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain
the smooth compactly supported functions, and shows that it is essentially self-adjoint as soon as
the differential equation `-u'' + V u = ± i u` has no nonzero solution in `L²(ℝ)` (understood in
the distributional sense).
-/

namespace Brockian.Weyl

open LinearPMap Complex

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A partially defined operator `T` on a complex inner product space is *symmetric* if
`⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in its domain. -/
def IsSymmetricPMap (T : E →ₗ.[ℂ] E) : Prop :=
  ∀ x y : T.domain, ⟪T x, (y : E)⟫ = ⟪(x : E), T y⟫

/-- The domain of the closure contains the original domain, hence is dense. -/
theorem dense_closure_domain {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E)) :
    Dense (T.closure.domain : Set E) :=
  hT.mono (fun _ hx => T.le_closure.1 hx)

/-- The operator `x ↦ A x + c i x` on the domain of `A`. -/
noncomputable def shiftMap (A : E →ₗ.[ℂ] E) (c : ℝ) : A.domain →ₗ[ℂ] E :=
  A.toFun + ((c : ℂ) * Complex.I) • A.domain.subtype

@[simp] theorem shiftMap_apply (A : E →ₗ.[ℂ] E) (c : ℝ) (x : A.domain) :
    shiftMap A c x = A x + ((c : ℂ) * Complex.I) • (x : E) := rfl

/-- For a symmetric operator, `‖A x + c i x‖² = ‖A x‖² + c²‖x‖²`. -/
theorem norm_shiftMap_sq {A : E →ₗ.[ℂ] E} (hs : IsSymmetricPMap A) (c : ℝ) (x : A.domain) :
    ‖shiftMap A c x‖ ^ 2 = ‖A x‖ ^ 2 + c ^ 2 * ‖(x : E)‖ ^ 2 := by
  have h : ⟪A x, (x : E)⟫ = ⟪(x : E), A x⟫ := hs x x
  rw [shiftMap_apply]
  have h2 : (⟪A x, (x : E)⟫ : ℂ).im = 0 := by
    have h3 : (starRingEnd ℂ) (⟪A x, (x : E)⟫ : ℂ) = ⟪A x, (x : E)⟫ := by
      rw [inner_conj_symm, h]
    rw [Complex.conj_eq_iff_im] at h3
    exact h3
  have h1 : RCLike.re (⟪A x, ((c : ℂ) * Complex.I) • (x : E)⟫ : ℂ) = 0 := by
    rw [inner_smul_right]
    simp [h2]
  have h4 : ‖((c : ℂ) * Complex.I) • (x : E)‖ = |c| * ‖(x : E)‖ := by
    rw [norm_smul]; simp
  rw [@norm_add_sq ℂ, h1, h4, mul_pow, sq_abs]
  ring

end Basic

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

namespace IsSymmetricPMap

variable {T : E →ₗ.[ℂ] E}

theorem le_adjoint (hT : Dense (T.domain : Set E)) (hs : IsSymmetricPMap T) : T ≤ T.adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint hT hs

end IsSymmetricPMap

/-- A densely defined symmetric operator is closable. -/
theorem isClosable_of_isSymmetric {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T) : T.IsClosable :=
  LinearPMap.isClosable_iff_exists_closed_extension.mpr
    ⟨T.adjoint, LinearPMap.adjoint_isClosed hT, hs.le_adjoint hT⟩

omit [CompleteSpace E] in
/-- The closure of an operator is contained in any closed extension. -/
theorem closure_le_of_isClosed {T S : E →ₗ.[ℂ] E} (hTS : T ≤ S) (hS : S.IsClosed) :
    T.closure ≤ S := by
  have hcl : T.IsClosable := hS.isClosable.leIsClosable hTS
  refine LinearPMap.le_of_le_graph ?_
  rw [← hcl.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hTS) hS

/-- The closure of a densely defined symmetric operator is contained in the adjoint. -/
theorem closure_le_adjoint {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T) : T.closure ≤ T.adjoint :=
  closure_le_of_isClosed (hs.le_adjoint hT) (LinearPMap.adjoint_isClosed hT)

/-- The closure of a densely defined symmetric operator is symmetric. -/
theorem isSymmetric_closure {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T) : IsSymmetricPMap T.closure := by
  intro x y
  have hcl : T.IsClosable := isClosable_of_isSymmetric hT hs
  have hle : T.closure ≤ T.adjoint := closure_le_adjoint hT hs
  set w : E := T.adjoint ⟨(y : E), hle.1 y.2⟩ with hwdef
  have hyw : T.closure y = w := hle.2 rfl
  have hclosed : IsClosed {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    apply isClosed_eq <;> fun_prop
  have hsub : (T.graph : Set (E × E)) ⊆ {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    rintro ⟨a, b⟩ hab
    obtain ⟨z, hz⟩ := (T.mem_graph_iff).mp hab
    have h1 : a = (z : E) := hz.1.symm
    have h2 : b = T z := hz.2.symm
    subst h1; subst h2
    show ⟪T z, (y : E)⟫ = ⟪(z : E), w⟫
    have h5 := LinearPMap.adjoint_isFormalAdjoint hT ⟨(y : E), hle.1 y.2⟩ z
    rw [← inner_conj_symm (T z) ((y : E)), ← inner_conj_symm ((z : E)) w]
    exact congrArg _ h5.symm
  have hmem : ((x : E), T.closure x) ∈ (T.graph.topologicalClosure : Set (E × E)) := by
    rw [hcl.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph x
  have hfin : ((x : E), T.closure x) ∈ {p : E × E | ⟪p.2, (y : E)⟫ = ⟪p.1, w⟫} := by
    rw [Submodule.topologicalClosure_coe] at hmem
    exact closure_minimal hsub hclosed hmem
  simpa [hyw] using hfin

set_option maxHeartbeats 1000000 in
/-- The range of `A + c i` is closed when `A` is closed and symmetric and `c ≠ 0`. -/
theorem isClosed_range_shiftMap {A : E →ₗ.[ℂ] E} (hA : A.IsClosed) (hs : IsSymmetricPMap A)
    {c : ℝ} (hc : c ≠ 0) : IsClosed ((LinearMap.range (shiftMap A c) : Submodule ℂ E) : Set E) := by
  haveI : CompleteSpace A.graph := hA.completeSpace_coe
  let Φ : A.graph →ₗ[ℂ] E :=
    { toFun := fun z => (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
      map_add' := by
        intro a b
        simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, smul_add]
        abel
      map_smul' := by
        intro r a
        simp only [Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply,
          smul_add, smul_comm r ((c : ℂ) * Complex.I)] }
  have hΦapply : ∀ z : A.graph, Φ z = (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1 :=
    fun _ => rfl
  have hΦcont : Continuous Φ := by
    show Continuous fun z : A.graph => (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
    fun_prop
  set ΦL : A.graph →L[ℂ] E := ⟨Φ, hΦcont⟩ with hΦL
  have hrange : Set.range ΦL = ((LinearMap.range (shiftMap A c) : Submodule ℂ E) : Set E) := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (A.mem_graph_iff).mp z.2
      refine ⟨x, ?_⟩
      show A x + ((c : ℂ) * Complex.I) • (x : E)
          = (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1
      rw [hx.1, hx.2]
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : E), A x), A.mem_graph x⟩, rfl⟩
  rw [← hrange]
  have hbound : ∀ z : A.graph, ‖z‖ ≤ (max 1 |c|⁻¹) * ‖ΦL z‖ := by
    intro z
    obtain ⟨x, hx⟩ := (A.mem_graph_iff).mp z.2
    have hz1 : (z : E × E).1 = (x : E) := hx.1.symm
    have hz2 : (z : E × E).2 = A x := hx.2.symm
    have hΦz : ΦL z = shiftMap A c x := by
      show (z : E × E).2 + ((c : ℂ) * Complex.I) • (z : E × E).1 = _
      rw [hz1, hz2, shiftMap_apply]
    have hnormsq : ‖ΦL z‖ ^ 2 = ‖A x‖ ^ 2 + c ^ 2 * ‖(x : E)‖ ^ 2 := by
      rw [hΦz]; exact norm_shiftMap_sq hs c x
    have hx1 : ‖(x : E)‖ ≤ |c|⁻¹ * ‖ΦL z‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ (abs_pos.mpr hc)]
      nlinarith [norm_nonneg (ΦL z), norm_nonneg ((x : E)), norm_nonneg (A x), sq_abs c,
        abs_nonneg c]
    have hx2 : ‖A x‖ ≤ ‖ΦL z‖ := by
      nlinarith [norm_nonneg (ΦL z), norm_nonneg (A x), norm_nonneg ((x : E)), sq_nonneg c,
        sq_nonneg (‖(x : E)‖)]
    have hnz : ‖z‖ = max ‖(z : E × E).1‖ ‖(z : E × E).2‖ := by
      rw [← Prod.norm_def]; rfl
    rw [hnz, hz1, hz2]
    have h1 : ‖(x : E)‖ ≤ max 1 |c|⁻¹ * ‖ΦL z‖ := by
      refine hx1.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have h2 : ‖A x‖ ≤ max 1 |c|⁻¹ * ‖ΦL z‖ := by
      refine hx2.trans ?_
      nlinarith [norm_nonneg (ΦL z), le_max_left (1 : ℝ) |c|⁻¹]
    exact max_le h1 h2
  have hK : (Real.toNNReal (max 1 |c|⁻¹) : ℝ) = max 1 |c|⁻¹ :=
    Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  have hanti : AntilipschitzWith (Real.toNNReal (max 1 |c|⁻¹)) ΦL := by
    refine ContinuousLinearMap.antilipschitz_of_bound ΦL ?_
    intro z
    rw [hK]
    exact hbound z
  exact hanti.isClosed_range ΦL.uniformContinuous

/-- If `w` is orthogonal to the range of `T + c i` then `w` is an eigenvector of the adjoint
with eigenvalue `c i`. -/
theorem adjoint_apply_of_mem_orthogonal {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (c : ℝ) {w : E} (hw : ∀ x : T.domain, ⟪w, T x + ((c : ℂ) * Complex.I) • (x : E)⟫ = 0) :
    ∃ hw' : w ∈ T.adjoint.domain, T.adjoint ⟨w, hw'⟩ = ((c : ℂ) * Complex.I) • w := by
  have key : ∀ x : T.domain, ⟪((c : ℂ) * Complex.I) • w, (x : E)⟫ = ⟪w, T x⟫ := by
    intro x
    have h := hw x
    rw [inner_add_right, inner_smul_right] at h
    rw [inner_smul_left]
    have hconj : (starRingEnd ℂ) ((c : ℂ) * Complex.I) = -((c : ℂ) * Complex.I) := by
      simp
    rw [hconj]
    linear_combination -h
  have hw' : w ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists w ⟨((c : ℂ) * Complex.I) • w, key⟩
  exact ⟨hw', LinearPMap.adjoint_apply_eq hT ⟨w, hw'⟩ key⟩

/-- Monotonicity of the adjoint. -/
theorem adjoint_le_adjoint_of_le {T S : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hS : Dense (S.domain : Set E)) (h : T ≤ S) : S.adjoint ≤ T.adjoint := by
  have key : ∀ (u : E) (hu : u ∈ S.adjoint.domain) (x : T.domain),
      ⟪S.adjoint ⟨u, hu⟩, (x : E)⟫ = ⟪u, T x⟫ := by
    intro u hu x
    have h1 : (x : E) ∈ S.domain := h.1 x.2
    have h2 : T x = S ⟨(x : E), h1⟩ := h.2 rfl
    rw [h2]
    exact LinearPMap.adjoint_isFormalAdjoint hS ⟨u, hu⟩ ⟨(x : E), h1⟩
  constructor
  · intro u hu
    exact LinearPMap.mem_adjoint_domain_of_exists u ⟨S.adjoint ⟨u, hu⟩, key u hu⟩
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
    have huv' : u = v := huv
    subst huv'
    exact (LinearPMap.adjoint_apply_eq hT ⟨u, hv⟩ (key u hu)).symm

/-- **Deficiency criterion / basic criterion for essential self-adjointness.**

A densely defined symmetric operator `T` on a complex Hilbert space whose adjoint has no
eigenvector for the eigenvalues `i` and `-i` is essentially self-adjoint: its closure is
self-adjoint. -/
theorem isSelfAdjoint_closure_of_deficiency {T : E →ₗ.[ℂ] E} (hT : Dense (T.domain : Set E))
    (hs : IsSymmetricPMap T)
    (hpos : ∀ u : T.adjoint.domain, T.adjoint u = Complex.I • (u : E) → (u : E) = 0)
    (hneg : ∀ u : T.adjoint.domain, T.adjoint u = -Complex.I • (u : E) → (u : E) = 0) :
    IsSelfAdjoint T.closure := by
  have hAsym : IsSymmetricPMap T.closure := isSymmetric_closure hT hs
  have hAdense : Dense (T.closure.domain : Set E) := dense_closure_domain hT
  have hAclosed : T.closure.IsClosed := (isClosable_of_isSymmetric hT hs).closure_isClosed
  have hAle : T.closure ≤ T.adjoint := closure_le_adjoint hT hs
  -- surjectivity of `closure - i`
  have hrangetop : LinearMap.range (shiftMap T.closure (-1 : ℝ)) = ⊤ := by
    have hclosed := isClosed_range_shiftMap hAclosed hAsym (c := (-1 : ℝ)) (by norm_num)
    haveI : CompleteSpace (LinearMap.range (shiftMap T.closure (-1 : ℝ))) :=
      hclosed.completeSpace_coe
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro w hw
    have hw' : ∀ x : T.domain,
        ⟪w, T x + (((-1 : ℝ) : ℂ) * Complex.I) • (x : E)⟫ = 0 := by
      intro x
      have hx : (x : E) ∈ T.closure.domain := T.le_closure.1 x.2
      have hTx : T x = T.closure ⟨(x : E), hx⟩ := T.le_closure.2 rfl
      have hmem : T.closure ⟨(x : E), hx⟩ + (((-1 : ℝ) : ℂ) * Complex.I) • (x : E) ∈
          LinearMap.range (shiftMap T.closure (-1 : ℝ)) := ⟨⟨(x : E), hx⟩, rfl⟩
      have h0 := (Submodule.mem_orthogonal _ _).mp hw _ hmem
      rw [hTx]
      exact inner_eq_zero_symm.mp h0
    obtain ⟨hw2, hval⟩ := adjoint_apply_of_mem_orthogonal hT (-1 : ℝ) hw'
    refine hneg ⟨w, hw2⟩ ?_
    rw [hval]
    push_cast
    module
  -- the adjoint is contained in the closure
  have hkey : T.adjoint ≤ T.closure := by
    have hdom : ∀ u : T.adjoint.domain, ∃ x : T.closure.domain, (u : E) = (x : E) := by
      intro u
      have hex : T.adjoint u + (((-1 : ℝ) : ℂ) * Complex.I) • (u : E) ∈
          LinearMap.range (shiftMap T.closure (-1 : ℝ)) := by rw [hrangetop]; trivial
      obtain ⟨x, hx⟩ := hex
      have hxdom : (x : E) ∈ T.adjoint.domain := hAle.1 x.2
      have hxval : T.closure x = T.adjoint ⟨(x : E), hxdom⟩ := hAle.2 rfl
      have hsub : (u : E) - (x : E) ∈ T.adjoint.domain :=
        Submodule.sub_mem _ u.2 hxdom
      have hval : T.adjoint ⟨(u : E) - (x : E), hsub⟩ = Complex.I • ((u : E) - (x : E)) := by
        have hsplit : (⟨(u : E) - (x : E), hsub⟩ : T.adjoint.domain)
            = u - ⟨(x : E), hxdom⟩ := by
          apply Subtype.ext; simp
        rw [hsplit, LinearPMap.map_sub, ← hxval]
        rw [shiftMap_apply] at hx
        push_cast at hx ⊢
        linear_combination (norm := module) -hx
      have hzero := hpos ⟨(u : E) - (x : E), hsub⟩ hval
      exact ⟨x, by simpa [sub_eq_zero] using hzero⟩
    constructor
    · intro u hu
      obtain ⟨x, hx⟩ := hdom ⟨u, hu⟩
      simpa [← hx] using x.2
    · rintro ⟨u, hu⟩ ⟨v, hv⟩ huv
      have huv' : u = v := huv
      subst huv'
      exact (hAle.2 (x := ⟨u, hv⟩) (y := ⟨u, hu⟩) rfl).symm
  have hAeq : T.adjoint = T.closure := le_antisymm hkey hAle
  rw [LinearPMap.isSelfAdjoint_def]
  have h1 : T.closure.adjoint ≤ T.adjoint :=
    adjoint_le_adjoint_of_le hT hAdense T.le_closure
  have h2 : T.closure ≤ T.closure.adjoint := hAsym.le_adjoint hAdense
  exact le_antisymm (hAeq ▸ h1) h2

end Hilbert

end Brockian.Weyl

namespace Brockian.Weyl.SchrodingerMinimal

open MeasureTheory Complex LinearPMap
open scoped ContDiff

local notation "L2" => MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A test function: a smooth, compactly supported function `ℝ → ℂ`. -/
def IsTestFn (g : ℝ → ℂ) : Prop := ContDiff ℝ ∞ g ∧ HasCompactSupport g

/-- The space of smooth compactly supported functions, as a submodule of `ℝ → ℂ`. -/
def testFunctions : Submodule ℂ (ℝ → ℂ) where
  carrier := {g | IsTestFn g}
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport, tsupport]⟩
  smul_mem' := fun c f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩

theorem isTestFn_of_mem {g : ℝ → ℂ} (hg : g ∈ testFunctions) : IsTestFn g := hg

theorem memLp_of_isTestFn {g : ℝ → ℂ} (hg : IsTestFn g) : MemLp g 2 (volume : Measure ℝ) :=
  hg.1.continuous.memLp_of_hasCompactSupport hg.2

/-- A test function, viewed as an element of `L²(ℝ)`. -/
noncomputable def testToL2 : testFunctions →ₗ[ℂ] L2 where
  toFun g := (memLp_of_isTestFn (isTestFn_of_mem g.2)).toLp (g : ℝ → ℂ)
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' _ _ := MemLp.toLp_const_smul _ _

theorem testToL2_coeFn (g : testFunctions) : (testToL2 g : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) :=
  MemLp.coeFn_toLp (memLp_of_isTestFn (isTestFn_of_mem g.2))

theorem testToL2_injective : Function.Injective testToL2 := by
  intro f g h
  have hae : (f : ℝ → ℂ) =ᵐ[volume] (g : ℝ → ℂ) := by
    refine (testToL2_coeFn f).symm.trans ?_
    rw [h]
    exact testToL2_coeFn g
  exact Subtype.ext ((Continuous.ae_eq_iff_eq volume (isTestFn_of_mem f.2).1.continuous
    (isTestFn_of_mem g.2).1.continuous).mp hae)

theorem contDiff_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (deriv f) :=
  (contDiff_infty_iff_deriv.mp hf).2

theorem deriv_add_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    deriv (f + g) = deriv f + deriv g := by
  funext x
  exact deriv_add (hf.differentiable (by simp) x) (hg.differentiable (by simp) x)

theorem deriv_smul_contDiff (c : ℂ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    deriv (c • f) = c • deriv f := by
  funext x
  simpa using deriv_const_smul (F := ℂ) c (hf.differentiable (by simp) x)

/-- The Schrödinger differential expression `-g'' + V g`. -/
noncomputable def schExpr (V : ℝ → ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -(deriv (deriv g) x) + (V x : ℂ) * g x

theorem isTestFn_schExpr {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) {g : ℝ → ℂ} (hg : IsTestFn g) :
    IsTestFn (schExpr V g) := by
  have hd2 : ContDiff ℝ ∞ (deriv (deriv g)) := contDiff_deriv (contDiff_deriv hg.1)
  refine ⟨(hd2.neg).add ((Complex.ofRealCLM.contDiff.comp hV).mul hg.1), ?_⟩
  exact (hg.2.deriv.deriv.neg).add (HasCompactSupport.mul_left hg.2)

/-- The Schrödinger differential expression as a linear map on test functions. -/
noncomputable def schMap (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) : testFunctions →ₗ[ℂ] testFunctions where
  toFun g := ⟨schExpr V (g : ℝ → ℂ), isTestFn_schExpr hV (isTestFn_of_mem g.2)⟩
  map_add' f g := by
    have hf := isTestFn_of_mem f.2
    have hg := isTestFn_of_mem g.2
    apply Subtype.ext
    have hd2 : deriv (deriv ((f : ℝ → ℂ) + (g : ℝ → ℂ)))
        = deriv (deriv (f : ℝ → ℂ)) + deriv (deriv (g : ℝ → ℂ)) := by
      rw [deriv_add_contDiff hf.1 hg.1,
        deriv_add_contDiff (contDiff_deriv hf.1) (contDiff_deriv hg.1)]
    show schExpr V ((f : ℝ → ℂ) + (g : ℝ → ℂ)) = schExpr V (f : ℝ → ℂ) + schExpr V (g : ℝ → ℂ)
    funext x
    simp only [schExpr, hd2, Pi.add_apply]
    ring
  map_smul' c f := by
    have hf := isTestFn_of_mem f.2
    apply Subtype.ext
    have hd2 : deriv (deriv (c • (f : ℝ → ℂ))) = c • deriv (deriv (f : ℝ → ℂ)) := by
      rw [deriv_smul_contDiff c hf.1, deriv_smul_contDiff c (contDiff_deriv hf.1)]
    show schExpr V (c • (f : ℝ → ℂ)) = c • schExpr V (f : ℝ → ℂ)
    funext x
    simp only [schExpr, hd2, Pi.smul_apply, smul_eq_mul]
    ring

/-- The minimal Schrödinger operator: `-d²/dx² + V` with domain the smooth compactly supported
functions inside `L²(ℝ)`. -/
noncomputable def schrodingerMinimal (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) : L2 →ₗ.[ℂ] L2 where
  domain := LinearMap.range testToL2
  toFun := (testToL2.comp (schMap V hV)).comp
    (LinearEquiv.ofInjective testToL2 testToL2_injective).symm.toLinearMap

theorem schrodingerMinimal_domain (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) :
    (schrodingerMinimal V hV).domain = LinearMap.range testToL2 := rfl

theorem schrodingerMinimal_apply {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (g : testFunctions)
    (v : (schrodingerMinimal V hV).domain) (hv : (v : L2) = testToL2 g) :
    schrodingerMinimal V hV v = testToL2 (schMap V hV g) := by
  have hvg : v = (LinearEquiv.ofInjective testToL2 testToL2_injective) g := by
    apply Subtype.ext
    rw [hv]
    rfl
  show testToL2 (schMap V hV ((LinearEquiv.ofInjective testToL2 testToL2_injective).symm v)) = _
  rw [hvg, LinearEquiv.symm_apply_apply]

/-- The domain of the minimal Schrödinger operator is dense in `L²(ℝ)`. -/
theorem dense_domain (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) :
    Dense ((schrodingerMinimal V hV).domain : Set L2) := by
  have hd := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (F := ℂ)
    (μ := (volume : Measure ℝ)) (p := 2) (by simp)
  refine Dense.mono ?_ hd
  rintro f ⟨g, hfg, hcs, hsm⟩
  refine ⟨⟨g, show IsTestFn g from ⟨hsm, hcs⟩⟩, ?_⟩
  refine (Lp.ext_iff.mpr ?_).symm
  exact hfg.trans (testToL2_coeFn ⟨g, show IsTestFn g from ⟨hsm, hcs⟩⟩).symm

theorem IsTestFn.deriv {f : ℝ → ℂ} (hf : IsTestFn f) : IsTestFn (deriv f) :=
  ⟨contDiff_deriv hf.1, hf.2.deriv⟩

theorem IsTestFn.conj {f : ℝ → ℂ} (hf : IsTestFn f) :
    IsTestFn (fun x => (starRingEnd ℂ) (f x)) :=
  ⟨Complex.conjCLE.contDiff.comp hf.1,
    hf.2.comp_left (g := fun z : ℂ => (starRingEnd ℂ) z) (by simp)⟩

theorem integrable_mul_of_isTestFn {f g : ℝ → ℂ} (hf : IsTestFn f) (hg : IsTestFn g) :
    Integrable (fun x => f x * g x) (volume : Measure ℝ) :=
  (hf.1.continuous.mul hg.1.continuous).integrable_of_hasCompactSupport
    (hf.2.mul_right (f' := g))

theorem deriv_conj_of_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    deriv (fun x => (starRingEnd ℂ) (f x)) = fun x => (starRingEnd ℂ) (deriv f x) := by
  funext x
  have h1 : HasDerivAt f (deriv f x) x := (hf.differentiable (by simp) x).hasDerivAt
  exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x h1).deriv

/-- Integration by parts, twice, for test functions. -/
theorem integral_deriv_deriv_mul {f g : ℝ → ℂ} (hf : IsTestFn f) (hg : IsTestFn g) :
    ∫ x, deriv (deriv f) x * g x = ∫ x, f x * deriv (deriv g) x := by
  have hf' := hf.deriv
  have hf'' := hf'.deriv
  have hg' := hg.deriv
  have hg'' := hg'.deriv
  have step1 : ∫ x, f x * deriv (deriv g) x = -∫ x, deriv f x * deriv g x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x => (hf.1.differentiable (by simp) x).hasDerivAt)
      (fun x => (hg'.1.differentiable (by simp) x).hasDerivAt)
      (integrable_mul_of_isTestFn hf hg'') (integrable_mul_of_isTestFn hf' hg')
      (integrable_mul_of_isTestFn hf hg')
  have step2 : ∫ x, deriv f x * deriv g x = -∫ x, deriv (deriv f) x * g x :=
    integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x => (hf'.1.differentiable (by simp) x).hasDerivAt)
      (fun x => (hg.1.differentiable (by simp) x).hasDerivAt)
      (integrable_mul_of_isTestFn hf' hg') (integrable_mul_of_isTestFn hf'' hg)
      (integrable_mul_of_isTestFn hf' hg)
  rw [step1, step2, neg_neg]

theorem inner_L2_testToL2 (u : L2) (b : testFunctions) :
    ⟪u, testToL2 b⟫ = ∫ x, (starRingEnd ℂ) ((u : ℝ → ℂ) x) * (b : ℝ → ℂ) x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [testToL2_coeFn b] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

theorem inner_testToL2 (a b : testFunctions) :
    ⟪testToL2 a, testToL2 b⟫ = ∫ x, (starRingEnd ℂ) ((a : ℝ → ℂ) x) * (b : ℝ → ℂ) x := by
  rw [inner_L2_testToL2]
  refine integral_congr_ae ?_
  filter_upwards [testToL2_coeFn a] with x hx
  rw [hx]

theorem conj_schExpr (V : ℝ → ℝ) {f : ℝ → ℂ} (hf : IsTestFn f) (x : ℝ) :
    (starRingEnd ℂ) (schExpr V f x) = schExpr V (fun y => (starRingEnd ℂ) (f y)) x := by
  simp only [schExpr, deriv_conj_of_contDiff hf.1,
    deriv_conj_of_contDiff (contDiff_deriv hf.1)]
  simp [Complex.conj_ofReal]

/-- The minimal Schrödinger operator is symmetric. -/
theorem isSymmetric_schrodingerMinimal (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V) :
    Brockian.Weyl.IsSymmetricPMap (schrodingerMinimal V hV) := by
  intro a b
  obtain ⟨f, hf⟩ := a.2
  obtain ⟨g, hg⟩ := b.2
  have hfT := isTestFn_of_mem f.2
  have hgT := isTestFn_of_mem g.2
  rw [schrodingerMinimal_apply hV f a hf.symm, schrodingerMinimal_apply hV g b hg.symm, ← hf, ← hg,
    inner_testToL2, inner_testToL2]
  have hFT : IsTestFn (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y)) := hfT.conj
  have hA : Integrable (fun x => (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x)
      (volume : Measure ℝ) :=
    integrable_mul_of_isTestFn ((isTestFn_schExpr hV hfT).conj) hgT
  have hB : Integrable (fun x => (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x)
      (volume : Measure ℝ) :=
    integrable_mul_of_isTestFn hFT (isTestFn_schExpr hV hgT)
  have hpoint : ∀ x : ℝ, (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x
      - (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x
      = -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x)
        + (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x := by
    intro x
    show (starRingEnd ℂ) (schExpr V (f : ℝ → ℂ) x) * (g : ℝ → ℂ) x
      - (starRingEnd ℂ) ((f : ℝ → ℂ) x) * schExpr V (g : ℝ → ℂ) x = _
    rw [conj_schExpr V hfT x]
    simp only [schExpr]
    ring
  have hsplit : (∫ x, (-(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x
        * (g : ℝ → ℂ) x) + (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x))
      = (∫ x, -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x))
        + ∫ x, (starRingEnd ℂ) ((f : ℝ → ℂ) x) * deriv (deriv (g : ℝ → ℂ)) x :=
    integral_add ((integrable_mul_of_isTestFn hFT.deriv.deriv hgT).neg)
      (integrable_mul_of_isTestFn hFT hgT.deriv.deriv)
  have hneg : (∫ x, -(deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x))
      = -∫ x, deriv (deriv (fun y => (starRingEnd ℂ) ((f : ℝ → ℂ) y))) x * (g : ℝ → ℂ) x :=
    integral_neg _
  have hzero : (∫ x, (starRingEnd ℂ) ((schMap V hV f : ℝ → ℂ) x) * (g : ℝ → ℂ) x)
      - ∫ x, (starRingEnd ℂ) ((f : ℝ → ℂ) x) * (schMap V hV g : ℝ → ℂ) x = 0 := by
    rw [← integral_sub hA hB,
      integral_congr_ae (Filter.Eventually.of_forall hpoint), hsplit, hneg,
      integral_deriv_deriv_mul hFT hgT]
    ring
  linear_combination hzero

/-- An eigenvector of the adjoint of the minimal operator is a distributional solution of the
Schrödinger equation. -/
theorem weak_ode_of_adjoint_eigenvector {V : ℝ → ℝ} (hV : ContDiff ℝ ∞ V) (z : ℂ)
    (u : (schrodingerMinimal V hV).adjoint.domain)
    (hu : (schrodingerMinimal V hV).adjoint u = z • (u : L2)) :
    ∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, (starRingEnd ℂ) ((u : L2) x) * (-(deriv (deriv g) x) + (V x : ℂ) * g x)
        = (starRingEnd ℂ) z * ∫ x, (starRingEnd ℂ) ((u : L2) x) * g x := by
  intro g hg1 hg2
  set G : testFunctions := ⟨g, show IsTestFn g from ⟨hg1, hg2⟩⟩ with hG
  have hmem : testToL2 G ∈ (schrodingerMinimal V hV).domain := ⟨G, rfl⟩
  have hformal := LinearPMap.adjoint_isFormalAdjoint (dense_domain V hV) u ⟨testToL2 G, hmem⟩
  rw [hu, schrodingerMinimal_apply hV G ⟨testToL2 G, hmem⟩ rfl] at hformal
  rw [inner_smul_left, inner_L2_testToL2, inner_L2_testToL2] at hformal
  exact hformal.symm

theorem memLp_conj (u : L2) :
    MemLp (fun x => (starRingEnd ℂ) ((u : ℝ → ℂ) x)) 2 (volume : Measure ℝ) := by
  refine MemLp.of_le (Lp.memLp u) ?_ ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)
  · filter_upwards with x
    simp

/-- The complex conjugate of an `L²` function, as an element of `L²`. -/
noncomputable def conjL2 (u : L2) : L2 := (memLp_conj u).toLp _

theorem conjL2_coeFn (u : L2) :
    (conjL2 u : ℝ → ℂ) =ᵐ[volume] fun x => (starRingEnd ℂ) ((u : ℝ → ℂ) x) :=
  MemLp.coeFn_toLp (memLp_conj u)

theorem conjL2_eq_zero_iff (u : L2) : conjL2 u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have h0 : (fun x => (starRingEnd ℂ) ((u : ℝ → ℂ) x)) =ᵐ[volume] (0 : ℝ → ℂ) := by
      refine (conjL2_coeFn u).symm.trans ?_
      rw [h]
      exact Lp.coeFn_zero ℂ 2 volume
    refine Lp.ext_iff.mpr ?_
    filter_upwards [h0, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0
    have : (starRingEnd ℂ) ((u : ℝ → ℂ) x) = 0 := hx
    rw [hx0]
    simpa using congrArg (starRingEnd ℂ) this
  · intro h
    refine Lp.ext_iff.mpr ?_
    filter_upwards [conjL2_coeFn u, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx hx0
    rw [hx, hx0, h]
    simp

/-- **Essential self-adjointness of the minimal Schrödinger operator.**

If the differential equation `-u'' + V u = z u` (understood in the distributional sense) has no
nonzero solution `u ∈ L²(ℝ)` for `z = i` and for `z = -i`, then the minimal Schrödinger operator
`-d²/dx² + V`, defined on the smooth compactly supported functions, is essentially self-adjoint:
its closure is a self-adjoint operator. -/
theorem schrodinger_essentiallySelfAdjoint_of_ode (V : ℝ → ℝ) (hV : ContDiff ℝ ∞ V)
    (hode : ∀ z : ℂ, (z = Complex.I ∨ z = -Complex.I) → ∀ u : L2,
      (∀ g : ℝ → ℂ, ContDiff ℝ ∞ g → HasCompactSupport g →
          ∫ x, (u : ℝ → ℂ) x * (-(deriv (deriv g) x) + (V x : ℂ) * g x)
            = z * ∫ x, (u : ℝ → ℂ) x * g x) → u = 0) :
    IsSelfAdjoint (schrodingerMinimal V hV).closure := by
  refine Brockian.Weyl.isSelfAdjoint_closure_of_deficiency (dense_domain V hV)
    (isSymmetric_schrodingerMinimal V hV) ?_ ?_
  · intro u hu
    have hweak := weak_ode_of_adjoint_eigenvector hV Complex.I u hu
    have hzero : conjL2 (u : L2) = 0 := by
      refine hode (-Complex.I) (Or.inr rfl) (conjL2 (u : L2)) ?_
      intro g hg1 hg2
      have h1 : ∫ x, (conjL2 (u : L2) : ℝ → ℂ) x * (-(deriv (deriv g) x) + (V x : ℂ) * g x)
          = ∫ x, (starRingEnd ℂ) ((u : L2) x) * (-(deriv (deriv g) x) + (V x : ℂ) * g x) := by
        refine integral_congr_ae ?_
        filter_upwards [conjL2_coeFn (u : L2)] with x hx
        rw [hx]
      have h2 : ∫ x, (conjL2 (u : L2) : ℝ → ℂ) x * g x
          = ∫ x, (starRingEnd ℂ) ((u : L2) x) * g x := by
        refine integral_congr_ae ?_
        filter_upwards [conjL2_coeFn (u : L2)] with x hx
        rw [hx]
      rw [h1, h2, hweak g hg1 hg2]
      simp
    exact (conjL2_eq_zero_iff _).mp hzero
  · intro u hu
    have hweak := weak_ode_of_adjoint_eigenvector hV (-Complex.I) u hu
    have hzero : conjL2 (u : L2) = 0 := by
      refine hode Complex.I (Or.inl rfl) (conjL2 (u : L2)) ?_
      intro g hg1 hg2
      have h1 : ∫ x, (conjL2 (u : L2) : ℝ → ℂ) x * (-(deriv (deriv g) x) + (V x : ℂ) * g x)
          = ∫ x, (starRingEnd ℂ) ((u : L2) x) * (-(deriv (deriv g) x) + (V x : ℂ) * g x) := by
        refine integral_congr_ae ?_
        filter_upwards [conjL2_coeFn (u : L2)] with x hx
        rw [hx]
      have h2 : ∫ x, (conjL2 (u : L2) : ℝ → ℂ) x * g x
          = ∫ x, (starRingEnd ℂ) ((u : L2) x) * g x := by
        refine integral_congr_ae ?_
        filter_upwards [conjL2_coeFn (u : L2)] with x hx
        rw [hx]
      rw [h1, h2, hweak g hg1 hg2]
      simp
    exact (conjL2_eq_zero_iff _).mp hzero

end Brockian.Weyl.SchrodingerMinimal

