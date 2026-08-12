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
Essential self-adjointness via the basic criterion on deficiency subspaces.

This file develops, for an unbounded (partially defined) operator on a complex Hilbert
space, the classical criterion of von Neumann/Weyl:

  a densely defined symmetric operator `T` is essentially self-adjoint as soon as the two
  deficiency subspaces `ker (T† - i)` and `ker (T† + i)` are trivial.

Along the way we show that under this hypothesis the closure of `T` coincides with the
adjoint `T†`.
-/
import Mathlib

namespace Brockian.Weyl

open LinearPMap Complex
open scoped ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- An unbounded operator on a Hilbert space is *essentially self-adjoint* if its closure is
self-adjoint. -/
def IsEssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  IsSelfAdjoint T.closure

/-- The deficiency subspace of `T` at `z`: the solutions in the domain of the adjoint of the
equation `T† u = z • u`. -/
def deficiency (T : H →ₗ.[ℂ] H) (z : ℂ) : Prop :=
  ∀ u : T†.domain, (T† u) = z • (u : H) → (u : H) = 0

section Criterion

variable {T : H →ₗ.[ℂ] H}

/-- A symmetric operator is contained in its adjoint. -/
theorem le_adjoint_of_isSymmetric (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T) :
    T ≤ T† :=
  hs.le_adjoint hd

/-- The adjoint is antitone. -/
theorem adjoint_le_adjoint_of_le {S : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H)) (h : T ≤ S)
    (hSd : Dense (S.domain : Set H)) : S† ≤ T† := by
  refine IsFormalAdjoint.le_adjoint hd ?_
  intro x y
  have hx : (x : H) ∈ S.domain := h.1 x.2
  have hSx : S ⟨(x : H), hx⟩ = T x := (h.2 rfl).symm
  have := ((adjoint_isFormalAdjoint hSd).symm) ⟨(x : H), hx⟩ y
  simpa [hSx] using this

omit [CompleteSpace H] in
/-- Symmetry passes to the closure of the graph. -/
theorem graphClosure_symm (hs : T.IsFormalAdjoint T) {p q : H × H}
    (hp : p ∈ T.graph.topologicalClosure) (hq : q ∈ T.graph.topologicalClosure) :
    ⟪p.2, q.1⟫ = ⟪p.1, q.2⟫ := by
  -- first fix `q` in the graph and let `p` vary
  have step1 : ∀ p' ∈ T.graph.topologicalClosure, ∀ q' ∈ T.graph,
      ⟪p'.2, q'.1⟫ = ⟪p'.1, q'.2⟫ := by
    intro p' hp' q' hq'
    have hclosed : IsClosed {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      have : Continuous fun r : H × H => ⟪r.2, q'.1⟫ - ⟪r.1, q'.2⟫ := by fun_prop
      simpa [Set.ext_iff, sub_eq_zero] using isClosed_eq (by fun_prop :
        Continuous fun r : H × H => ⟪r.2, q'.1⟫) (by fun_prop :
        Continuous fun r : H × H => ⟪r.1, q'.2⟫)
    have hsub : (T.graph : Set (H × H)) ⊆ {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      rintro r hr
      obtain ⟨a, ha, ha'⟩ := T.mem_graph_iff.1 hr
      obtain ⟨b, hb, hb'⟩ := T.mem_graph_iff.1 hq'
      simp only [Set.mem_setOf_eq, ← ha, ← ha', ← hb, ← hb']
      exact hs a b
    have : (T.graph.topologicalClosure : Set (H × H)) ⊆
        {r : H × H | ⟪r.2, q'.1⟫ = ⟪r.1, q'.2⟫} := by
      rw [Submodule.topologicalClosure_coe]
      exact hclosed.closure_subset_iff.2 hsub
    exact this hp'
  -- now fix `p` in the closure and let `q` vary
  have hclosed : IsClosed {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : (T.graph : Set (H × H)) ⊆ {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} := by
    intro r hr
    exact step1 p hp r hr
  have : (T.graph.topologicalClosure : Set (H × H)) ⊆
      {r : H × H | ⟪p.2, r.1⟫ = ⟪p.1, r.2⟫} := by
    rw [Submodule.topologicalClosure_coe]
    exact hclosed.closure_subset_iff.2 hsub
  exact this hq

omit [CompleteSpace H] in
/-- For a point `(x, y)` in the closure of the graph of a symmetric operator we have
`‖y - i • x‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2`. -/
theorem norm_sub_I_smul_sq (hs : T.IsFormalAdjoint T) {p : H × H}
    (hp : p ∈ T.graph.topologicalClosure) :
    ‖p.2 - I • p.1‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  have hsym := graphClosure_symm hs hp hp
  have hre : RCLike.re (⟪p.2, I • p.1⟫) = 0 := by
    have h0 : ⟪p.2, I • p.1⟫ = I * ⟪p.2, p.1⟫ := by
      simp
    have hconj : conj ⟪p.2, p.1⟫ = ⟪p.2, p.1⟫ := by
      rw [inner_conj_symm]; exact hsym.symm
    have him : (⟪p.2, p.1⟫).im = 0 := Complex.conj_eq_iff_im.1 hconj
    simp only [h0, RCLike.re_to_complex, Complex.mul_re, Complex.I_re, Complex.I_im, him]
    ring
  have hexp := @norm_sub_sq ℂ _ _ _ _ p.2 (I • p.1)
  rw [hexp, hre, norm_smul, Complex.norm_I, one_mul]
  ring

omit [CompleteSpace H] in
theorem norm_le_norm_sub_I_smul (hs : T.IsFormalAdjoint T) {p : H × H}
    (hp : p ∈ T.graph.topologicalClosure) :
    ‖p‖ ≤ ‖p.2 - I • p.1‖ := by
  have h := norm_sub_I_smul_sq hs hp
  have h1 : ‖p.1‖ ^ 2 ≤ ‖p.2 - I • p.1‖ ^ 2 := by
    rw [h]; nlinarith [norm_nonneg p.2]
  have h2 : ‖p.2‖ ^ 2 ≤ ‖p.2 - I • p.1‖ ^ 2 := by
    rw [h]; nlinarith [norm_nonneg p.1]
  have h1' : ‖p.1‖ ≤ ‖p.2 - I • p.1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h1
  have h2' : ‖p.2‖ ≤ ‖p.2 - I • p.1‖ :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  rw [Prod.norm_def]
  exact max_le h1' h2'

/-- The `-i` deficiency condition implies that `y - i • x` runs through all of `H` as `(x, y)`
runs through the closure of the graph. -/
theorem exists_mem_graphClosure (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₂ : deficiency T (-I)) (z : H) :
    ∃ p ∈ T.graph.topologicalClosure, p.2 - I • p.1 = z := by
  classical
  set M := T.graph.topologicalClosure with hM
  haveI : CompleteSpace M := (Submodule.isClosed_topologicalClosure T.graph).completeSpace_coe
  -- the map `φ`
  let φ : M →L[ℂ] H :=
    { toFun := fun p => (p : H × H).2 - I • (p : H × H).1
      map_add' := by intro a b; simp [smul_add]; abel
      map_smul' := by
        intro c a
        simp [smul_sub, smul_smul, mul_comm]
      cont := by
        apply Continuous.sub
        · exact continuous_snd.comp continuous_subtype_val
        · exact (continuous_const_smul I).comp (continuous_fst.comp continuous_subtype_val) }
  have hanti : AntilipschitzWith 1 φ := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro a b
    have : dist a b = ‖(a : H × H) - b‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    rw [this, dist_eq_norm]
    have hab : ((a : H × H) - b) ∈ M := M.sub_mem a.2 b.2
    have := norm_le_norm_sub_I_smul hs hab
    have hφ : φ a - φ b = ((a : H × H) - b).2 - I • ((a : H × H) - b).1 := by
      simp only [φ, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_sub,
        Prod.snd_sub, smul_sub]
      abel
    rw [hφ]
    simpa using this
  have hclosed : IsClosed (Set.range φ) := hanti.isClosed_range φ.uniformContinuous
  set R : Submodule ℂ H := LinearMap.range (φ : M →ₗ[ℂ] H) with hR
  have hRcoe : (R : Set H) = Set.range φ := by
    ext x; simp [hR, LinearMap.mem_range]
  have hRclosed : IsClosed (R : Set H) := by rw [hRcoe]; exact hclosed
  haveI : CompleteSpace R := hRclosed.completeSpace_coe
  have hRtop : R = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff]
    rw [Submodule.eq_bot_iff]
    intro w hw
    -- `w` is orthogonal to the range, hence in the deficiency space at `-I`
    have hw' : ∀ x : T.domain, ⟪(-I) • w, (x : H)⟫ = ⟪w, T x⟫ := by
      intro x
      have hmem : ((x : H), T x) ∈ M := by
        apply Submodule.le_topologicalClosure
        exact T.mem_graph x
      have hmemR : (T x - I • (x : H)) ∈ R := ⟨⟨((x : H), T x), hmem⟩, rfl⟩
      have hzero : ⟪(T x - I • (x : H)), w⟫ = (0 : ℂ) := hw _ hmemR
      have h1 : ⟪T x, w⟫ = ⟪I • (x : H), w⟫ := by
        rw [inner_sub_left, sub_eq_zero] at hzero; exact hzero
      calc ⟪(-I) • w, (x : H)⟫ = I * ⟪w, (x : H)⟫ := by
            rw [inner_smul_left]; congr 1; simp
        _ = conj (⟪I • (x : H), w⟫) := by
            rw [inner_smul_left, map_mul]
            congr 1
            · simp
            · rw [inner_conj_symm]
        _ = conj ⟪T x, w⟫ := by rw [h1]
        _ = ⟪w, T x⟫ := inner_conj_symm _ _
    have hwd : w ∈ T†.domain := mem_adjoint_domain_of_exists _ ⟨(-I) • w, hw'⟩
    exact h₂ ⟨w, hwd⟩ (adjoint_apply_eq hd ⟨w, hwd⟩ hw')
  have : z ∈ R := by rw [hRtop]; trivial
  rw [hR, LinearMap.mem_range] at this
  obtain ⟨p, hp⟩ := this
  exact ⟨(p : H × H), p.2, hp⟩

/-- Under the two deficiency conditions, the graph of the adjoint is contained in the closure of
the graph. -/
theorem adjoint_graph_le_graphClosure (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    T†.graph ≤ T.graph.topologicalClosure := by
  rintro ⟨u, w⟩ huw
  obtain ⟨y, hy, hy'⟩ := T†.mem_graph_iff.1 huw
  simp only at hy hy'
  subst hy
  subst hy'
  obtain ⟨p, hp, hpz⟩ := exists_mem_graphClosure hd hs h₂ (T† y - I • (y : H))
  have hpmem : p ∈ T†.graph :=
    (Submodule.topologicalClosure_minimal _ (le_graph_of_le (le_adjoint_of_isSymmetric hd hs))
      (adjoint_isClosed hd)) hp
  obtain ⟨x, hx, hx'⟩ := T†.mem_graph_iff.1 hpmem
  have hvd : ((y : H) - (x : H)) ∈ T†.domain := T†.domain.sub_mem y.2 x.2
  have hkey : T† ⟨(y : H) - (x : H), hvd⟩ = I • ((y : H) - (x : H)) := by
    have hsub : (⟨(y : H) - (x : H), hvd⟩ : T†.domain) = y - x := rfl
    rw [hsub, LinearPMap.map_sub]
    have : T† y - T† x = I • (y : H) - I • (x : H) := by
      have := hpz
      rw [← hx, ← hx'] at this
      linear_combination (norm := module) -this
    rw [this, smul_sub]
  have hzero := h₁ ⟨(y : H) - (x : H), hvd⟩ hkey
  have hyx : y = x := Subtype.ext (sub_eq_zero.1 hzero)
  have hpe : ((x : H), (T† x : H)) = p := Prod.ext hx hx'
  rw [hyx, hpe]
  exact hp

/-- **Basic criterion of essential self-adjointness.** A densely defined symmetric operator with
trivial deficiency subspaces is essentially self-adjoint, and its closure is its adjoint. -/
theorem closure_eq_adjoint_of_deficiency (hd : Dense (T.domain : Set H)) (hs : T.IsFormalAdjoint T)
    (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    T.closure = T† := by
  have hle : T ≤ T† := le_adjoint_of_isSymmetric hd hs
  have hclosable : T.IsClosable :=
    isClosable_iff_exists_closed_extension.2 ⟨T†, adjoint_isClosed hd, hle⟩
  apply eq_of_eq_graph
  rw [← hclosable.graph_closure_eq_closure_graph]
  refine le_antisymm ?_ (adjoint_graph_le_graphClosure hd hs h₁ h₂)
  exact Submodule.topologicalClosure_minimal _ (le_graph_of_le hle) (adjoint_isClosed hd)

theorem isEssentiallySelfAdjoint_of_deficiency (hd : Dense (T.domain : Set H))
    (hs : T.IsFormalAdjoint T) (h₁ : deficiency T I) (h₂ : deficiency T (-I)) :
    IsEssentiallySelfAdjoint T := by
  have hcl := closure_eq_adjoint_of_deficiency hd hs h₁ h₂
  -- the adjoint is symmetric, since its graph is the closure of the graph of `T`
  have hclosable : T.IsClosable :=
    isClosable_iff_exists_closed_extension.2
      ⟨T†, adjoint_isClosed hd, le_adjoint_of_isSymmetric hd hs⟩
  have hgraph : T†.graph = T.graph.topologicalClosure := by
    rw [← hcl, ← hclosable.graph_closure_eq_closure_graph]
  have hsymm : T†.IsFormalAdjoint T† := by
    intro x y
    have hx : ((x : H), T† x) ∈ T.graph.topologicalClosure := by
      rw [← hgraph]; exact T†.mem_graph x
    have hy : ((y : H), T† y) ∈ T.graph.topologicalClosure := by
      rw [← hgraph]; exact T†.mem_graph y
    exact graphClosure_symm hs hx hy
  have hd' : Dense (T†.domain : Set H) := by
    apply Dense.mono _ hd
    intro x hx
    exact (le_adjoint_of_isSymmetric hd hs).1 hx
  have hle1 : T† ≤ T†† := hsymm.le_adjoint hd'
  have hle2 : T†† ≤ T† := adjoint_le_adjoint_of_le hd (le_adjoint_of_isSymmetric hd hs) hd'
  rw [IsEssentiallySelfAdjoint, hcl, isSelfAdjoint_def]
  exact le_antisymm hle2 hle1

end Criterion

end Brockian.Weyl

/-
Multiplication by a bounded real function as a bounded self-adjoint operator on `L²`.
-/
import Mathlib

namespace Brockian.Weyl

open MeasureTheory Complex
open scoped ComplexConjugate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section Mul

/-- The hypotheses we require of the potential: it is measurable and bounded by `C`. -/
structure BoundedPotential (V : α → ℝ) (C : ℝ) (μ : Measure α) : Prop where
  measurable : AEStronglyMeasurable V μ
  le_bound : ∀ᵐ x ∂μ, |V x| ≤ C

variable {V : α → ℝ} {C : ℝ}

theorem BoundedPotential.aestronglyMeasurable_complex (hV : BoundedPotential V C μ) :
    AEStronglyMeasurable (fun x => (V x : ℂ)) μ :=
  Complex.continuous_ofReal.comp_aestronglyMeasurable hV.measurable

/-- Multiplication by a bounded function preserves `L²`. -/
theorem BoundedPotential.memLp_mul (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    MemLp (fun x => (V x : ℂ) * (f : α → ℂ) x) 2 μ := by
  have hf : MemLp (fun x => ((C : ℂ)) * (f : α → ℂ) x) 2 μ := (Lp.memLp f).const_mul _
  refine MemLp.mono hf ?_ ?_
  · exact hV.aestronglyMeasurable_complex.mul (Lp.memLp f).aestronglyMeasurable
  · filter_upwards [hV.le_bound] with x hx
    have hx' : |V x| ≤ |C| := hx.trans (le_abs_self C)
    have h1 : ‖(V x : ℂ)‖ ≤ ‖(C : ℂ)‖ := by
      simpa [Complex.norm_real] using hx'
    calc ‖(V x : ℂ) * (f : α → ℂ) x‖ = ‖(V x : ℂ)‖ * ‖(f : α → ℂ) x‖ := norm_mul _ _
      _ ≤ ‖(C : ℂ)‖ * ‖(f : α → ℂ) x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖(C : ℂ) * (f : α → ℂ) x‖ := (norm_mul _ _).symm

/-- Multiplication by a bounded real function, as a linear map on `L²`. -/
noncomputable def BoundedPotential.mulₗ (hV : BoundedPotential V C μ) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (hV.memLp_mul f).toLp _
  map_add' f g := by
    rw [Lp.ext_iff]
    filter_upwards [(hV.memLp_mul (f + g)).coeFn_toLp, Lp.coeFn_add ((hV.memLp_mul f).toLp _)
      ((hV.memLp_mul g).toLp _), (hV.memLp_mul f).coeFn_toLp, (hV.memLp_mul g).coeFn_toLp,
      Lp.coeFn_add f g] with x h1 h2 h3 h4 h5
    rw [h1, h2]
    simp only [Pi.add_apply, h3, h4, h5]
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, Lp.ext_iff]
    filter_upwards [(hV.memLp_mul (c • f)).coeFn_toLp, Lp.coeFn_smul c ((hV.memLp_mul f).toLp _),
      (hV.memLp_mul f).coeFn_toLp, Lp.coeFn_smul c f] with x h1 h2 h3 h4
    rw [h1, h2]
    simp only [Pi.smul_apply, smul_eq_mul, h3, h4]
    ring

theorem BoundedPotential.coeFn_mulₗ (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    (hV.mulₗ f : α → ℂ) =ᵐ[μ] fun x => (V x : ℂ) * (f : α → ℂ) x :=
  (hV.memLp_mul f).coeFn_toLp

theorem BoundedPotential.norm_mulₗ_le (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    ‖hV.mulₗ f‖ ≤ |C| * ‖f‖ := by
  have hc : ‖((C : ℂ)) • f‖ = |C| * ‖f‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [← hc]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hV.coeFn_mulₗ f, Lp.coeFn_smul ((C : ℂ)) f, hV.le_bound] with x h1 h2 hb
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb.trans (le_abs_self C)) (norm_nonneg _)

/-- Multiplication by a bounded real function, as a bounded operator on `L²`. -/
noncomputable def BoundedPotential.mul (hV : BoundedPotential V C μ) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  hV.mulₗ.mkContinuous |C| hV.norm_mulₗ_le

@[simp] theorem BoundedPotential.mul_apply (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    hV.mul f = hV.mulₗ f := rfl

/-- The multiplication operator by a real function is symmetric. -/
theorem BoundedPotential.inner_mul_left (hV : BoundedPotential V C μ) (f g : Lp ℂ 2 μ) :
    inner ℂ (hV.mul f) g = inner ℂ f (hV.mul g) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hV.coeFn_mulₗ f, hV.coeFn_mulₗ g] with x h1 h2
  rw [BoundedPotential.mul_apply, BoundedPotential.mul_apply, h1, h2]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The quadratic form of a real multiplication operator is real. -/
theorem BoundedPotential.inner_mul_self_isReal (hV : BoundedPotential V C μ) (f : Lp ℂ 2 μ) :
    conj (inner ℂ f (hV.mul f)) = inner ℂ f (hV.mul f) := by
  rw [L2.inner_def, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hV.coeFn_mulₗ f] with x h1
  rw [BoundedPotential.mul_apply, h1]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

end Mul

end Brockian.Weyl

/-
# Essential self-adjointness of one-dimensional Schrödinger operators

We consider the Schrödinger operator `-d²/dx² + V` on the line, with a bounded measurable
real potential `V`, defined on the Schwartz space `𝓢(ℝ, ℂ)` viewed as a dense subspace of
`L²(ℝ)`.

The main result `schrodinger_essentiallySelfAdjoint_of_weakRegularity` states that this
operator is essentially self-adjoint.  The proof goes through the deficiency (Weyl) ODE:
an element `u` of the domain of the adjoint with `T† u = ± i u` is a weak (distributional)
solution of the deficiency equation `-u'' + V u = ± i u`.  The *weak regularity* input,
which is discharged here rather than assumed, is the statement that for a weak solution the
quantity `⟪u, -u''⟫` is real; on the Fourier side this is the identity
`⟪u, -u''⟫ = ∫ (2πξ)² |û(ξ)|² ∂ξ`.
-/
import Brockian.Weyl.Deficiency
import Brockian.Weyl.Multiplication

namespace Brockian.Weyl.DeficiencyODE

open MeasureTheory SchwartzMap FourierTransform Complex LinearPMap Brockian.Weyl
open scoped ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- The Hilbert space `L²(ℝ)`. -/
noncomputable abbrev L2R := Lp (α := ℝ) ℂ 2 volume

/-- A Schwartz function, viewed as an element of `L²(ℝ)`. -/
noncomputable def toL2 : 𝓢(ℝ, ℂ) →L[ℂ] L2R := SchwartzMap.toLpCLM ℂ ℂ 2 volume

theorem coeFn_toL2 (f : 𝓢(ℝ, ℂ)) : (toL2 f : ℝ → ℂ) =ᵐ[volume] ⇑f :=
  SchwartzMap.coeFn_toLp f 2 volume

theorem toL2_injective : Function.Injective toL2 := by
  intro f g h
  have hae : (f : ℝ → ℂ) =ᵐ[volume] g := (coeFn_toL2 f).symm.trans (h ▸ coeFn_toL2 g)
  ext x
  exact congrFun ((f.continuous.ae_eq_iff_eq volume g.continuous).mp hae) x

theorem denseRange_toL2 : DenseRange toL2 :=
  SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) (by simp)

theorem inner_toL2 (f g : 𝓢(ℝ, ℂ)) : ⟪toL2 f, toL2 g⟫ = ∫ x, conj (f x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 f, coeFn_toL2 g] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]
  ring

theorem fourier_toL2 (f : 𝓢(ℝ, ℂ)) : 𝓕 (toL2 f) = toL2 (𝓕 f) :=
  SchwartzMap.toLp_fourier_eq (E := ℝ) (F := ℂ) f

/-- The second derivative operator on Schwartz functions. -/
noncomputable def D2 : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

theorem D2_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : D2 f x = deriv (deriv ⇑f) x := by
  have h1 : D2 f x = deriv (⇑(SchwartzMap.derivCLM ℂ ℂ f)) x :=
    SchwartzMap.derivCLM_apply (𝕜 := ℂ) _ x
  have h2 : (⇑(SchwartzMap.derivCLM ℂ ℂ f)) = deriv ⇑f :=
    funext fun y => SchwartzMap.derivCLM_apply (𝕜 := ℂ) f y
  rw [h1, h2]

/-- The Fourier multiplier of `-d²/dx²`. -/
noncomputable def symb (x : ℝ) : ℝ := (2 * Real.pi * x) ^ 2

theorem symb_nonneg (x : ℝ) : 0 ≤ symb x := sq_nonneg _

theorem continuous_symb : Continuous symb := by
  unfold symb; fun_prop

theorem fourier_derivCLM (g : 𝓢(ℝ, ℂ)) :
    𝓕 (SchwartzMap.derivCLM ℂ ℂ g) = fun y : ℝ => (2 * Real.pi * I * y) • 𝓕 g y := by
  have hco : (⇑(SchwartzMap.derivCLM ℂ ℂ g)) = deriv (⇑g) := by
    ext y; exact SchwartzMap.derivCLM_apply (𝕜 := ℂ) g y
  have hint : Integrable (deriv (⇑g)) volume := by
    apply (SchwartzMap.derivCLM ℂ ℂ g).integrable.congr
    filter_upwards with y using (SchwartzMap.derivCLM_apply (𝕜 := ℂ) g y)
  rw [SchwartzMap.fourier_coe, hco, Real.fourier_deriv g.integrable g.differentiable hint]
  ext y
  rw [SchwartzMap.fourier_coe]

/-- The Fourier transform turns `-d²/dx²` into multiplication by `(2πξ)²`. -/
theorem fourier_neg_D2 (f : 𝓢(ℝ, ℂ)) (x : ℝ) : 𝓕 (-(D2 f)) x = (symb x : ℂ) * 𝓕 f x := by
  have hD2 : 𝓕 (D2 f) x = (-(symb x) : ℝ) * 𝓕 f x := by
    rw [show D2 f = SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f) from rfl,
      fourier_derivCLM, fourier_derivCLM]
    simp only [smul_eq_mul, symb]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hneg : 𝓕 (-(D2 f)) x = -(𝓕 (D2 f) x) := by
    have : (𝓕 (-(D2 f)) : 𝓢(ℝ, ℂ)) = -(𝓕 (D2 f) : 𝓢(ℝ, ℂ)) := map_neg (fourierCLM ℂ _) _
    rw [this]; rfl
  rw [hneg, hD2]
  push_cast
  ring

section Schrodinger

variable {V : ℝ → ℝ} {C : ℝ}

/-- The Schrödinger expression `-f'' + V f`, as a map from Schwartz functions to `L²`. -/
noncomputable def schrodingerAux (hV : BoundedPotential V C volume) : 𝓢(ℝ, ℂ) →L[ℂ] L2R :=
  toL2.comp (-D2) + (hV.mul).comp toL2

theorem schrodingerAux_apply (hV : BoundedPotential V C volume) (f : 𝓢(ℝ, ℂ)) :
    schrodingerAux hV f = toL2 (-(D2 f)) + hV.mul (toL2 f) := rfl

/-- The Schrödinger expression is indeed given by `f ↦ -f'' + V f`. -/
theorem coeFn_schrodingerAux (hV : BoundedPotential V C volume) (f : 𝓢(ℝ, ℂ)) :
    ((schrodingerAux hV f : L2R) : ℝ → ℂ) =ᵐ[volume]
      fun x => -(deriv (deriv ⇑f) x) + (V x : ℂ) * f x := by
  rw [schrodingerAux_apply]
  filter_upwards [Lp.coeFn_add (toL2 (-(D2 f))) (hV.mul (toL2 f)), coeFn_toL2 (-(D2 f)),
    hV.coeFn_mulₗ (toL2 f), coeFn_toL2 f] with x h1 h2 h3 h4
  rw [h1]
  simp only [Pi.add_apply, h2, BoundedPotential.mul_apply, h3, h4, SchwartzMap.neg_apply,
    D2_apply]

/-- The minimal Schrödinger operator `-d²/dx² + V` on `L²(ℝ)`, with domain the (image of the)
Schwartz space. -/
noncomputable def schrodingerMin (hV : BoundedPotential V C volume) : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range (toL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R)
  toFun := (schrodingerAux hV).toLinearMap.comp
    (LinearEquiv.ofInjective (toL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R) toL2_injective).symm.toLinearMap

theorem schrodingerMin_domain (hV : BoundedPotential V C volume) :
    (schrodingerMin hV).domain = LinearMap.range (toL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R) := rfl

theorem schrodingerMin_apply (hV : BoundedPotential V C volume) (f : 𝓢(ℝ, ℂ))
    (hf : (toL2 f : L2R) ∈ (schrodingerMin hV).domain) :
    schrodingerMin hV ⟨toL2 f, hf⟩ = schrodingerAux hV f := by
  have hsymm : (LinearEquiv.ofInjective (toL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] L2R) toL2_injective).symm
      ⟨toL2 f, hf⟩ = f := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  show schrodingerAux hV ((LinearEquiv.ofInjective _ toL2_injective).symm ⟨toL2 f, hf⟩) = _
  rw [hsymm]

theorem mem_schrodingerMin_domain (hV : BoundedPotential V C volume) (f : 𝓢(ℝ, ℂ)) :
    (toL2 f : L2R) ∈ (schrodingerMin hV).domain := ⟨f, rfl⟩

theorem dense_schrodingerMin_domain (hV : BoundedPotential V C volume) :
    Dense ((schrodingerMin hV).domain : Set L2R) := by
  have : ((schrodingerMin hV).domain : Set L2R) = Set.range toL2 := rfl
  rw [this]
  exact denseRange_toL2

/-- Symmetry of the free part `-d²/dx²` on Schwartz functions. -/
theorem inner_neg_D2_symm (f g : 𝓢(ℝ, ℂ)) :
    ⟪toL2 (-(D2 f)), toL2 g⟫ = ⟪toL2 f, toL2 (-(D2 g))⟫ := by
  have h1 : ⟪toL2 (-(D2 f)), toL2 g⟫ = ⟪𝓕 (toL2 (-(D2 f))), 𝓕 (toL2 g)⟫ :=
    (Lp.inner_fourier_eq _ _).symm
  have h2 : ⟪toL2 f, toL2 (-(D2 g))⟫ = ⟪𝓕 (toL2 f), 𝓕 (toL2 (-(D2 g)))⟫ :=
    (Lp.inner_fourier_eq _ _).symm
  rw [h1, h2, fourier_toL2, fourier_toL2, fourier_toL2, fourier_toL2, inner_toL2, inner_toL2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [fourier_neg_D2, fourier_neg_D2]
  simp only [map_mul, Complex.conj_ofReal]
  ring

theorem schrodingerMin_isSymmetric (hV : BoundedPotential V C volume) :
    (schrodingerMin hV).IsFormalAdjoint (schrodingerMin hV) := by
  rintro x y
  obtain ⟨f, hf⟩ := x.2
  obtain ⟨g, hg⟩ := y.2
  have hx : x = ⟨toL2 f, mem_schrodingerMin_domain hV f⟩ := Subtype.ext hf.symm
  have hy : y = ⟨toL2 g, mem_schrodingerMin_domain hV g⟩ := Subtype.ext hg.symm
  rw [hx, hy, schrodingerMin_apply, schrodingerMin_apply, schrodingerAux_apply,
    schrodingerAux_apply]
  rw [inner_add_left, inner_add_right, inner_neg_D2_symm]
  congr 1
  exact hV.inner_mul_left _ _

end Schrodinger

/-! ### Weak regularity -/

theorem inner_L2_toL2 (v : L2R) (g : 𝓢(ℝ, ℂ)) :
    ⟪v, toL2 g⟫ = ∫ x, conj ((v : ℝ → ℂ) x) * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_toL2 g] with x h2
  rw [h2, RCLike.inner_apply]
  ring

/-- **Weak regularity.**  If `u, w ∈ L²(ℝ)` and `w = -u''` in the sense of distributions
(tested against Schwartz functions), then `⟪u, w⟫` is real.  On the Fourier side this is the
fact that `ŵ = (2πξ)² û`, so that `⟪u, w⟫ = ∫ (2πξ)² |û|²`. -/
theorem inner_isReal_of_weak_second_derivative (u w : L2R)
    (h : ∀ f : 𝓢(ℝ, ℂ), ⟪w, toL2 f⟫ = ⟪u, toL2 (-(D2 f))⟫) :
    conj ⟪u, w⟫ = ⟪u, w⟫ := by
  set a : ℝ → ℂ := ((𝓕 u : L2R) : ℝ → ℂ) with ha
  set b : ℝ → ℂ := ((𝓕 w : L2R) : ℝ → ℂ) with hb
  -- Step 1: on the Fourier side, `ŵ = (2πξ)² û` in the weak sense
  have key : ∀ ψ : 𝓢(ℝ, ℂ),
      ∫ x, conj (b x) * ψ x = ∫ x, conj (a x) * ((symb x : ℂ) * ψ x) := by
    intro ψ
    have hFψ : (𝓕 (𝓕⁻ ψ) : 𝓢(ℝ, ℂ)) = ψ := FourierTransform.fourier_fourierInv_eq ψ
    have hL : ⟪w, toL2 (𝓕⁻ ψ)⟫ = ∫ x, conj (b x) * ψ x := by
      rw [← Lp.inner_fourier_eq w (toL2 (𝓕⁻ ψ)), fourier_toL2, hFψ, inner_L2_toL2]
    have hR : ⟪u, toL2 (-(D2 (𝓕⁻ ψ)))⟫ = ∫ x, conj (a x) * ((symb x : ℂ) * ψ x) := by
      rw [← Lp.inner_fourier_eq u (toL2 (-(D2 (𝓕⁻ ψ)))), fourier_toL2, inner_L2_toL2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      dsimp only
      rw [fourier_neg_D2, hFψ]
    rw [← hL, ← hR, h]
  -- Step 2: local integrability of the relevant functions
  have hloc_a : LocallyIntegrable a volume := (Lp.memLp (𝓕 u)).locallyIntegrable (by norm_num)
  have hloc_b : LocallyIntegrable b volume := (Lp.memLp (𝓕 w)).locallyIntegrable (by norm_num)
  have hloc_sa : LocallyIntegrable (fun x => (symb x : ℂ) * a x) volume := by
    rw [← locallyIntegrableOn_univ] at hloc_a ⊢
    refine hloc_a.continuousOn_mul ?_ (IsClosed.isLocallyClosed isClosed_univ)
    exact (Complex.continuous_ofReal.comp continuous_symb).continuousOn
  have hF : LocallyIntegrable (fun x => b x - (symb x : ℂ) * a x) volume := hloc_b.sub hloc_sa
  -- Step 3: test against real-valued test functions
  have hzero : ∀ g : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ x, g x • (b x - (symb x : ℂ) * a x) = 0 := by
    intro g hgs hgc
    have h1 : HasCompactSupport (fun x => (g x : ℂ)) :=
      hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x => (g x : ℂ)) := Complex.ofRealCLM.contDiff.comp hgs
    set ψ : 𝓢(ℝ, ℂ) := h1.toSchwartzMap (by exact_mod_cast h2) with hψdef
    have hψ : ⇑ψ = fun x => (g x : ℂ) := rfl
    have hk := key ψ
    rw [hψ] at hk
    have hk2 : ∫ x, b x * (g x : ℂ) = ∫ x, a x * ((symb x : ℂ) * (g x : ℂ)) := by
      have hc := congrArg conj hk
      rw [← integral_conj, ← integral_conj] at hc
      simpa [map_mul, Complex.conj_ofReal] using hc
    have hint1 : Integrable (fun x => g x • b x) volume :=
      hloc_b.integrable_smul_left_of_hasCompactSupport hgs.continuous hgc
    have hint2 : Integrable (fun x => g x • ((symb x : ℂ) * a x)) volume :=
      hloc_sa.integrable_smul_left_of_hasCompactSupport hgs.continuous hgc
    simp only [smul_sub]
    rw [integral_sub hint1 hint2, sub_eq_zero]
    simp only [Complex.real_smul]
    rw [show (∫ (x : ℝ), (g x : ℂ) * b x) = ∫ (x : ℝ), b x * (g x : ℂ) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _), hk2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hF hzero
  have hbe : ∀ᵐ x : ℝ, b x = (symb x : ℂ) * a x := by
    filter_upwards [hae] with x hx
    exact sub_eq_zero.1 hx
  -- Step 4: conclude
  have hinner : ⟪u, w⟫ = ∫ x, conj (a x) * b x := by
    rw [← Lp.inner_fourier_eq u w, L2.inner_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [RCLike.inner_apply]
    ring
  rw [hinner, ← integral_conj]
  refine integral_congr_ae ?_
  filter_upwards [hbe] with x hx
  rw [hx]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-! ### The main theorem -/

section Main

variable {V : ℝ → ℝ} {C : ℝ}

/-- Elements of the deficiency space of the minimal Schrödinger operator are weak solutions of
the deficiency ODE `-u'' + V u = z u`. -/
theorem weak_deficiency_equation (hV : BoundedPotential V C volume)
    (u : (schrodingerMin hV)†.domain) (f : 𝓢(ℝ, ℂ)) :
    ⟪(schrodingerMin hV)† u - hV.mul (u : L2R), toL2 f⟫ = ⟪(u : L2R), toL2 (-(D2 f))⟫ := by
  have hadj := (adjoint_isFormalAdjoint (dense_schrodingerMin_domain hV)) u
    ⟨toL2 f, mem_schrodingerMin_domain hV f⟩
  rw [schrodingerMin_apply, schrodingerAux_apply] at hadj
  rw [inner_sub_left, hadj, inner_add_right, hV.inner_mul_left]
  ring

/-- The deficiency ODE `-u'' + V u = z u` has no nonzero `L²` solution when `z` is not real. -/
theorem deficiency_aux (hV : BoundedPotential V C volume) (u : (schrodingerMin hV)†.domain)
    (z : ℂ) (hz : z.im ≠ 0) (hu : (schrodingerMin hV)† u = z • (u : L2R)) : (u : L2R) = 0 := by
  set w : L2R := (schrodingerMin hV)† u - hV.mul (u : L2R) with hw
  have hreal : conj ⟪(u : L2R), w⟫ = ⟪(u : L2R), w⟫ :=
    inner_isReal_of_weak_second_derivative _ _ (weak_deficiency_equation hV u)
  have hval : ⟪(u : L2R), w⟫ = z * ⟪(u : L2R), (u : L2R)⟫ - ⟪(u : L2R), hV.mul (u : L2R)⟫ := by
    rw [hw, inner_sub_right, hu, inner_smul_right]
  have hconj : conj ⟪(u : L2R), w⟫
      = conj z * ⟪(u : L2R), (u : L2R)⟫ - ⟪(u : L2R), hV.mul (u : L2R)⟫ := by
    rw [hval, _root_.map_sub, map_mul, hV.inner_mul_self_isReal, inner_self_conj]
  rw [hconj, hval] at hreal
  have hzz : (conj z - z) * ⟪(u : L2R), (u : L2R)⟫ = 0 := by linear_combination hreal
  have hne : conj z - z ≠ 0 := by
    intro hcon
    apply hz
    have := sub_eq_zero.1 hcon
    have h2 : (conj z).im = z.im := by rw [this]
    rw [Complex.conj_im] at h2
    linarith
  have : ⟪(u : L2R), (u : L2R)⟫ = 0 := by
    rcases mul_eq_zero.1 hzz with h | h
    · exact absurd h hne
    · exact h
  exact inner_self_eq_zero.1 this

/-- **The minimal Schrödinger operator with a bounded measurable potential is essentially
self-adjoint.**

The hypothesis of *weak regularity* of solutions of the deficiency ODE, which is often assumed
at this point, is discharged (see `inner_isReal_of_weak_second_derivative`), so the statement is
unconditional. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity (hV : BoundedPotential V C volume) :
    IsEssentiallySelfAdjoint (schrodingerMin hV) := by
  refine isEssentiallySelfAdjoint_of_deficiency (dense_schrodingerMin_domain hV)
    (schrodingerMin_isSymmetric hV) ?_ ?_
  · intro u hu
    exact deficiency_aux hV u I (by norm_num) hu
  · intro u hu
    exact deficiency_aux hV u (-I) (by norm_num) hu

/-- The free case: `-d²/dx²` on the Schwartz space is essentially self-adjoint. -/
theorem freeLaplacian_essentiallySelfAdjoint :
    IsEssentiallySelfAdjoint (schrodingerMin (V := fun _ => (0 : ℝ)) (C := 0)
      ⟨aestronglyMeasurable_const, by filter_upwards with _; simp⟩) :=
  schrodinger_essentiallySelfAdjoint_of_weakRegularity _

end Main

end Brockian.Weyl.DeficiencyODE

