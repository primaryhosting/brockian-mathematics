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
def opGraph {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) : Submodule ℂ (E × E) :=
  LinearMap.range ((D.subtype).prod T)

lemma mem_opGraph_iff {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) (p : E × E) :
    p ∈ opGraph T ↔ ∃ x : D, ((x : E), T x) = p := by
  simp [opGraph, LinearMap.mem_range, Prod.ext_iff]

/-- The graph of the adjoint operator `T†`: the set of pairs `(u, v)` with
`⟪T x, u⟫ = ⟪x, v⟫` for all `x` in the domain of `T`. -/
def adjointGraph {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) : Submodule ℂ (E × E) where
  carrier := {p : E × E | ∀ x : D, ⟪T x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ}
  add_mem' := by
    intro p q hp hq x
    simp only [Prod.fst_add, Prod.snd_add, inner_add_right, hp x, hq x]
  zero_mem' := by intro x; simp
  smul_mem' := by
    intro c p hp x
    simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, hp x]

lemma mem_adjointGraph_iff {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) (p : E × E) :
    p ∈ adjointGraph T ↔ ∀ x : D, ⟪T x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ := Iff.rfl

/-- Symmetry of an unbounded operator on its domain. -/
def IsSymmetricOp {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) : Prop :=
  ∀ x y : D, ⟪T x, (y : E)⟫_ℂ = ⟪(x : E), T y⟫_ℂ

/-- `T` is *essentially self-adjoint* if it is densely defined and the graph of its adjoint
coincides with the closure of its graph; equivalently, the closure of `T` is self-adjoint. -/
def EssentiallySelfAdjoint {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) : Prop :=
  Dense (D : Set E) ∧ adjointGraph T = (opGraph T).topologicalClosure

/-- The adjoint graph is closed. -/
lemma isClosed_adjointGraph {D : Submodule ℂ E} (T : D →ₗ[ℂ] E) :
    IsClosed (adjointGraph T : Set (E × E)) := by
  have : (adjointGraph T : Set (E × E)) =
      ⋂ x : D, {p : E × E | ⟪T x, p.1⟫_ℂ = ⟪(x : E), p.2⟫_ℂ} := by
    ext p; simp [adjointGraph, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun x => ?_
  have h1 : Continuous fun p : E × E => ⟪T x, p.1⟫_ℂ := continuous_const.inner continuous_fst
  have h2 : Continuous fun p : E × E => ⟪(x : E), p.2⟫_ℂ := continuous_const.inner continuous_snd
  exact isClosed_eq h1 h2

lemma opGraph_le_adjointGraph {D : Submodule ℂ E} {T : D →ₗ[ℂ] E} (hsym : IsSymmetricOp T) :
    opGraph T ≤ adjointGraph T := by
  rintro p hp
  rw [mem_opGraph_iff] at hp
  obtain ⟨y, rfl⟩ := hp
  intro x
  exact hsym x y

lemma closure_opGraph_le_adjointGraph {D : Submodule ℂ E} {T : D →ₗ[ℂ] E}
    (hsym : IsSymmetricOp T) : (opGraph T).topologicalClosure ≤ adjointGraph T :=
  Submodule.topologicalClosure_minimal _ (opGraph_le_adjointGraph hsym) (isClosed_adjointGraph T)

/-! ### The basic criterion: trivial deficiency subspaces imply essential self-adjointness -/

/-- The continuous linear map `(x, y) ↦ y - i • x` on `E × E`. -/
noncomputable def defMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    (E × E) →L[ℂ] E :=
  ContinuousLinearMap.snd ℂ E E - Complex.I • ContinuousLinearMap.fst ℂ E E

@[simp] lemma defMap_apply (p : E × E) : defMap E p = p.2 - Complex.I • p.1 := rfl

/-- The basic norm identity for a symmetric operator: `‖(T - i)x‖² = ‖Tx‖² + ‖x‖²`. -/
lemma norm_sub_I_smul_sq {D : Submodule ℂ E} {T : D →ₗ[ℂ] E} (hsym : IsSymmetricOp T) (x : D) :
    ‖T x - Complex.I • (x : E)‖ ^ 2 = ‖T x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  have him : (inner ℂ (T x) (x : E) : ℂ).im = 0 := by
    have h2 : (starRingEnd ℂ) (inner ℂ (T x) (x : E)) = inner ℂ (T x) (x : E) := by
      rw [inner_conj_symm]; exact (hsym x x).symm
    exact Complex.conj_eq_iff_im.mp h2
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul]
  simp [him, Complex.I_re, Complex.I_im]

/-- On the closure of the graph, `‖x‖ ≤ ‖y - i x‖`. -/
lemma norm_fst_le_of_mem_closure {D : Submodule ℂ E} {T : D →ₗ[ℂ] E} (hsym : IsSymmetricOp T)
    {p : E × E} (hp : p ∈ (opGraph T).topologicalClosure) : ‖p.1‖ ≤ ‖defMap E p‖ := by
  have hclosed : IsClosed {q : E × E | ‖q.1‖ ≤ ‖defMap E q‖} := by
    have h1 : Continuous fun q : E × E => ‖q.1‖ := continuous_norm.comp continuous_fst
    have h2 : Continuous fun q : E × E => ‖defMap E q‖ := (defMap E).continuous.norm
    exact isClosed_le h1 h2
  have hsub : (opGraph T : Set (E × E)) ⊆ {q : E × E | ‖q.1‖ ≤ ‖defMap E q‖} := by
    rintro q hq
    rw [SetLike.mem_coe, mem_opGraph_iff] at hq
    obtain ⟨x, rfl⟩ := hq
    have hid := norm_sub_I_smul_sq hsym x
    have : ‖(x : E)‖ ^ 2 ≤ ‖T x - Complex.I • (x : E)‖ ^ 2 := by
      rw [hid]; nlinarith [sq_nonneg ‖T x‖]
    have := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (two_ne_zero)).mp this
    simpa [defMap] using this
  have hmem : p ∈ closure (opGraph T : Set (E × E)) := by
    rwa [← Submodule.topologicalClosure_coe, SetLike.mem_coe]
  exact closure_minimal hsub hclosed hmem

/-- **Basic criterion for essential self-adjointness.**  A symmetric operator whose two
deficiency subspaces are trivial is essentially self-adjoint. -/
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
noncomputable def wronskian (c : ℤ → ℂ) (n : ℤ) : ℝ := (c (n + 1) * (starRingEnd ℂ) (c n)).im

/-- Green's identity for the difference operator: the Wronskian decreases by `Im z * |c n|²`. -/
lemma wronskian_sub (q : ℤ → ℝ) (z : ℂ) (c : ℤ → ℂ)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) (n : ℤ) :
    wronskian c (n - 1) - wronskian c n = z.im * ‖c n‖ ^ 2 := by
  have hA := congrArg Complex.re (heq n)
  have hB := congrArg Complex.im (heq n)
  simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] at hA hB
  have hnorm : ‖c n‖ ^ 2 = (c n).re ^ 2 + (c n).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have h1 : n - 1 + 1 = n := by ring
  simp only [wronskian, Complex.mul_im, Complex.conj_re, Complex.conj_im, hnorm, h1]
  linear_combination (-(c n).im) * hA + (c n).re * hB

lemma abs_wronskian_le (c : ℤ → ℂ) (n : ℤ) :
    |wronskian c n| ≤ (‖c (n + 1)‖ ^ 2 + ‖c n‖ ^ 2) / 2 := by
  have h1 : |wronskian c n| ≤ ‖c (n + 1) * (starRingEnd ℂ) (c n)‖ := by
    simpa [wronskian] using Complex.abs_im_le_norm (c (n + 1) * (starRingEnd ℂ) (c n))
  have h2 : ‖c (n + 1) * (starRingEnd ℂ) (c n)‖ = ‖c (n + 1)‖ * ‖c n‖ := by
    rw [norm_mul, RCLike.norm_conj]
  nlinarith [sq_nonneg (‖c (n + 1)‖ - ‖c n‖), norm_nonneg (c (n + 1)), norm_nonneg (c n)]

lemma tendsto_wronskian (c : ℤ → ℂ) (hsum : Summable fun n => ‖c n‖ ^ 2) :
    Tendsto (wronskian c) atTop (𝓝 0) ∧ Tendsto (wronskian c) atBot (𝓝 0) := by
  have hs : Tendsto (fun n => ‖c n‖ ^ 2) cofinite (𝓝 0) := hsum.tendsto_cofinite_zero
  rw [Int.cofinite_eq] at hs
  have htop : Tendsto (fun n => ‖c n‖ ^ 2) atTop (𝓝 0) := hs.mono_left le_sup_right
  have hbot : Tendsto (fun n => ‖c n‖ ^ 2) atBot (𝓝 0) := hs.mono_left le_sup_left
  have hshift_top : Tendsto (fun n : ℤ => ‖c (n + 1)‖ ^ 2) atTop (𝓝 0) :=
    htop.comp (tendsto_atTop_add_const_right atTop 1 tendsto_id)
  have hshift_bot : Tendsto (fun n : ℤ => ‖c (n + 1)‖ ^ 2) atBot (𝓝 0) :=
    hbot.comp (tendsto_atBot_add_const_right atBot 1 tendsto_id)
  refine ⟨squeeze_zero_norm (fun n => abs_wronskian_le c n) ?_,
    squeeze_zero_norm (fun n => abs_wronskian_le c n) ?_⟩
  · simpa using ((hshift_top.add htop).div_const 2)
  · simpa using ((hshift_bot.add hbot).div_const 2)

/-- Auxiliary version of the vanishing theorem for `Im z > 0`. -/
lemma deficiency_solution_eq_zero_of_im_pos (q : ℤ → ℝ) (z : ℂ) (hz : 0 < z.im) (c : ℤ → ℂ)
    (hsum : Summable fun n => ‖c n‖ ^ 2)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) : ∀ n, c n = 0 := by
  have hkey := wronskian_sub q z c heq
  have hstep : ∀ n : ℤ, wronskian c n ≤ wronskian c (n - 1) := by
    intro n
    have h := hkey n
    nlinarith [sq_nonneg ‖c n‖]
  have hanti : ∀ m n : ℤ, m ≤ n → wronskian c n ≤ wronskian c m := by
    intro m n hmn
    induction n, hmn using Int.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
        have h := hstep (n + 1)
        simp only [add_sub_cancel_right] at h
        linarith
  obtain ⟨htop, hbot⟩ := tendsto_wronskian c hsum
  have hnonneg : ∀ n, 0 ≤ wronskian c n := by
    intro n
    refine le_of_tendsto htop ?_
    filter_upwards [eventually_ge_atTop n] with m hm using hanti n m hm
  have hnonpos : ∀ n, wronskian c n ≤ 0 := by
    intro n
    refine ge_of_tendsto hbot ?_
    filter_upwards [eventually_le_atBot n] with m hm using hanti m n hm
  intro n
  have h := hkey n
  rw [le_antisymm (hnonpos _) (hnonneg _), le_antisymm (hnonpos _) (hnonneg _)] at h
  have h0 : z.im * ‖c n‖ ^ 2 = 0 := by linarith
  have : ‖c n‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 (ne_of_gt hz)
    · exact h1
  simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- **No nonzero `ℓ²` solutions of the deficiency equation.**  For a non-real spectral parameter
`z` and an arbitrary real potential `q`, the second order difference equation
`q n * c n - c (n+1) - c (n-1) = z * c n` has no nonzero square-summable solution. -/
lemma deficiency_solution_eq_zero (q : ℤ → ℝ) (z : ℂ) (hz : z.im ≠ 0) (c : ℤ → ℂ)
    (hsum : Summable fun n => ‖c n‖ ^ 2)
    (heq : ∀ n, (q n : ℂ) * c n - c (n + 1) - c (n - 1) = z * c n) : ∀ n, c n = 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · -- pass to the complex conjugate solution
    set c' : ℤ → ℂ := fun n => (starRingEnd ℂ) (c n) with hc'
    have hsum' : Summable fun n => ‖c' n‖ ^ 2 := by simpa [hc'] using hsum
    have heq' : ∀ n, (q n : ℂ) * c' n - c' (n + 1) - c' (n - 1) = ((starRingEnd ℂ) z) * c' n := by
      intro n
      have := congrArg (starRingEnd ℂ) (heq n)
      simpa [hc', map_sub, map_mul, Complex.conj_ofReal] using this
    have him : 0 < ((starRingEnd ℂ) z).im := by
      simpa [Complex.conj_im] using hneg
    intro n
    have := deficiency_solution_eq_zero_of_im_pos q _ him c' hsum' heq' n
    simpa [hc'] using congrArg (starRingEnd ℂ) this
  · exact deficiency_solution_eq_zero_of_im_pos q z hpos c hsum heq

/-!
## The discrete Schrödinger operator

We realise the one-dimensional Schrödinger operator `H = -Δ + V` on `ℓ²(ℤ)` (equivalently, on any
complex Hilbert space equipped with a Hilbert basis indexed by `ℤ`), defined on the dense domain
of finitely supported vectors, i.e. the algebraic span of the basis:
`H e n = 2 e n - e (n+1) - e (n-1) + V n • e n`.
The potential `V` is an arbitrary real-valued function; no regularity is assumed.
-/

/-- The action of the discrete Schrödinger operator `-Δ + V` on the `n`-th basis vector. -/
noncomputable def schrodingerBasisImage (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (n : ℤ) : E :=
  ((2 : ℂ) + (V n : ℂ)) • b n - b (n + 1) - b (n - 1)

/-- The domain of the Schrödinger operator: the algebraic span of the basis vectors
(the finitely supported vectors). -/
def schrodingerDomain (b : HilbertBasis ℤ ℂ E) : Submodule ℂ E := Submodule.span ℂ (Set.range b)

/-- The `ℤ`-indexed basis of the domain. -/
noncomputable def domBasis (b : HilbertBasis ℤ ℂ E) :
    Module.Basis ℤ ℂ (schrodingerDomain b) :=
  Module.Basis.span b.orthonormal.linearIndependent

@[simp] lemma coe_domBasis (b : HilbertBasis ℤ ℂ E) (n : ℤ) : ((domBasis b n : E)) = b n :=
  Module.Basis.span_apply _ n

/-- The discrete Schrödinger operator `-Δ + V` on its dense domain. -/
noncomputable def schrodingerOp (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) :
    schrodingerDomain b →ₗ[ℂ] E :=
  (domBasis b).constr ℂ (schrodingerBasisImage b V)

@[simp] lemma schrodingerOp_basis (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (n : ℤ) :
    schrodingerOp b V (domBasis b n) = schrodingerBasisImage b V n :=
  Module.Basis.constr_basis _ _ _ _

lemma dense_schrodingerDomain (b : HilbertBasis ℤ ℂ E) :
    Dense (schrodingerDomain b : Set E) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span

lemma inner_basis (b : HilbertBasis ℤ ℂ E) (i j : ℤ) :
    ⟪b i, b j⟫_ℂ = if i = j then 1 else 0 :=
  orthonormal_iff_ite.mp b.orthonormal i j

/-- Symmetry on pairs of basis vectors. -/
lemma schrodinger_symm_basis (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (m n : ℤ) :
    ⟪schrodingerBasisImage b V m, b n⟫_ℂ = ⟪b m, schrodingerBasisImage b V n⟫_ℂ := by
  simp only [schrodingerBasisImage, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, inner_basis, map_add, map_ofNat, Complex.conj_ofReal]
  by_cases h1 : m = n
  · subst h1
    simp [show (m : ℤ) ≠ m - 1 by omega, show (m : ℤ) ≠ m + 1 by omega,
      show ¬ (m + 1 = m) by omega, show ¬ (m - 1 = m) by omega]
  · have h4 : (m + 1 = n) ↔ (m = n - 1) := by omega
    have h5 : (m - 1 = n) ↔ (m = n + 1) := by omega
    simp only [h1, h4, h5, if_false]
    by_cases h6 : m = n - 1 <;> by_cases h7 : m = n + 1 <;> simp_all

/-- The Schrödinger operator is symmetric on its domain. -/
lemma schrodinger_isSymmetric (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) :
    IsSymmetricOp (schrodingerOp b V) := by
  -- first: symmetry when the left argument is a basis vector
  have step2 : ∀ (m : ℤ) (y : schrodingerDomain b),
      ⟪schrodingerOp b V (domBasis b m), (y : E)⟫_ℂ
        = ⟪(b m : E), schrodingerOp b V y⟫_ℂ := by
    intro m
    have hfg : ((innerSL ℂ (schrodingerOp b V (domBasis b m))).toLinearMap ∘ₗ
          (schrodingerDomain b).subtype : schrodingerDomain b →ₗ[ℂ] ℂ) =
        ((innerSL ℂ (b m)).toLinearMap ∘ₗ schrodingerOp b V :
          schrodingerDomain b →ₗ[ℂ] ℂ) := by
      refine (domBasis b).ext fun n => ?_
      simpa using schrodinger_symm_basis b V m n
    intro y
    simpa using LinearMap.congr_fun hfg y
  intro x y
  have hfg : ((innerSL ℂ ((y : E))).toLinearMap ∘ₗ schrodingerOp b V :
        schrodingerDomain b →ₗ[ℂ] ℂ) =
      ((innerSL ℂ (schrodingerOp b V y)).toLinearMap ∘ₗ (schrodingerDomain b).subtype :
        schrodingerDomain b →ₗ[ℂ] ℂ) := by
    refine (domBasis b).ext fun m => ?_
    have h := step2 m y
    have h' : ⟪(y : E), schrodingerOp b V (domBasis b m)⟫_ℂ = ⟪schrodingerOp b V y, (b m : E)⟫_ℂ := by
      rw [← inner_conj_symm ((y : E)), h, inner_conj_symm]
    simpa using h'
  have h2 : ⟪(y : E), schrodingerOp b V x⟫_ℂ = ⟪schrodingerOp b V y, (x : E)⟫_ℂ := by
    simpa using LinearMap.congr_fun hfg x
  rw [← inner_conj_symm (schrodingerOp b V x), h2, inner_conj_symm]

/-- Square-summability of the coefficients of a vector in a Hilbert basis. -/
lemma summable_repr_sq (b : HilbertBasis ℤ ℂ E) (u : E) :
    Summable fun n => ‖b.repr u n‖ ^ 2 := by
  have h := lp.memℓp (b.repr u)
  rw [Memℓp] at h
  simp at h
  convert h using 2 with n

/-- **Triviality of the deficiency subspaces.**  For any non-real `z`, a vector `u` with
`⟪H x, u⟫ = z ⟪x, u⟫` for all `x` in the domain vanishes.  This is where the deficiency
difference equation ('deficiency ODE') is solved. -/
lemma schrodinger_deficiency_trivial (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) (z : ℂ) (hz : z.im ≠ 0)
    (u : E) (hu : ∀ x : schrodingerDomain b,
      ⟪schrodingerOp b V x, u⟫_ℂ = z * ⟪(x : E), u⟫_ℂ) : u = 0 := by
  have hrepr : ∀ n : ℤ, b.repr u n = ⟪b n, u⟫_ℂ := fun n => b.repr_apply_apply u n
  have hsum : Summable fun n => ‖b.repr u n‖ ^ 2 := summable_repr_sq b u
  have heq : ∀ n : ℤ, (((2 + V n : ℝ)) : ℂ) * b.repr u n - b.repr u (n + 1) - b.repr u (n - 1)
      = z * b.repr u n := by
    intro n
    have h := hu (domBasis b n)
    rw [schrodingerOp_basis, coe_domBasis] at h
    simp only [schrodingerBasisImage, inner_sub_left, inner_smul_left, map_add, map_ofNat,
      Complex.conj_ofReal] at h
    simp only [hrepr]
    push_cast
    linear_combination h
  have hzero := deficiency_solution_eq_zero (fun n => 2 + V n) z hz (fun n => b.repr u n) hsum heq
  have : b.repr u = 0 := by ext n; simpa using hzero n
  simpa using congrArg b.repr.symm this

/-- **Essential self-adjointness of the one-dimensional Schrödinger operator `-Δ + V`
(discrete model) for an arbitrary real potential.**

The named `weakRegularity` hypothesis on the potential has been discharged: the statement is
unconditional, the potential `V : ℤ → ℝ` being an arbitrary real-valued function.  The operator
is defined on the dense domain of finitely supported vectors and is essentially self-adjoint,
i.e. the graph of its adjoint is exactly the closure of its graph (equivalently, its closure is
self-adjoint).  The proof follows Weyl's deficiency argument: symmetry plus the fact that the
deficiency equation `H c = ± i c` has no nonzero `ℓ²` solution (a Wronskian/Green identity
computation, the limit point case). -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity [CompleteSpace E]
    (b : HilbertBasis ℤ ℂ E) (V : ℤ → ℝ) :
    EssentiallySelfAdjoint (schrodingerOp b V) :=
  essentiallySelfAdjoint_of_deficiency_trivial (dense_schrodingerDomain b)
    (schrodinger_isSymmetric b V)
    (fun u hu => schrodinger_deficiency_trivial b V (-Complex.I) (by simp) u
      (fun x => by simpa using hu x))
    (fun u hu => schrodinger_deficiency_trivial b V Complex.I (by simp) u
      (fun x => by simpa using hu x))

/-! ### The concrete model: `ℓ²(ℤ)` -/

/-- The standard Hilbert basis of `ℓ²(ℤ)`. -/
noncomputable def l2Basis : HilbertBasis ℤ ℂ (lp (fun _ : ℤ => ℂ) 2) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Essential self-adjointness of the discrete Schrödinger operator `-Δ + V` on `ℓ²(ℤ)`,
defined on the finitely supported vectors, for an arbitrary real potential `V`. -/
theorem schrodinger_l2_essentiallySelfAdjoint (V : ℤ → ℝ) :
    EssentiallySelfAdjoint (schrodingerOp l2Basis V) :=
  schrodinger_essentiallySelfAdjoint_of_weakRegularity l2Basis V

end Brockian.Weyl.DeficiencyODE

