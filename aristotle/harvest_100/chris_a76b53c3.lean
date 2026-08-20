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

open scoped InnerProductSpace
open scoped NNReal

namespace Brockian.Weyl.DeficiencyODE

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- An (in general unbounded) linear operator on a Hilbert space `H` is encoded by its graph,
a linear subspace of `H × H`. -/
abbrev OperatorGraph (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Submodule ℂ (H × H)

/-- The graph of the adjoint of the operator with graph `G`:
`(u, v)` belongs to it iff `⟪T x, u⟫ = ⟪x, v⟫` for all `(x, T x) ∈ G`. -/
def adjointGraph (G : OperatorGraph H) : OperatorGraph H where
  carrier := {p : H × H | ∀ q ∈ G, ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ}
  add_mem' := by
    intro a b ha hb q hq
    simp [ha q hq, hb q hq]
  zero_mem' := by intro q _; simp
  smul_mem' := by
    intro c a ha q hq
    simp [ha q hq]

lemma mem_adjointGraph_iff {G : OperatorGraph H} {p : H × H} :
    p ∈ adjointGraph G ↔ ∀ q ∈ G, ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ := Iff.rfl

/-- A graph is symmetric when the operator it encodes is contained in its adjoint. -/
def IsSymmetricGraph (G : OperatorGraph H) : Prop := G ≤ adjointGraph G

/-- The operator with graph `G` is essentially self-adjoint when the closure of its graph
is the graph of its adjoint. -/
def EssentiallySelfAdjoint (G : OperatorGraph H) : Prop :=
  G.topologicalClosure = adjointGraph G

/-- The continuous linear map `(x, y) ↦ y + c • x` on `H × H`. -/
def shiftMap (c : ℂ) : (H × H) →L[ℂ] H :=
  ContinuousLinearMap.snd ℂ H H + c • ContinuousLinearMap.fst ℂ H H

@[simp] lemma shiftMap_apply (c : ℂ) (p : H × H) : shiftMap c p = p.2 + c • p.1 := rfl

/-- The deficiency range `ran (T + c)` of the operator with graph `G`. -/
def defRange (c : ℂ) (G : OperatorGraph H) : Submodule ℂ H :=
  G.map (shiftMap c : (H × H) →L[ℂ] H).toLinearMap

lemma mem_defRange_iff {c : ℂ} {G : OperatorGraph H} {z : H} :
    z ∈ defRange c G ↔ ∃ p ∈ G, p.2 + c • p.1 = z := by
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p, hp, rfl⟩

/-! ### Basic properties of the adjoint graph -/

lemma adjointGraph_isClosed (G : OperatorGraph H) :
    IsClosed ((adjointGraph G : OperatorGraph H) : Set (H × H)) := by
  have hset : ((adjointGraph G : OperatorGraph H) : Set (H × H))
      = ⋂ q ∈ (G : Set (H × H)), {p : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro q hq
      exact hp q hq
    · intro hp q hq
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hp
      exact hp q hq
  rw [hset]
  refine isClosed_iInter fun q => isClosed_iInter fun _ => isClosed_eq ?_ ?_
  · exact continuous_const.inner continuous_fst
  · exact continuous_const.inner continuous_snd

lemma adjointGraph_antitone {G₁ G₂ : OperatorGraph H} (h : G₁ ≤ G₂) :
    adjointGraph G₂ ≤ adjointGraph G₁ := fun _ hp q hq => hp q (h hq)

lemma adjoint_rel_symm (p q : H × H) :
    (⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ) ↔ (⟪p.2, q.1⟫_ℂ = ⟪p.1, q.2⟫_ℂ) := by
  constructor
  · intro hpq
    have := congrArg (starRingEnd ℂ) hpq
    rw [inner_conj_symm, inner_conj_symm] at this
    exact this.symm
  · intro hpq
    have := congrArg (starRingEnd ℂ) hpq
    rw [inner_conj_symm, inner_conj_symm] at this
    exact this.symm

lemma closure_le_adjointGraph {G : OperatorGraph H} (h : IsSymmetricGraph G) :
    G.topologicalClosure ≤ adjointGraph G :=
  Submodule.topologicalClosure_minimal G h (adjointGraph_isClosed G)

lemma isSymmetricGraph_topologicalClosure {G : OperatorGraph H} (h : IsSymmetricGraph G) :
    IsSymmetricGraph G.topologicalClosure := by
  have h1 : G.topologicalClosure ≤ adjointGraph G := closure_le_adjointGraph h
  have h2 : G ≤ adjointGraph G.topologicalClosure := by
    intro p hp q hq
    exact (adjoint_rel_symm p q).mpr (h1 hq p hp)
  exact Submodule.topologicalClosure_minimal G h2 (adjointGraph_isClosed _)

/-! ### The basic norm identity for symmetric operators -/

/-- The **basic identity** `‖T x + c x‖² = ‖T x‖² + |c|² ‖x‖²` valid for a symmetric operator `T`
and a purely imaginary number `c`. -/
lemma norm_shift_sq {G : OperatorGraph H} (hsym : IsSymmetricGraph G) {p : H × H} (hp : p ∈ G)
    {c : ℂ} (hc : c.re = 0) :
    ‖p.2 + c • p.1‖ ^ 2 = ‖p.2‖ ^ 2 + ‖c‖ ^ 2 * ‖p.1‖ ^ 2 := by
  have hre : ⟪p.2, p.1⟫_ℂ = ⟪p.1, p.2⟫_ℂ := hsym hp p hp
  have hconj : (starRingEnd ℂ) ⟪p.2, p.1⟫_ℂ = ⟪p.2, p.1⟫_ℂ := by
    rw [inner_conj_symm]; exact hre.symm
  have him : (⟪p.2, p.1⟫_ℂ).im = 0 := by
    have h2 := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h2
    linarith
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have hzero : RCLike.re (c * ⟪p.2, p.1⟫_ℂ) = 0 := by
    simp [hc, him]
  rw [hzero]
  ring

lemma norm_le_norm_shift {G : OperatorGraph H} (hsym : IsSymmetricGraph G) {p : H × H} (hp : p ∈ G)
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    ‖p‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
  have h := norm_shift_sq hsym hp hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hMpos : (0 : ℝ) ≤ max 1 ‖c‖⁻¹ := le_trans zero_le_one (le_max_left _ _)
  have hM1 : (1 : ℝ) ≤ max 1 ‖c‖⁻¹ := le_max_left _ _
  have hM2 : ‖c‖⁻¹ ≤ max 1 ‖c‖⁻¹ := le_max_right _ _
  have hN : 0 ≤ ‖p.2 + c • p.1‖ := norm_nonneg _
  have h1 : ‖p.1‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
    have hkey : ‖c‖ * ‖p.1‖ ≤ ‖p.2 + c • p.1‖ := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2]
    have : ‖p.1‖ ≤ ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
      rw [inv_mul_eq_div, le_div_iff₀ hcpos]
      linarith [hkey, mul_comm ‖c‖ ‖p.1‖]
    nlinarith
  have h2 : ‖p.2‖ ≤ max 1 ‖c‖⁻¹ * ‖p.2 + c • p.1‖ := by
    have : ‖p.2‖ ≤ ‖p.2 + c • p.1‖ := by
      nlinarith [norm_nonneg p.1, norm_nonneg p.2, sq_nonneg ‖c‖]
    nlinarith
  rw [Prod.norm_def]
  exact max_le h1 h2

/-! ### Closed range of the deficiency shifts -/

/-- For a *closed* symmetric operator and a nonzero purely imaginary `c`, the deficiency range
`ran (T + c)` is closed. -/
lemma isClosed_defRange [CompleteSpace H] {K : OperatorGraph H} (hKsym : IsSymmetricGraph K)
    (hKclosed : IsClosed (K : Set (H × H))) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    IsClosed ((defRange c K : Submodule ℂ H) : Set H) := by
  classical
  haveI : CompleteSpace K := hKclosed.completeSpace_coe
  set f : K → H := fun p => ((p : H × H).2 + c • (p : H × H).1) with hf
  set M : ℝ≥0 := Real.toNNReal (max 1 ‖c‖⁻¹) with hM
  have hMcoe : (M : ℝ) = max 1 ‖c‖⁻¹ :=
    Real.coe_toNNReal _ (le_trans zero_le_one (le_max_left _ _))
  have hanti : AntilipschitzWith M f := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro x y
    have hmem : ((x : H × H) - (y : H × H)) ∈ K := K.sub_mem x.2 y.2
    have hle := norm_le_norm_shift hKsym hmem hc hc0
    have hEq : f x - f y = ((x : H × H) - (y : H × H)).2
        + c • ((x : H × H) - (y : H × H)).1 := by
      simp only [hf, Prod.fst_sub, Prod.snd_sub, smul_sub]
      abel
    have hdist : dist x y = ‖(x : H × H) - (y : H × H)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    rw [hdist, dist_eq_norm, hEq, hMcoe]
    exact hle
  have huc : UniformContinuous f := by
    have hfeq : f = fun p : K => (shiftMap c) ((p : H × H)) := rfl
    rw [hfeq]
    exact (shiftMap c : (H × H) →L[ℂ] H).uniformContinuous.comp uniformContinuous_subtype_val
  have hclosedRange : IsClosed (Set.range f) := (hanti.isComplete_range huc).isClosed
  have hsets : Set.range f = ((defRange c K : Submodule ℂ H) : Set H) := by
    ext z
    constructor
    · rintro ⟨p, rfl⟩
      exact mem_defRange_iff.mpr ⟨(p : H × H), p.2, rfl⟩
    · intro hz
      obtain ⟨p, hp, rfl⟩ := mem_defRange_iff.mp hz
      exact ⟨⟨p, hp⟩, rfl⟩
  rwa [hsets] at hclosedRange

lemma defRange_closure_eq_top [CompleteSpace H] {G : OperatorGraph H} (hsym : IsSymmetricGraph G)
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0)
    (hd : Dense ((defRange c G : Submodule ℂ H) : Set H)) :
    defRange c G.topologicalClosure = ⊤ := by
  have hclosedRange : IsClosed ((defRange c G.topologicalClosure : Submodule ℂ H) : Set H) :=
    isClosed_defRange (isSymmetricGraph_topologicalClosure hsym) G.isClosed_topologicalClosure
      hc hc0
  have hsubset : ((defRange c G : Submodule ℂ H) : Set H)
      ⊆ ((defRange c G.topologicalClosure : Submodule ℂ H) : Set H) := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := mem_defRange_iff.mp hz
    exact mem_defRange_iff.mpr ⟨p, Submodule.le_topologicalClosure G hp, rfl⟩
  have huniv : (Set.univ : Set H) ⊆ ((defRange c G.topologicalClosure : Submodule ℂ H) : Set H) := by
    rw [← hd.closure_eq]
    exact hclosedRange.closure_subset_iff.mpr hsubset
  refine eq_top_iff.mpr ?_
  intro z _
  exact huniv (Set.mem_univ z)

/-! ### The basic criterion for essential self-adjointness -/

/-- **Basic criterion (von Neumann).** A symmetric operator both of whose deficiency ranges
`ran (T + c)` and `ran (T - c)` are dense, for some nonzero purely imaginary `c` (e.g. `c = i`),
is essentially self-adjoint. -/
theorem essentiallySelfAdjoint_of_defRange_dense [CompleteSpace H] {G : OperatorGraph H}
    (hsym : IsSymmetricGraph G) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0)
    (hplus : Dense ((defRange c G : Submodule ℂ H) : Set H))
    (hminus : Dense ((defRange (-c) G : Submodule ℂ H) : Set H)) :
    EssentiallySelfAdjoint G := by
  refine le_antisymm (closure_le_adjointGraph hsym) ?_
  intro p hp
  obtain ⟨q, hq, hqeq⟩ : ∃ q ∈ G.topologicalClosure,
      q.2 + (-c) • q.1 = p.2 + (-c) • p.1 := by
    have htop := defRange_closure_eq_top hsym (by simpa using hc) (neg_ne_zero.mpr hc0) hminus
    have hmem : (p.2 + (-c) • p.1) ∈ defRange (-c) G.topologicalClosure := by
      rw [htop]; trivial
    exact mem_defRange_iff.mp hmem
  set a : H × H := p - q with ha
  have ha2 : a.2 = c • a.1 := by
    have h := hqeq
    simp only [neg_smul] at h
    have hkey : p.2 - q.2 = c • (p.1 - q.1) := by
      rw [smul_sub]
      linear_combination (norm := module) -h
    simpa [ha] using hkey
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  have haadj : a ∈ adjointGraph G :=
    (adjointGraph G).sub_mem hp (closure_le_adjointGraph hsym hq)
  have ha1 : a.1 = 0 := by
    have horth : ((defRange c G : Submodule ℂ H) : Set H)
        ⊆ {z : H | ⟪z, a.1⟫_ℂ = 0} := by
      intro z hz
      obtain ⟨r, hr, rfl⟩ := mem_defRange_iff.mp hz
      have h1 : ⟪r.2, a.1⟫_ℂ = c * ⟪r.1, a.1⟫_ℂ := by
        have := haadj r hr
        rw [ha2, inner_smul_right] at this
        exact this
      simp only [Set.mem_setOf_eq, inner_add_left, inner_smul_left, h1, hconjc]
      ring
    have hclosed : IsClosed {z : H | ⟪z, a.1⟫_ℂ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hall : ∀ z : H, ⟪z, a.1⟫_ℂ = 0 := by
      intro z
      have hsub : (Set.univ : Set H) ⊆ {z : H | ⟪z, a.1⟫_ℂ = 0} := by
        rw [← hplus.closure_eq]
        exact hclosed.closure_subset_iff.mpr horth
      exact hsub (Set.mem_univ z)
    exact inner_self_eq_zero.mp (hall a.1)
  have ha0 : a = 0 := by
    have : a.2 = 0 := by rw [ha2, ha1, smul_zero]
    exact Prod.ext ha1 this
  have : p = q := by
    have := ha0
    rw [ha, sub_eq_zero] at this
    exact this
  rw [this]
  exact hq

/-! ### Bounded symmetric operators restricted to a dense core -/

/-- The graph of the bounded operator `S` restricted to the subspace `D`. -/
def opGraph (S : H →L[ℂ] H) (D : Submodule ℂ H) : OperatorGraph H where
  carrier := {p : H × H | p.1 ∈ D ∧ p.2 = S p.1}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨D.add_mem ha hb, by simp [Prod.fst_add, Prod.snd_add, ha', hb']⟩
  zero_mem' := ⟨D.zero_mem, by simp⟩
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    exact ⟨D.smul_mem c ha, by simp [ha']⟩

@[simp] lemma mem_opGraph_iff {S : H →L[ℂ] H} {D : Submodule ℂ H} {p : H × H} :
    p ∈ opGraph S D ↔ p.1 ∈ D ∧ p.2 = S p.1 := Iff.rfl

lemma isSymmetricGraph_opGraph {S : H →L[ℂ] H} (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ)
    (D : Submodule ℂ H) : IsSymmetricGraph (opGraph S D) := by
  rintro p ⟨-, hp⟩ q ⟨-, hq⟩
  rw [hp, hq]
  exact hS q.1 p.1

/-- For a bounded symmetric operator `S` and `c = ± i`, the deficiency range `ran (S + c)`
restricted to a dense core is dense. -/
lemma dense_defRange_opGraph [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) {D : Submodule ℂ H} (hD : Dense (D : Set H))
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    Dense ((defRange c (opGraph S D) : Submodule ℂ H) : Set H) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro z hz
  have hzero : ∀ x : H, ⟪S x + c • x, z⟫_ℂ = 0 := by
    have hclosed : IsClosed {x : H | ⟪S x + c • x, z⟫_ℂ = 0} :=
      isClosed_eq (((S.continuous).add (continuous_const_smul c)).inner continuous_const)
        continuous_const
    have hsub : (D : Set H) ⊆ {x : H | ⟪S x + c • x, z⟫_ℂ = 0} := by
      intro x hx
      exact hz _ (mem_defRange_iff.mpr ⟨(x, S x), ⟨hx, rfl⟩, rfl⟩)
    intro x
    have huniv : (Set.univ : Set H) ⊆ {x : H | ⟪S x + c • x, z⟫_ℂ = 0} := by
      rw [← hD.closure_eq]
      exact hclosed.closure_subset_iff.mpr hsub
    exact huniv (Set.mem_univ x)
  have hzz := hzero z
  rw [inner_add_left, inner_smul_left] at hzz
  have hreal : (⟪S z, z⟫_ℂ).im = 0 := by
    have hconj : (starRingEnd ℂ) ⟪S z, z⟫_ℂ = ⟪S z, z⟫_ℂ := by
      rw [inner_conj_symm]; exact (hS z z).symm
    have h2 := congrArg Complex.im hconj
    simp only [Complex.conj_im] at h2
    linarith
  have hnormsq : ⟪z, z⟫_ℂ = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  rw [hnormsq] at hzz
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  rw [hconjc] at hzz
  have hcim : c.im ≠ 0 := by
    intro h
    exact hc0 (Complex.ext hc h)
  have him := congrArg Complex.im hzz
  simp only [Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im, hreal] at him
  have hnorm2 : (‖z‖ : ℝ) ^ 2 = 0 := by
    rcases lt_or_gt_of_ne hcim with h | h <;> nlinarith [him]
  have hz0 : ‖z‖ = 0 := by nlinarith [norm_nonneg z]
  exact norm_eq_zero.mp hz0

/-- A bounded symmetric operator is essentially self-adjoint on any dense core. -/
theorem essentiallySelfAdjoint_opGraph [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    EssentiallySelfAdjoint (opGraph S D) :=
  essentiallySelfAdjoint_of_defRange_dense (isSymmetricGraph_opGraph hS D)
    (c := Complex.I) (by simp) Complex.I_ne_zero
    (dense_defRange_opGraph hS hD (by simp) Complex.I_ne_zero)
    (dense_defRange_opGraph hS hD (by simp) (by simp))

/-- The adjoint of a bounded symmetric operator restricted to a dense core is the operator
itself, defined on all of `H`. -/
lemma adjointGraph_opGraph {S : H →L[ℂ] H} (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ)
    {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    adjointGraph (opGraph S D) = opGraph S ⊤ := by
  refine le_antisymm ?_ ?_
  · intro p hp
    refine ⟨Submodule.mem_top, ?_⟩
    have hall : ∀ x : H, ⟪x, S p.1 - p.2⟫_ℂ = 0 := by
      have hclosed : IsClosed {x : H | ⟪x, S p.1 - p.2⟫_ℂ = 0} :=
        isClosed_eq (continuous_id.inner continuous_const) continuous_const
      have hsub : (D : Set H) ⊆ {x : H | ⟪x, S p.1 - p.2⟫_ℂ = 0} := by
        intro x hx
        have h1 : ⟪S x, p.1⟫_ℂ = ⟪x, p.2⟫_ℂ := hp (x, S x) ⟨hx, rfl⟩
        rw [hS x p.1] at h1
        simp only [Set.mem_setOf_eq, inner_sub_right, h1, sub_self]
      intro x
      have huniv := hclosed.closure_subset_iff.mpr hsub
      rw [hD.closure_eq] at huniv
      exact huniv (Set.mem_univ x)
    have h2 : S p.1 - p.2 = 0 := inner_self_eq_zero.mp (hall (S p.1 - p.2))
    exact (sub_eq_zero.mp h2).symm
  · intro p hp q hq
    rw [hp.2, hq.2]
    exact hS q.1 p.1

/-- For a bounded symmetric operator on a dense core, the closure of the graph is the graph of
the everywhere-defined operator; in particular the criterion above is not vacuous. -/
lemma topologicalClosure_opGraph [CompleteSpace H] {S : H →L[ℂ] H}
    (hS : ∀ x y : H, ⟪S x, y⟫_ℂ = ⟪x, S y⟫_ℂ) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    (opGraph S D).topologicalClosure = opGraph S ⊤ := by
  rw [essentiallySelfAdjoint_opGraph hS hD, adjointGraph_opGraph hS hD]

/-! ### Bounded perturbations of essentially self-adjoint operators (Kato–Rellich) -/

/-- The adjoint only depends on the closure of the graph. -/
lemma adjointGraph_topologicalClosure (G : OperatorGraph H) :
    adjointGraph G.topologicalClosure = adjointGraph G := by
  refine le_antisymm (adjointGraph_antitone (Submodule.le_topologicalClosure G)) ?_
  intro p hp
  have hclosed : IsClosed {q : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hsub : (G : Set (H × H)) ⊆ {q : H × H | ⟪q.2, p.1⟫_ℂ = ⟪q.1, p.2⟫_ℂ} := fun q hq => hp q hq
  intro q hq
  have hmem : q ∈ closure (G : Set (H × H)) := by
    simpa [Submodule.topologicalClosure_coe] using hq
  exact hclosed.closure_subset_iff.mpr hsub hmem

/-- A graph is self-adjoint when it agrees with the graph of its adjoint. -/
def IsSelfAdjointGraph (K : OperatorGraph H) : Prop := adjointGraph K = K

lemma IsSelfAdjointGraph.isSymmetric {K : OperatorGraph H} (hK : IsSelfAdjointGraph K) :
    IsSymmetricGraph K := by
  rw [IsSelfAdjointGraph] at hK
  rw [IsSymmetricGraph, hK]

lemma IsSelfAdjointGraph.isClosed {K : OperatorGraph H} (hK : IsSelfAdjointGraph K) :
    IsClosed ((K : OperatorGraph H) : Set (H × H)) := by
  rw [← hK]
  exact adjointGraph_isClosed K

/-- The closure of an essentially self-adjoint operator is self-adjoint. -/
lemma isSelfAdjointGraph_topologicalClosure {G : OperatorGraph H} (h : EssentiallySelfAdjoint G) :
    IsSelfAdjointGraph G.topologicalClosure := by
  rw [IsSelfAdjointGraph, adjointGraph_topologicalClosure, h]

/-- For a self-adjoint operator and a nonzero purely imaginary `c`, `T + c` is surjective. -/
lemma defRange_eq_top_of_isSelfAdjointGraph [CompleteSpace H] {K : OperatorGraph H}
    (hK : IsSelfAdjointGraph K) {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) :
    defRange c K = ⊤ := by
  have hsym : IsSymmetricGraph K := hK.isSymmetric
  have hKclosed : IsClosed ((K : OperatorGraph H) : Set (H × H)) := hK.isClosed
  have hconjc : (starRingEnd ℂ) c = -c := by
    apply Complex.ext <;> simp [hc]
  have hrangeClosed : IsClosed ((defRange c K : Submodule ℂ H) : Set H) :=
    isClosed_defRange hsym hKclosed hc hc0
  have hdense : Dense ((defRange c K : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro z hz
    have hmem : ((z, c • z) : H × H) ∈ adjointGraph K := by
      intro q hq
      have h0 : ⟪q.2 + c • q.1, z⟫_ℂ = 0 := hz _ (mem_defRange_iff.mpr ⟨q, hq, rfl⟩)
      rw [inner_add_left, inner_smul_left, hconjc] at h0
      show ⟪q.2, z⟫_ℂ = ⟪q.1, c • z⟫_ℂ
      rw [inner_smul_right]
      linear_combination h0
    rw [hK] at hmem
    have hsymz := hsym hmem ((z, c • z) : H × H) hmem
    simp only [inner_smul_left, inner_smul_right, hconjc] at hsymz
    have h2 : (2 * c) * ⟪z, z⟫_ℂ = 0 := by linear_combination -hsymz
    have hc2 : (2 : ℂ) * c ≠ 0 := by
      simp [hc0]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hc2
    · exact inner_self_eq_zero.mp h
  have hall : ((defRange c K : Submodule ℂ H) : Set H) = Set.univ := by
    rw [← hdense.closure_eq, hrangeClosed.closure_eq]
  refine eq_top_iff.mpr ?_
  intro z _
  have : z ∈ ((defRange c K : Submodule ℂ H) : Set H) := by rw [hall]; trivial
  exact this

/-- The map `(x, y) ↦ (x, y + V x)` implementing the perturbation of an operator by a bounded
operator `V`. -/
def perturbMap (V : H →L[ℂ] H) : (H × H) →L[ℂ] (H × H) :=
  (ContinuousLinearMap.fst ℂ H H).prod
    (ContinuousLinearMap.snd ℂ H H + V.comp (ContinuousLinearMap.fst ℂ H H))

@[simp] lemma perturbMap_apply (V : H →L[ℂ] H) (p : H × H) :
    perturbMap V p = (p.1, p.2 + V p.1) := rfl

/-- The graph of `T + V`, where `T` has graph `G` and `V` is bounded. -/
def perturbGraph (V : H →L[ℂ] H) (G : OperatorGraph H) : OperatorGraph H :=
  G.map (perturbMap V : (H × H) →L[ℂ] (H × H)).toLinearMap

lemma mem_perturbGraph_iff {V : H →L[ℂ] H} {G : OperatorGraph H} {p : H × H} :
    p ∈ perturbGraph V G ↔ ∃ q ∈ G, (q.1, q.2 + V q.1) = p := by
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩

lemma isSymmetricGraph_perturbGraph {G : OperatorGraph H} (hsym : IsSymmetricGraph G)
    {V : H →L[ℂ] H} (hV : ∀ x y : H, ⟪V x, y⟫_ℂ = ⟪x, V y⟫_ℂ) :
    IsSymmetricGraph (perturbGraph V G) := by
  rintro p hp q hq
  obtain ⟨p', hp', rfl⟩ := mem_perturbGraph_iff.mp hp
  obtain ⟨q', hq', rfl⟩ := mem_perturbGraph_iff.mp hq
  simp only [inner_add_left, inner_add_right]
  rw [hsym hp' q' hq', hV q'.1 p'.1]

/-- **Kato–Rellich for bounded perturbations, surjectivity step.** If `K` is self-adjoint and
`‖V‖ < ‖c‖` for a purely imaginary `c`, then `K + V + c` is surjective. -/
lemma defRange_perturbGraph_eq_top [CompleteSpace H] {K : OperatorGraph H}
    (hK : IsSelfAdjointGraph K) {V : H →L[ℂ] H}
    {c : ℂ} (hc : c.re = 0) (hc0 : c ≠ 0) (hlt : ‖V‖ < ‖c‖) :
    defRange c (perturbGraph V K) = ⊤ := by
  classical
  have hsym : IsSymmetricGraph K := hK.isSymmetric
  have hKclosed : IsClosed ((K : OperatorGraph H) : Set (H × H)) := hK.isClosed
  haveI : CompleteSpace K := hKclosed.completeSpace_coe
  have hcpos : 0 < ‖c‖ := lt_of_le_of_lt (norm_nonneg V) hlt
  set Phi : K →L[ℂ] H := (shiftMap c).comp K.subtypeL with hPhi
  have hPhiApply : ∀ p : K, Phi p = ((p : H × H)).2 + c • ((p : H × H)).1 := fun _ => rfl
  have hlower : ∀ p : K, ‖c‖ * ‖((p : H × H)).1‖ ≤ ‖Phi p‖ := by
    intro p
    have h := norm_shift_sq hsym p.2 (c := c) hc
    rw [hPhiApply p]
    nlinarith [norm_nonneg ((p : H × H)).1, norm_nonneg ((p : H × H)).2,
      norm_nonneg (((p : H × H)).2 + c • ((p : H × H)).1), hcpos]
  have hker : LinearMap.ker (Phi : K →ₗ[ℂ] H) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have h := norm_shift_sq hsym p.2 (c := c) hc
    have hp' : ((p : H × H)).2 + c • ((p : H × H)).1 = 0 := hp
    rw [hp'] at h
    simp only [norm_zero] at h
    have hcsq : 0 < ‖c‖ ^ 2 := by positivity
    have hsum : ‖((p : H × H)).2‖ ^ 2 + ‖c‖ ^ 2 * ‖((p : H × H)).1‖ ^ 2 = 0 := by
      rw [← h]; ring
    have ha2 : ‖((p : H × H)).1‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖((p : H × H)).2‖, sq_nonneg ‖((p : H × H)).1‖]
    have hb2 : ‖((p : H × H)).2‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖((p : H × H)).2‖, sq_nonneg ‖((p : H × H)).1‖]
    have h1 : ‖((p : H × H)).1‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha2
    have h2 : ‖((p : H × H)).2‖ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb2
    apply Subtype.ext
    exact Prod.ext (norm_eq_zero.mp h1) (norm_eq_zero.mp h2)
  have hran : LinearMap.range (Phi : K →ₗ[ℂ] H) = ⊤ := by
    refine eq_top_iff.mpr ?_
    intro z _
    have hz : z ∈ defRange c K := by
      rw [defRange_eq_top_of_isSelfAdjointGraph hK hc hc0]; trivial
    obtain ⟨p, hp, hpz⟩ := mem_defRange_iff.mp hz
    exact ⟨⟨p, hp⟩, hpz⟩
  let e : K ≃L[ℂ] H := ContinuousLinearEquiv.ofBijective Phi hker hran
  have he : ∀ p : K, e p = Phi p := fun _ => rfl
  have hesymm : ∀ w : H, Phi (e.symm w) = w := by
    intro w
    rw [← he]
    exact e.apply_symm_apply w
  set R : H →L[ℂ] H :=
    (ContinuousLinearMap.fst ℂ H H).comp (K.subtypeL.comp (e.symm : H →L[ℂ] K)) with hR
  have hRapp : ∀ w : H, R w = ((e.symm w : K) : H × H).1 := fun _ => rfl
  have hRnorm : ∀ w : H, ‖R w‖ ≤ ‖c‖⁻¹ * ‖w‖ := by
    intro w
    have h1 := hlower (e.symm w)
    rw [hesymm w] at h1
    rw [hRapp w, inv_mul_eq_div, le_div_iff₀ hcpos]
    linarith [h1, mul_comm ‖c‖ ‖((e.symm w : K) : H × H).1‖]
  have hRop : ‖R‖ ≤ ‖c‖⁻¹ := R.opNorm_le_bound (by positivity) hRnorm
  set B : H →L[ℂ] H := V.comp R with hB
  have hBnorm : ‖B‖ < 1 := by
    have h1 : ‖B‖ ≤ ‖V‖ * ‖R‖ := V.opNorm_comp_le R
    have h2 : ‖V‖ * ‖R‖ ≤ ‖V‖ * ‖c‖⁻¹ := by
      exact mul_le_mul_of_nonneg_left hRop (norm_nonneg V)
    have h3 : ‖V‖ * ‖c‖⁻¹ < 1 := by
      rw [inv_eq_one_div, mul_one_div, div_lt_one hcpos]
      exact hlt
    linarith
  obtain ⟨u, hu⟩ : ∃ u : (H →L[ℂ] H)ˣ, (u : H →L[ℂ] H) = 1 + B := by
    refine ⟨Units.oneSub (-B) (by simpa using hBnorm), ?_⟩
    simp
  refine eq_top_iff.mpr ?_
  intro w _
  set z : H := ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) w with hz
  have hzw : z + B z = w := by
    have hmul : ((u : H →L[ℂ] H) * ((u⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)) = 1 := u.mul_inv
    have happ := congrArg (fun f : H →L[ℂ] H => f w) hmul
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply, hu,
      ContinuousLinearMap.add_apply] at happ
    simpa [hz] using happ
  set p : H × H := ((e.symm z : K) : H × H) with hp
  have hpK : p ∈ K := (e.symm z).2
  have hpz : p.2 + c • p.1 = z := hesymm z
  refine mem_defRange_iff.mpr ⟨(p.1, p.2 + V p.1), mem_perturbGraph_iff.mpr ⟨p, hpK, rfl⟩, ?_⟩
  have hBz : B z = V p.1 := by
    rw [hB]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [hRapp z]
  calc (p.2 + V p.1) + c • p.1 = (p.2 + c • p.1) + V p.1 := by abel
    _ = z + B z := by rw [hpz, hBz]
    _ = w := hzw

lemma dense_defRange_perturbGraph {G : OperatorGraph H} {V : H →L[ℂ] H} {c : ℂ}
    (htop : defRange c (perturbGraph V G.topologicalClosure) = ⊤) :
    Dense ((defRange c (perturbGraph V G) : Submodule ℂ H) : Set H) := by
  set psi : (H × H) →L[ℂ] H := (shiftMap c).comp (perturbMap V) with hpsi
  have hpsiApply : ∀ q : H × H, psi q = (q.2 + V q.1) + c • q.1 := fun _ => rfl
  have himage : psi '' (G : Set (H × H)) ⊆ ((defRange c (perturbGraph V G) : Submodule ℂ H) : Set H) := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_defRange_iff.mpr ⟨(r.1, r.2 + V r.1), mem_perturbGraph_iff.mpr ⟨r, hr, rfl⟩, rfl⟩
  intro x
  have hx : x ∈ defRange c (perturbGraph V G.topologicalClosure) := by rw [htop]; trivial
  obtain ⟨pp, hpp, rfl⟩ := mem_defRange_iff.mp hx
  obtain ⟨q, hq, rfl⟩ := mem_perturbGraph_iff.mp hpp
  have hqmem : q ∈ closure (G : Set (H × H)) := by
    simpa [Submodule.topologicalClosure_coe] using hq
  have hmem : psi q ∈ closure (psi '' (G : Set (H × H))) :=
    image_closure_subset_closure_image psi.continuous ⟨q, hqmem, rfl⟩
  exact closure_mono himage hmem

/-- **Kato–Rellich (bounded perturbation).** If a symmetric operator `T` is essentially
self-adjoint and `V` is a bounded symmetric operator, then `T + V` is essentially self-adjoint
on the same domain. -/
theorem essentiallySelfAdjoint_perturbGraph [CompleteSpace H] {G : OperatorGraph H}
    (hG : EssentiallySelfAdjoint G) {V : H →L[ℂ] H}
    (hV : ∀ x y : H, ⟪V x, y⟫_ℂ = ⟪x, V y⟫_ℂ) :
    EssentiallySelfAdjoint (perturbGraph V G) := by
  have hsym : IsSymmetricGraph G :=
    le_trans (Submodule.le_topologicalClosure G) (le_of_eq hG)
  set c : ℂ := ((‖V‖ + 1 : ℝ) : ℂ) * Complex.I with hcdef
  have hcre : c.re = 0 := by simp [hcdef]
  have hcnorm : ‖c‖ = ‖V‖ + 1 := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖V‖ + 1)]
  have hlt : ‖V‖ < ‖c‖ := by rw [hcnorm]; linarith
  have hc0 : c ≠ 0 := by
    intro h
    rw [h] at hcnorm
    simp at hcnorm
    linarith [norm_nonneg V]
  have hKsa : IsSelfAdjointGraph G.topologicalClosure := isSelfAdjointGraph_topologicalClosure hG
  refine essentiallySelfAdjoint_of_defRange_dense (isSymmetricGraph_perturbGraph hsym hV)
    hcre hc0 ?_ ?_
  · exact dense_defRange_perturbGraph (defRange_perturbGraph_eq_top hKsa hcre hc0 hlt)
  · refine dense_defRange_perturbGraph (defRange_perturbGraph_eq_top hKsa ?_ ?_ ?_)
    · simpa using hcre
    · exact neg_ne_zero.mpr hc0
    · simpa using hlt

/-! ### The Schrödinger operator -/

/-- The Schrödinger operator with bounded kinetic term `A` and bounded potential `V`. -/
def schrodingerOp (A V : H →L[ℂ] H) : H →L[ℂ] H := A + V

/-- **Weak regularity of a potential.** The potential `V` is not assumed to have any smoothness
or continuity properties: it is only required to act as a bounded symmetric operator on the
Hilbert space (as is the case, e.g., for multiplication by an arbitrary essentially bounded
real measurable function). -/
def WeaklyRegularPotential (V : H →L[ℂ] H) : Prop := ∀ x y : H, ⟪V x, y⟫_ℂ = ⟪x, V y⟫_ℂ

/-- The graph of the Schrödinger operator `T + V`, where the kinetic term `T` is the (possibly
unbounded) operator with graph `G` and `V` is a potential. -/
def schrodingerGraph (V : H →L[ℂ] H) (G : OperatorGraph H) : OperatorGraph H := perturbGraph V G

/-- **Essential self-adjointness of a Schrödinger operator with a weakly regular potential.**

Let `T` be a symmetric, essentially self-adjoint kinetic term on a complex Hilbert space `H`
(for instance the free Hamiltonian `-Δ` on a core of smooth compactly supported functions), and
let `V` be a weakly regular potential, i.e. a symmetric potential which is merely bounded, with
no smoothness or continuity assumed. Then the Schrödinger operator `T + V`, defined on the same
domain, is essentially self-adjoint: the closure of its graph coincides with the graph of its
adjoint, equivalently both of its deficiency spaces are trivial. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakRegularity [CompleteSpace H]
    {G : OperatorGraph H} (hG : EssentiallySelfAdjoint G)
    {V : H →L[ℂ] H} (hV : WeaklyRegularPotential V) :
    EssentiallySelfAdjoint (schrodingerGraph V G) :=
  essentiallySelfAdjoint_perturbGraph hG hV

/-- Perturbing the graph of a bounded operator `A` on a domain `D` by a bounded potential `V`
gives the graph of `A + V` on `D`. -/
lemma schrodingerGraph_opGraph (A V : H →L[ℂ] H) (D : Submodule ℂ H) :
    schrodingerGraph V (opGraph A D) = opGraph (schrodingerOp A V) D := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := mem_perturbGraph_iff.mp hp
    exact ⟨hq.1, by simp [schrodingerOp, hq.2]⟩
  · intro hp
    refine mem_perturbGraph_iff.mpr ⟨(p.1, A p.1), ⟨hp.1, rfl⟩, ?_⟩
    have h2 : p.2 = A p.1 + V p.1 := by simpa [schrodingerOp] using hp.2
    exact Prod.ext rfl h2.symm

/-- **Bounded kinetic term.** A Schrödinger operator whose kinetic term `A` is a bounded
symmetric operator and whose potential `V` is weakly regular is essentially self-adjoint on any
dense core `D`. This is an unconditional instance of the previous theorem. -/
theorem schrodingerOp_essentiallySelfAdjoint_of_weakRegularity [CompleteSpace H]
    {A V : H →L[ℂ] H} (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hV : WeaklyRegularPotential V) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    EssentiallySelfAdjoint (opGraph (schrodingerOp A V) D) := by
  rw [← schrodingerGraph_opGraph]
  exact schrodinger_essentiallySelfAdjoint_of_weakRegularity
    (essentiallySelfAdjoint_opGraph hA hD) hV

/-- The closure of the Schrödinger operator with bounded kinetic term and weakly regular
potential, initially defined on a dense core `D`, is the everywhere defined self-adjoint
operator `A + V`. -/
theorem schrodingerOp_topologicalClosure_of_weakRegularity [CompleteSpace H]
    {A V : H →L[ℂ] H} (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hV : WeaklyRegularPotential V) {D : Submodule ℂ H} (hD : Dense (D : Set H)) :
    (opGraph (schrodingerOp A V) D).topologicalClosure = opGraph (schrodingerOp A V) ⊤ := by
  refine topologicalClosure_opGraph ?_ hD
  intro x y
  simp only [schrodingerOp, ContinuousLinearMap.add_apply, inner_add_left, inner_add_right,
    hA x y, hV x y]

end Brockian.Weyl.DeficiencyODE

