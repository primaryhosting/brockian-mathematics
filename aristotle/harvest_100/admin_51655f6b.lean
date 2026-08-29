import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.SchrodingerMinimal

open LinearPMap

open scoped LinearPMap ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- A densely defined operator `T` on a complex Hilbert space is *essentially self-adjoint* if
its adjoint is self-adjoint; equivalently, `T` has a unique self-adjoint extension, namely the
closure `T†† = T̄` of `T`. -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop := IsSelfAdjoint T†

/-- Taking adjoints is antitone. -/
theorem adjoint_le_adjoint_of_le {S T : H →ₗ.[ℂ] H} (hS : Dense (S.domain : Set H)) (h : S ≤ T) :
    T† ≤ S† := by
  have hT : Dense (T.domain : Set H) := hS.mono fun x hx => h.1 hx
  have hfa : S.IsFormalAdjoint T† := by
    intro x y
    have hx : (x : H) ∈ T.domain := h.1 x.2
    have h1 : ⟪T (⟨(x : H), hx⟩ : T.domain), (y : H)⟫ = ⟪(x : H), T† y⟫ :=
      (adjoint_isFormalAdjoint hT).symm ⟨(x : H), hx⟩ y
    rwa [← h.2 (rfl : ((x : H)) = ((⟨(x : H), hx⟩ : T.domain) : H))] at h1
  exact hfa.le_adjoint hS

/-- A densely defined symmetric operator is contained in its adjoint. -/
theorem le_adjoint_self {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : T ≤ T† :=
  hsymm.le_adjoint hdense

/-- The adjoint of a densely defined symmetric operator is densely defined. -/
theorem dense_adjoint_domain {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : Dense ((T†).domain : Set H) :=
  hdense.mono fun x hx => (le_adjoint_self hdense hsymm).1 hx

/-- A densely defined symmetric operator is contained in its second adjoint. -/
theorem le_adjoint_adjoint {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : T ≤ T†† :=
  (adjoint_isFormalAdjoint hdense).le_adjoint (dense_adjoint_domain hdense hsymm)

/-- The second adjoint of a densely defined symmetric operator is contained in the adjoint. -/
theorem adjoint_adjoint_le_adjoint {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : T†† ≤ T† :=
  adjoint_le_adjoint_of_le hdense (le_adjoint_self hdense hsymm)

/-- The second adjoint of a densely defined symmetric operator is symmetric. -/
theorem adjoint_adjoint_isFormalAdjoint {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T) : (T††).IsFormalAdjoint (T††) := by
  intro x y
  have hle : T†† ≤ T† := adjoint_adjoint_le_adjoint hdense hsymm
  have hy : (y : H) ∈ (T†).domain := hle.1 y.2
  have h1 : ⟪T†† x, (y : H)⟫ = ⟪(x : H), T† (⟨(y : H), hy⟩ : (T†).domain)⟫ :=
    adjoint_isFormalAdjoint (dense_adjoint_domain hdense hsymm) x ⟨(y : H), hy⟩
  rwa [← hle.2 (rfl : ((y : H)) = ((⟨(y : H), hy⟩ : (T†).domain) : H))] at h1

/-- The shifted operator `T + z` as a linear map on the domain of `T`. -/
noncomputable def shiftMap (T : H →ₗ.[ℂ] H) (z : ℂ) : T.domain →ₗ[ℂ] H :=
  T.toFun + z • T.domain.subtype

@[simp] theorem shiftMap_apply (T : H →ₗ.[ℂ] H) (z : ℂ) (x : T.domain) :
    shiftMap T z x = T x + z • (x : H) := rfl

/-- A vector is orthogonal to the range of `T + z` exactly when it solves the (weak) eigenvalue
equation `T† v = conj (-z) • v`. -/
theorem mem_orthogonal_range_shiftMap_iff {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (z : ℂ) (v : H) :
    v ∈ (LinearMap.range (shiftMap T z))ᗮ ↔
      ∃ hv : v ∈ (T†).domain, T† ⟨v, hv⟩ = conj (-z) • v := by
  constructor
  · intro hv
    have key : ∀ x : T.domain, ⟪conj (-z) • v, (x : H)⟫ = ⟪v, T x⟫ := by
      intro x
      have h0 : ⟪shiftMap T z x, v⟫ = 0 := (Submodule.mem_orthogonal _ v).mp hv _ ⟨x, rfl⟩
      have h0' : ⟪v, T x + z • (x : H)⟫ = 0 := by
        rw [← inner_conj_symm]
        simp only [shiftMap_apply] at h0
        rw [h0, map_zero]
      rw [inner_add_right, inner_smul_right] at h0'
      rw [inner_smul_left, RingHomCompTriple.comp_apply, RingHom.id_apply]
      simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply,
        Complex.conj_conj]
      linear_combination h0'
    have hv' : v ∈ (T†).domain := mem_adjoint_domain_of_exists _ ⟨conj (-z) • v, key⟩
    exact ⟨hv', adjoint_apply_eq hdense ⟨v, hv'⟩ key⟩
  · rintro ⟨hv, hval⟩
    rw [Submodule.mem_orthogonal]
    rintro u ⟨x, rfl⟩
    have h1 : ⟪T† (⟨v, hv⟩ : (T†).domain), (x : H)⟫ = ⟪v, T x⟫ :=
      adjoint_isFormalAdjoint hdense ⟨v, hv⟩ x
    rw [hval, inner_smul_left] at h1
    simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj] at h1
    have h2 : ⟪v, T x + z • (x : H)⟫ = 0 := by
      rw [inner_add_right, inner_smul_right, ← h1]
      ring
    have := congrArg (starRingEnd ℂ) h2
    rw [inner_conj_symm, map_zero] at this
    simpa using this

/-- Key estimate: for a symmetric operator and purely imaginary `z`,
`‖A x + z • x‖² = ‖A x‖² + ‖z • x‖²`. -/
theorem norm_shift_sq {A : H →ₗ.[ℂ] H} (hsymm : A.IsFormalAdjoint A) {z : ℂ}
    (hz : conj z = -z) (x : A.domain) :
    ‖A x + z • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖z • (x : H)‖ ^ 2 := by
  have hc : conj (⟪A x, (x : H)⟫) = ⟪A x, (x : H)⟫ := by
    rw [inner_conj_symm]
    exact (hsymm x x).symm
  have hzc : conj (z * ⟪A x, (x : H)⟫) = -(z * ⟪A x, (x : H)⟫) := by
    rw [map_mul, hz, hc]; ring
  have hre : Complex.re (z * ⟪A x, (x : H)⟫) = 0 := by
    have h2 := Complex.add_conj (z * ⟪A x, (x : H)⟫)
    rw [hzc] at h2
    simp only [add_neg_cancel] at h2
    have : ((2 * Complex.re (z * ⟪A x, (x : H)⟫) : ℝ) : ℂ) = 0 := h2.symm
    have : (2 : ℝ) * Complex.re (z * ⟪A x, (x : H)⟫) = 0 := by exact_mod_cast this
    linarith
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right]
  simp only [RCLike.re_to_complex, hre]
  ring

/-- For a closed symmetric operator `A` and unit purely imaginary `z` with `Ran (A + z)` dense,
the operator `A + z` is surjective. -/
theorem surjective_shift_of_isClosed {A : H →ₗ.[ℂ] H} (hclosed : A.IsClosed)
    (hsymm : A.IsFormalAdjoint A) {z : ℂ} (hz : conj z = -z) (hz1 : ‖z‖ = 1)
    (hdense : Dense (Set.range fun x : A.domain => A x + z • (x : H))) (y : H) :
    ∃ x : A.domain, A x + z • (x : H) = y := by
  haveI : _root_.IsClosed (A.graph : Set (H × H)) := hclosed
  haveI : CompleteSpace (A.graph : Set (H × H)) := IsClosed.completeSpace_coe
  -- the continuous linear map `(x, w) ↦ w + z • x` restricted to the graph of `A`
  set F : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hF
  set f : (A.graph : Submodule ℂ (H × H)) →L[ℂ] H := F.comp (A.graph.subtypeL) with hf
  have hrange : Set.range f = Set.range fun x : A.domain => A x + z • (x : H) := by
    ext w
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := (A.mem_graph_iff).mp p.2
      refine ⟨x, ?_⟩
      simp only [hf, hF, ContinuousLinearMap.coe_comp', Function.comp_apply,
        Submodule.coe_subtypeL', Submodule.coe_subtype, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [hx1, hx2]
    · rintro ⟨x, rfl⟩
      refine ⟨⟨((x : H), A x), A.mem_graph x⟩, ?_⟩
      simp [hf, hF]
  have hanti : AntilipschitzWith 1 f := by
    refine AddMonoidHomClass.antilipschitz_of_bound f fun p => ?_
    obtain ⟨x, hx1, hx2⟩ := (A.mem_graph_iff).mp p.2
    have hfp : f p = A x + z • (x : H) := by
      simp only [hf, hF, ContinuousLinearMap.coe_comp', Function.comp_apply,
        Submodule.coe_subtypeL', Submodule.coe_subtype, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_smul', Pi.smul_apply]
      rw [hx1, hx2]
    have hkey : ‖A x + z • (x : H)‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [norm_shift_sq hsymm hz x, norm_smul, hz1]
      ring
    have hpnorm : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖A x‖ := by
      rw [← hx1, ← hx2]
      simp [Prod.norm_def]
    have hp : ‖p‖ = max ‖(x : H)‖ ‖A x‖ := hpnorm
    rw [hp, hfp]
    have h1 : (0 : ℝ) ≤ ‖A x + z • (x : H)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ ‖(x : H)‖ := norm_nonneg _
    have h3 : (0 : ℝ) ≤ ‖A x‖ := norm_nonneg _
    have hx : ‖(x : H)‖ ≤ ‖A x + z • (x : H)‖ := by nlinarith
    have hax : ‖A x‖ ≤ ‖A x + z • (x : H)‖ := by nlinarith
    simp only [NNReal.coe_one, one_mul]
    exact max_le hx hax
  have hclosedRange : _root_.IsClosed (Set.range f) :=
    hanti.isClosed_range (ContinuousLinearMap.uniformContinuous f)
  have : Set.range f = Set.univ := by
    have hd : Dense (Set.range f) := by rw [hrange]; exact hdense
    rw [← hclosedRange.closure_eq, hd.closure_eq]
  rw [hrange] at this
  have hy : y ∈ Set.range fun x : A.domain => A x + z • (x : H) := by
    rw [this]; trivial
  exact hy

/-- **Basic criterion for essential self-adjointness.**  A densely defined symmetric operator
whose deficiency equations `T† u = ± i u` have no nonzero solutions is essentially
self-adjoint. -/
theorem essentiallySelfAdjoint_of_deficiency {T : H →ₗ.[ℂ] H} (hdense : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T)
    (hpos : ∀ (u : H) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = Complex.I • u → u = 0)
    (hneg : ∀ (u : H) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = -Complex.I • u → u = 0) :
    EssentiallySelfAdjoint T := by
  have hd' : Dense ((T†).domain : Set H) := dense_adjoint_domain hdense hsymm
  have hAle : T†† ≤ T† := adjoint_adjoint_le_adjoint hdense hsymm
  have hTA : T ≤ T†† := le_adjoint_adjoint hdense hsymm
  have hAclosed : (T††).IsClosed := adjoint_isClosed hd'
  have hAsymm : (T††).IsFormalAdjoint (T††) := adjoint_adjoint_isFormalAdjoint hdense hsymm
  -- the range of `T + i` is dense
  have hKbot : (LinearMap.range (shiftMap T Complex.I))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := (mem_orthogonal_range_shiftMap_iff hdense Complex.I v).mp hv
    refine hpos v hv1 ?_
    rw [hv2]
    simp
  have hKdense : Dense ((LinearMap.range (shiftMap T Complex.I) : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact Submodule.topologicalClosure_eq_top_iff.mpr hKbot
  have hdenseRange :
      Dense (Set.range fun x : (T††).domain => T†† x + Complex.I • (x : H)) := by
    refine hKdense.mono ?_
    rintro w ⟨x, rfl⟩
    exact ⟨⟨(x : H), hTA.1 x.2⟩, by
      simp only [shiftMap_apply]
      rw [← hTA.2 (rfl : ((x : H)) = ((⟨(x : H), hTA.1 x.2⟩ : (T††).domain) : H))]⟩
  -- surjectivity of `T†† + i`
  have hsurj : ∀ y : H, ∃ x : (T††).domain, T†† x + Complex.I • (x : H) = y := by
    intro y
    refine surjective_shift_of_isClosed hAclosed hAsymm ?_ ?_ hdenseRange y
    · simp
    · simp
  -- conclude
  have hle2 : T† ≤ T†† := by
    constructor
    · intro u hu
      obtain ⟨v, hv⟩ := hsurj (T† ⟨u, hu⟩ + Complex.I • u)
      have hvT : (v : H) ∈ (T†).domain := hAle.1 v.2
      have hvval : T† (⟨(v : H), hvT⟩ : (T†).domain) = T†† v :=
        (hAle.2 (rfl : ((v : H)) = ((⟨(v : H), hvT⟩ : (T†).domain) : H))).symm
      have hw : (⟨u, hu⟩ : (T†).domain) - ⟨(v : H), hvT⟩ = ⟨u - (v : H), by
        exact Submodule.sub_mem _ hu hvT⟩ := rfl
      have hTw : T† (⟨u - (v : H), Submodule.sub_mem _ hu hvT⟩ : (T†).domain)
          = -Complex.I • (u - (v : H)) := by
        have := (T†).map_sub (⟨u, hu⟩ : (T†).domain) ⟨(v : H), hvT⟩
        rw [hw] at this
        rw [this, hvval, ← hv]
        simp only [smul_sub]
        module
      have hzero : u - (v : H) = 0 := hneg _ _ hTw
      have : u = (v : H) := by
        have := sub_eq_zero.mp hzero
        exact this
      rw [this]
      exact v.2
    · intro x y hxy
      -- `x : T†.domain`, `y : T††.domain`, `(x : H) = y`
      exact (hAle.2 hxy.symm).symm
  have : T†† = T† := le_antisymm hAle hle2
  exact this

/-- The Hilbert space `L²(ℝ, ℂ)` on which the Schrödinger operator acts. -/
abbrev L2R : Type := MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)

/-- **Essential self-adjointness of the minimal Schrödinger operator from the ODE (Weyl limit
point) hypothesis.**

Here `T` is the minimal Schrödinger operator `u ↦ -u'' + V u` on `L²(ℝ)`, given as a densely
defined symmetric (`T.IsFormalAdjoint T`) unbounded operator, e.g. defined on `C_c^∞(ℝ)`.

The elements `u` of the domain of the adjoint `T†` with `T† u = ± i u` are exactly the
square-integrable (weak) solutions of the Schrödinger ODE `-u'' + V u = ± i u`; the hypotheses
`hode_pos` and `hode_neg` state that this ODE has no nonzero `L²` solution, which is Weyl's
limit-point condition.  Under this hypothesis `T` is essentially self-adjoint: its adjoint is
self-adjoint, i.e. `T†† = T†`, so the closure `T†† = T̄` of `T` is the unique self-adjoint
extension of `T`. -/
theorem schrodinger_essentiallySelfAdjoint_of_ode (T : L2R →ₗ.[ℂ] L2R)
    (hdense : Dense (T.domain : Set L2R)) (hsymm : T.IsFormalAdjoint T)
    (hode_pos : ∀ (u : L2R) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = Complex.I • u → u = 0)
    (hode_neg : ∀ (u : L2R) (hu : u ∈ (T†).domain), T† ⟨u, hu⟩ = -Complex.I • u → u = 0) :
    EssentiallySelfAdjoint T :=
  essentiallySelfAdjoint_of_deficiency hdense hsymm hode_pos hode_neg

end Brockian.Weyl.SchrodingerMinimal

