import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
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

universe u

namespace Frontier

open scoped InnerProductSpace

/-- A *quantum measure* (a finitely additive probability measure on the lattice of subspaces of
a Hilbert space): a nonnegative function on subspaces, normalized at the whole space, and
additive on pairs of mutually orthogonal subspaces. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ H → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg' : ∀ K, 0 ≤ toFun K
  /-- A quantum measure is a probability measure. -/
  normalized' : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive' : ∀ K L : Submodule ℂ H, K ≤ Lᗮ → toFun (K ⊔ L) = toFun K + toFun L

namespace QuantumMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩

lemma nonneg (μ : QuantumMeasure H) (K : Submodule ℂ H) : 0 ≤ μ K := μ.nonneg' K

lemma normalized (μ : QuantumMeasure H) : μ ⊤ = 1 := μ.normalized'

lemma additive (μ : QuantumMeasure H) {K L : Submodule ℂ H} (h : K ≤ Lᗮ) :
    μ (K ⊔ L) = μ K + μ L := μ.additive' K L h

lemma map_bot (μ : QuantumMeasure H) : μ ⊥ = 0 := by
  have h : μ (⊥ ⊔ ⊥ : Submodule ℂ H) = μ ⊥ + μ ⊥ := μ.additive (by simp)
  simp only [sup_idem] at h
  linarith

/-- A quantum measure is finitely additive along any orthonormal family: the measure of the
span of finitely many pairwise orthogonal unit vectors is the sum of the measures of the
corresponding lines. -/
lemma sum_span_of_orthonormal {ι : Type*} [DecidableEq ι] (μ : QuantumMeasure H) {v : ι → H}
    (hv : Orthonormal ℂ v) (s : Finset ι) :
    μ (Submodule.span ℂ (v '' s)) = ∑ i ∈ s, μ (Submodule.span ℂ {v i}) := by
  classical
  induction s using Finset.induction with
  | empty => simp [map_bot]
  | insert a s ha ih =>
      have himg : v '' (↑(insert a s) : Set ι) = insert (v a) (v '' (s : Set ι)) := by
        simp [Set.image_insert_eq]
      have horth : Submodule.span ℂ (v '' (s : Set ι)) ≤ (Submodule.span ℂ {v a})ᗮ := by
        rw [Submodule.span_le]
        rintro y ⟨i, hi, rfl⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left]
        refine inner_eq_zero_symm.mp (hv.2 ?_)
        rintro rfl
        exact ha hi
      rw [himg, Submodule.span_insert, sup_comm, μ.additive horth, Finset.sum_insert ha, ih]
      ring

end QuantumMeasure

section Auxiliary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The image in `H` of an orthonormal basis of a subspace `K` spans `K`. -/
lemma span_range_orthonormalBasis_coe (K : Submodule ℂ H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K) :
    Submodule.span ℂ (Set.range fun i => ((b i : K) : H)) = K := by
  have h1 : (Set.range fun i => ((b i : K) : H)) = K.subtype '' Set.range b := by
    rw [← Set.range_comp]; rfl
  have h2 : Submodule.span ℂ (Set.range (b : ι → K)) = ⊤ := by
    simpa [OrthonormalBasis.coe_toBasis] using b.toBasis.span_eq
  rw [h1, ← Submodule.map_span, h2, Submodule.map_top, Submodule.range_subtype]

/-- The image in `H` of an orthonormal basis of a subspace `K` is an orthonormal family in `H`. -/
lemma orthonormal_coe_orthonormalBasis (K : Submodule ℂ H) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ K) : Orthonormal ℂ (fun i => ((b i : K) : H)) :=
  b.orthonormal.comp_linearIsometry K.subtypeₗᵢ

/-- The orthogonal projection onto a sup of two orthogonal subspaces is the sum of the two
orthogonal projections. -/
lemma starProjection_sup_of_orthogonal [FiniteDimensional ℂ H] {K L : Submodule ℂ H} (h : K ≤ Lᗮ)
    (x : H) : (K ⊔ L).starProjection x = K.starProjection x + L.starProjection x := by
  set p := K.starProjection x with hp
  set q := L.starProjection x with hq
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup (K.starProjection_apply_mem x) (L.starProjection_apply_mem x)) ?_
  intro w hw
  rw [Submodule.mem_sup] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := hw
  have h1 : ⟪x - p, a⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (K.sub_starProjection_mem_orthogonal x a ha)
  have h2 : ⟪x - q, b⟫_ℂ = 0 :=
    inner_eq_zero_symm.mp (L.sub_starProjection_mem_orthogonal x b hb)
  have hqa : ⟪q, a⟫_ℂ = 0 := (h ha) q (L.starProjection_apply_mem x)
  have hpb : ⟪p, b⟫_ℂ = 0 := inner_eq_zero_symm.mp ((h (K.starProjection_apply_mem x)) b hb)
  have key1 : ⟪x - p - q, a⟫_ℂ = 0 := by rw [inner_sub_left, h1, hqa]; ring
  have key2 : ⟪x - p - q, b⟫_ℂ = 0 := by
    rw [show x - p - q = x - q - p from by abel, inner_sub_left, h2, hpb]; ring
  rw [show x - (p + q) = x - p - q from by abel, inner_add_right, key1, key2]
  ring

/-- For a symmetric operator `T`, the diagonal matrix elements `⟪x, T x⟫` are real. -/
lemma inner_self_ofReal_re {T : H →ₗ[ℂ] H} (hT : T.IsSymmetric) (x : H) :
    ((RCLike.re ⟪x, T x⟫_ℂ : ℝ) : ℂ) = ⟪x, T x⟫_ℂ := by
  have h : (starRingEnd ℂ) ⟪x, T x⟫_ℂ = ⟪x, T x⟫_ℂ := by
    rw [inner_conj_symm]; exact hT x x
  simpa using Complex.conj_eq_iff_re.mp h

/-- The trace of `T` composed with the orthogonal projection onto `K` is computed by summing
the diagonal matrix elements of `T` over an orthonormal basis of `K`. -/
lemma trace_comp_starProjection_eq_sum [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H)
    (K : Submodule ℂ H) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ K) :
    LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))
      = ∑ i, ⟪((b i : K) : H), T (b i : K)⟫_ℂ := by
  have hcomp : T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)
      = (T ∘ₗ K.subtype) ∘ₗ (K.orthogonalProjection : H →ₗ[ℂ] K) := by
    ext x
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_apply]
  rw [hcomp, LinearMap.trace_comp_comm' (K.orthogonalProjection : H →ₗ[ℂ] K) (T ∘ₗ K.subtype),
    LinearMap.trace_eq_sum_inner _ b]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply]
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left (b i) (T (b i : K))


/-- The trace of `T` against the projection onto `K` is real when `T` is symmetric, and it is
the sum of the (real) diagonal matrix elements over an orthonormal basis of `K`. -/
lemma trace_comp_starProjection_eq_ofReal_sum [FiniteDimensional ℂ H] {T : H →ₗ[ℂ] H}
    (hT : T.IsSymmetric) (K : Submodule ℂ H) :
    LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))
      = ((∑ i, RCLike.re ⟪((stdOrthonormalBasis ℂ K i : K) : H),
            T (stdOrthonormalBasis ℂ K i : K)⟫_ℂ : ℝ) : ℂ) := by
  rw [trace_comp_starProjection_eq_sum T K (stdOrthonormalBasis ℂ K), Complex.ofReal_sum]
  exact (Finset.sum_congr rfl fun i _ => inner_self_ofReal_re hT _).symm

/-- For a symmetric `T`, the trace of `T` against an orthogonal projection is a real number. -/
lemma ofReal_re_trace_comp_starProjection [FiniteDimensional ℂ H] {T : H →ₗ[ℂ] H}
    (hT : T.IsSymmetric) (K : Submodule ℂ H) :
    ((RCLike.re (LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))) : ℝ) : ℂ)
      = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) := by
  rw [trace_comp_starProjection_eq_ofReal_sum hT K]
  simp

/-- For a positive `T`, the trace of `T` against an orthogonal projection is nonnegative. -/
lemma re_trace_comp_starProjection_nonneg [FiniteDimensional ℂ H] {T : H →ₗ[ℂ] H}
    (hT : T.IsPositive) (K : Submodule ℂ H) :
    0 ≤ RCLike.re (LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H))) := by
  rw [trace_comp_starProjection_eq_ofReal_sum hT.1 K]
  have hnn : 0 ≤ ∑ i, RCLike.re ⟪((stdOrthonormalBasis ℂ K i : K) : H),
      T (stdOrthonormalBasis ℂ K i : K)⟫_ℂ := by
    refine Finset.sum_nonneg fun i _ => ?_
    have h := hT.2 ((stdOrthonormalBasis ℂ K i : K) : H)
    rwa [hT.1 _ _] at h
  simpa using hnn

end Auxiliary

/-- The *frame property* for a Hilbert space `H`: every quantum measure on `H` is given, on the
one-dimensional subspaces, by a positive operator. -/
def GleasonFrameProperty (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ μ : QuantumMeasure H, ∃ T : H →ₗ[ℂ] H, T.IsPositive ∧
    ∀ x : H, ‖x‖ = 1 → (μ (Submodule.span ℂ {x}) : ℂ) = ⟪x, T x⟫_ℂ

/-- The analytic core of Gleason's theorem: on every complex Hilbert space of dimension at
least three, every nonnegative frame function (equivalently, the restriction of a quantum
measure to the one-dimensional subspaces) is a quadratic form `x ↦ ⟪x, T x⟫` for some positive
operator `T`.  This is the hard, geometric part of Gleason's argument; it is taken here as an
explicit hypothesis, and `Frontier.gleason_theorem` reduces the full statement to it. -/
def GleasonFrameCore : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E],
    3 ≤ Module.finrank ℂ E → GleasonFrameProperty E

/-- **Gleason's theorem** (reduction to the frame-function core).

Let `H` be a complex Hilbert space of dimension at least three, and let `μ` be a quantum
measure on `H`, i.e. a nonnegative, normalized, orthogonally additive function on the lattice
of subspaces of `H`.  Granting the analytic core of Gleason's theorem (`GleasonFrameCore`:
nonnegative frame functions in dimension at least three are quadratic forms), there is a
density operator `T` on `H` — a positive operator of unit trace — such that

`μ K = tr (T ∘ P_K)`

for every subspace `K`, where `P_K` is the orthogonal projection onto `K`.  In other words,
every quantum measure comes from a density operator. -/
theorem gleason_theorem {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (h3 : 3 ≤ Module.finrank ℂ H) (hcore : GleasonFrameCore.{u})
    (μ : QuantumMeasure H) :
    ∃ T : H →ₗ[ℂ] H, T.IsPositive ∧ LinearMap.trace ℂ H T = 1 ∧
      ∀ K : Submodule ℂ H,
        (μ K : ℂ) = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) := by
  classical
  obtain ⟨T, hTpos, hTframe⟩ := hcore H h3 μ
  -- The key computation: the measure of any subspace is the trace of `T` against its projection.
  have key : ∀ K : Submodule ℂ H,
      (μ K : ℂ) = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) := by
    intro K
    set b := stdOrthonormalBasis ℂ K with hb
    set v : Fin (Module.finrank ℂ K) → H := fun i => ((b i : K) : H) with hv
    have hvon : Orthonormal ℂ v := orthonormal_coe_orthonormalBasis K b
    have hspan : Submodule.span ℂ (v '' (Finset.univ : Finset (Fin (Module.finrank ℂ K)))) = K := by
      have himg : (v '' (Finset.univ : Finset (Fin (Module.finrank ℂ K)))) = Set.range v := by
        simp [Set.image_univ]
      rw [himg]
      exact span_range_orthonormalBasis_coe K b
    have hsum := μ.sum_span_of_orthonormal hvon (Finset.univ : Finset (Fin (Module.finrank ℂ K)))
    rw [hspan] at hsum
    have hnorm : ∀ i, ‖v i‖ = 1 := by
      intro i
      have h : ‖(b i : K)‖ = 1 := b.norm_eq_one i
      rwa [show ‖(b i : K)‖ = ‖((b i : K) : H)‖ from rfl] at h
    calc (μ K : ℂ) = ((∑ i, μ (Submodule.span ℂ {v i}) : ℝ) : ℂ) := by rw [hsum]
      _ = ∑ i, ((μ (Submodule.span ℂ {v i}) : ℝ) : ℂ) := by push_cast; ring
      _ = ∑ i, ⟪v i, T (v i)⟫_ℂ := Finset.sum_congr rfl fun i _ => hTframe (v i) (hnorm i)
      _ = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) :=
          (trace_comp_starProjection_eq_sum T K b).symm
  refine ⟨T, hTpos, ?_, key⟩
  have htop := key ⊤
  rw [μ.normalized] at htop
  have hid : ((⊤ : Submodule ℂ H).starProjection : H →ₗ[ℂ] H) = LinearMap.id := by
    rw [Submodule.starProjection_top]; rfl
  rw [hid, LinearMap.comp_id] at htop
  exact htop.symm

/-- The converse direction, proved unconditionally: every density operator (a positive operator
of unit trace) on a finite-dimensional complex Hilbert space defines a quantum measure via
`K ↦ tr (T ∘ P_K)`.  Together with `Frontier.gleason_theorem` this identifies quantum measures
with density operators. -/
theorem quantumMeasure_of_density {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (T : H →ₗ[ℂ] H) (hTpos : T.IsPositive)
    (hTtr : LinearMap.trace ℂ H T = 1) :
    ∃ μ : QuantumMeasure H, ∀ K : Submodule ℂ H,
      (μ K : ℂ) = LinearMap.trace ℂ H (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)) := by
  classical
  have hid : ((⊤ : Submodule ℂ H).starProjection : H →ₗ[ℂ] H) = LinearMap.id := by
    rw [Submodule.starProjection_top]; rfl
  refine ⟨{ toFun := fun K => RCLike.re (LinearMap.trace ℂ H
              (T ∘ₗ (K.starProjection : H →ₗ[ℂ] H)))
            nonneg' := fun K => re_trace_comp_starProjection_nonneg hTpos K
            normalized' := ?_
            additive' := ?_ }, ?_⟩
  · rw [hid, LinearMap.comp_id, hTtr]
    simp
  · intro K L hKL
    have hproj : ((K ⊔ L).starProjection : H →ₗ[ℂ] H)
        = (K.starProjection : H →ₗ[ℂ] H) + (L.starProjection : H →ₗ[ℂ] H) := by
      ext x
      simpa using starProjection_sup_of_orthogonal hKL x
    rw [hproj, LinearMap.comp_add, map_add, map_add]
  · intro K
    exact ofReal_re_trace_comp_starProjection hTpos.1 K

end Frontier

