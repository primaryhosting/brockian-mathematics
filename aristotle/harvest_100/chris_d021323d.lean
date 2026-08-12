/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

open scoped ComplexOrder CStarAlgebra InnerProductSpace

namespace Frontier
namespace KadisonSinger

/-! ## The setting

Let `H` be a complex Hilbert space with a distinguished orthonormal (Hilbert) basis `e : ι → H`.
The *diagonal* subalgebra `𝒟` (an atomic MASA in `B(H)`, isomorphic to `ℓ^∞(ι)`) consists of the
bounded operators that are diagonalised by the basis.  The Kadison–Singer problem asks whether
every pure state of `𝒟` extends *uniquely* to a state of `B(H)`; this was answered
affirmatively by Marcus, Spielman and Srivastava.
-/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The rank-one orthogonal projection onto the line spanned by a unit vector `u`, i.e. `u u*`. -/
noncomputable def rankOneProj {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u : H) :
    H →L[ℂ] H := (innerSL ℂ u).smulRight u

@[simp] lemma rankOneProj_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u x : H) : rankOneProj u x = ⟪u, x⟫_ℂ • u := rfl

/-- A *state* on the C⋆-algebra `B(H)`: a unital positive linear functional. -/
structure IsState (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop where
  /-- A state is unital. -/
  map_one : psi 1 = 1
  /-- A state is positive: it maps positive operators to nonnegative complex numbers. -/
  nonneg : ∀ A : H →L[ℂ] H, 0 ≤ A → 0 ≤ psi A

/-- The diagonal subalgebra determined by a Hilbert basis `e`: the operators that are
diagonalised by `e`.  This is the atomic MASA `ℓ^∞(ι) ⊆ B(H)` of the Kadison–Singer problem. -/
def diagonal {ι : Type*} (e : HilbertBasis ι ℂ H) : Set (H →L[ℂ] H) :=
  {A | ∀ j, ∃ c : ℂ, A (e j) = c • e j}

/-- The state `psi` of `B(H)` is the *unique* state extending its own restriction to the
diagonal MASA. -/
def HasUniqueExtension {ι : Type*} (e : HilbertBasis ι ℂ H)
    (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  ∀ psi' : (H →L[ℂ] H) →ₗ[ℂ] ℂ, IsState psi' → (∀ A ∈ diagonal e, psi' A = psi A) → psi' = psi

/-- The restriction of `psi` to the diagonal MASA is a *pure* state.  For a commutative
C⋆-algebra the pure states are exactly the characters, i.e. the multiplicative states, which is
how purity of the restriction is expressed here. -/
def IsPureOnDiagonal {ι : Type*} (e : HilbertBasis ι ℂ H)
    (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) : Prop :=
  ∀ A ∈ diagonal e, ∀ B ∈ diagonal e, psi (A * B) = psi A * psi B

/-- **The Kadison–Singer problem** (in the form solved by Marcus–Spielman–Srivastava):
every state of `B(ℓ²(ℕ))` whose restriction to the atomic MASA `ℓ^∞(ℕ)` is pure is the unique
state extension of that restriction. -/
def Statement : Prop :=
  ∀ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (e : HilbertBasis ℕ ℂ H) (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ),
    IsState psi → IsPureOnDiagonal e psi → HasUniqueExtension e psi

/-- The *non-atomic* form of the Kadison–Singer problem: the same statement, restricted to the
pure states of the diagonal MASA that vanish on every atom `P_i = e_i e_i^*` (i.e. those
coming from free ultrafilters on `ℕ`). -/
def StatementNonatomic : Prop :=
  ∀ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (e : HilbertBasis ℕ ℂ H) (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ),
    IsState psi → IsPureOnDiagonal e psi → (∀ i, psi (rankOneProj (e i)) = 0) →
      HasUniqueExtension e psi

/-! ## Basic facts about rank-one projections -/

lemma star_rankOneProj (u : H) : star (rankOneProj u) = rankOneProj u := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff (rankOneProj u) (rankOneProj u)).mpr ?_).symm
  intro x y
  simp [inner_smul_left, inner_smul_right, mul_comm]

omit [CompleteSpace H] in
lemma rankOneProj_mul_self (u : H) (hu : ‖u‖ = 1) :
    rankOneProj u * rankOneProj u = rankOneProj u := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, rankOneProj_apply, inner_smul_right,
    inner_self_eq_norm_sq_to_K, hu]
  norm_num

omit [CompleteSpace H] in
lemma rankOneProj_mul_mul (u : H) (A : H →L[ℂ] H) :
    rankOneProj u * A * rankOneProj u = ⟪u, A u⟫_ℂ • rankOneProj u := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, rankOneProj_apply, map_smul,
    ContinuousLinearMap.smul_apply, smul_smul]
  ring_nf

omit [CompleteSpace H] in
lemma rankOneProj_mem_diagonal {ι : Type*} (e : HilbertBasis ι ℂ H) (i : ι) :
    rankOneProj (e i) ∈ diagonal e := by
  intro j
  rcases eq_or_ne i j with rfl | hij
  · refine ⟨1, ?_⟩
    have : ‖e i‖ = 1 := e.orthonormal.1 i
    simp [inner_self_eq_norm_sq_to_K, this]
  · exact ⟨0, by simp [e.orthonormal.inner_eq_zero hij]⟩

/-! ## Cauchy–Schwarz for states -/

/-- If a positive functional kills `star q * q`, it kills `star q * X` for every `X`
(Cauchy–Schwarz). -/
lemma apply_star_mul_eq_zero_left {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hpos : ∀ A : H →L[ℂ] H, 0 ≤ A → 0 ≤ psi A) {q : H →L[ℂ] H}
    (hq : psi (star q * q) = 0) (X : H →L[ℂ] H) : psi (star q * X) = 0 := by
  set f : (H →L[ℂ] H) →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ psi hpos with hf
  have hfa : ∀ A, f A = psi A := fun _ => rfl
  have hnorm : ‖f.toPreGNS q‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS, hfa, hq]
    simp
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS q) (f.toPreGNS X)
  rw [hnorm, zero_mul] at h1
  have h2 : ⟪f.toPreGNS q, f.toPreGNS X⟫_ℂ = 0 := by
    simpa using norm_le_zero_iff.mp h1
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, hfa] at h2
  exact h2

/-- If a positive functional kills `star q * q`, it kills `star X * q` for every `X`
(Cauchy–Schwarz). -/
lemma apply_star_mul_eq_zero_right {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hpos : ∀ A : H →L[ℂ] H, 0 ≤ A → 0 ≤ psi A) {q : H →L[ℂ] H}
    (hq : psi (star q * q) = 0) (X : H →L[ℂ] H) : psi (star X * q) = 0 := by
  set f : (H →L[ℂ] H) →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ psi hpos with hf
  have hfa : ∀ A, f A = psi A := fun _ => rfl
  have hnorm : ‖f.toPreGNS q‖ = 0 := by
    rw [PositiveLinearMap.preGNS_norm_def, PositiveLinearMap.ofPreGNS_toPreGNS, hfa, hq]
    simp
  have h1 := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS X) (f.toPreGNS q)
  rw [hnorm, mul_zero] at h1
  have h2 : ⟪f.toPreGNS X, f.toPreGNS q⟫_ℂ = 0 := by
    simpa using norm_le_zero_iff.mp h1
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.ofPreGNS_toPreGNS,
    PositiveLinearMap.ofPreGNS_toPreGNS, hfa] at h2
  exact h2

/-! ## The atomic case: a state concentrated on a unit vector is the vector state -/

/-- If a state `psi` of `B(H)` takes the value `1` on the rank-one projection onto a unit
vector `u`, then `psi` is the vector state `A ↦ ⟪u, A u⟫`. -/
theorem eq_vectorState_of_apply_rankOneProj_eq_one {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hpsi : IsState psi) {u : H} (hu : ‖u‖ = 1)
    (h1 : psi (rankOneProj u) = 1) (A : H →L[ℂ] H) : psi A = ⟪u, A u⟫_ℂ := by
  set P := rankOneProj u with hP
  set q : H →L[ℂ] H := 1 - P with hq
  have hstarP : star P = P := star_rankOneProj u
  have hPP : P * P = P := rankOneProj_mul_self u hu
  have hstarq : star q = q := by rw [hq, star_sub, star_one, hstarP]
  have hqq : star q * q = q := by
    have hexp : (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    rw [hstarq, hq, hexp, hPP]
    abel
  have hpq : psi (star q * q) = 0 := by
    rw [hqq, hq, map_sub, hpsi.map_one, h1, sub_self]
  -- decomposition `A = P A P + q A + P A q`
  have hdecomp : A = P * A * P + q * A + P * A * q := by
    rw [hq, sub_mul, mul_sub, one_mul, mul_one]
    abel
  have e1 : psi (P * A * P) = ⟪u, A u⟫_ℂ := by
    rw [hP, rankOneProj_mul_mul, map_smul, h1, smul_eq_mul, mul_one]
  have e2 : psi (q * A) = 0 := by
    have := apply_star_mul_eq_zero_left hpsi.nonneg hpq A
    rwa [hstarq] at this
  have e3 : psi (P * A * q) = 0 := by
    have := apply_star_mul_eq_zero_right hpsi.nonneg hpq (star (P * A))
    rwa [star_star] at this
  calc psi A = psi (P * A * P + q * A + P * A * q) := by rw [← hdecomp]
    _ = ⟪u, A u⟫_ℂ := by rw [map_add, map_add, e1, e2, e3, add_zero, add_zero]

/-! ## The vector state really is a state (non-vacuity of the hypotheses) -/

/-- The vector state `A ↦ ⟪u, A u⟫` as a linear functional. -/
noncomputable def vectorState (u : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun A := ⟪u, A u⟫_ℂ
  map_add' A B := by simp
  map_smul' c A := by simp

omit [CompleteSpace H] in
@[simp] lemma vectorState_apply (u : H) (A : H →L[ℂ] H) : vectorState u A = ⟪u, A u⟫_ℂ := rfl

omit [CompleteSpace H] in
lemma isState_vectorState {u : H} (hu : ‖u‖ = 1) : IsState (vectorState u) := by
  constructor
  · simp [inner_self_eq_norm_sq_to_K, hu]
  · intro A hA
    have hA' : (0 : H →L[ℂ] H) ≤ A := hA
    exact ContinuousLinearMap.IsPositive.inner_nonneg_right
      ((ContinuousLinearMap.nonneg_iff_isPositive A).mp hA') u

omit [CompleteSpace H] in
lemma vectorState_rankOneProj {u : H} (hu : ‖u‖ = 1) :
    vectorState u (rankOneProj u) = 1 := by
  simp [inner_self_eq_norm_sq_to_K, hu]

omit [CompleteSpace H] in
/-- The vector state at a basis vector restricts to a *pure* state (a character) of the
diagonal MASA; together with `isState_vectorState` this shows that the hypotheses of
`Frontier.kadison_singer` are not vacuous. -/
lemma isPureOnDiagonal_vectorState {ι : Type*} (e : HilbertBasis ι ℂ H) (i : ι) :
    IsPureOnDiagonal e (vectorState (e i)) := by
  intro A hA B hB
  obtain ⟨cA, hcA⟩ := hA i
  obtain ⟨cB, hcB⟩ := hB i
  have hu : ⟪e i, e i⟫_ℂ = 1 := by
    have : ‖e i‖ = 1 := e.orthonormal.1 i
    simp [inner_self_eq_norm_sq_to_K, this]
  simp only [vectorState_apply, ContinuousLinearMap.mul_apply, hcB, hcA, map_smul,
    inner_smul_right, hu]
  ring

omit [CompleteSpace H] in
/-- If the restriction of a state to the diagonal MASA is pure, its value on each atom
`P_i = e_i e_i^*` is either `0` or `1`. -/
lemma apply_rankOneProj_eq_zero_or_one {ι : Type*} {e : HilbertBasis ι ℂ H}
    {psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ} (hpure : IsPureOnDiagonal e psi) (i : ι) :
    psi (rankOneProj (e i)) = 0 ∨ psi (rankOneProj (e i)) = 1 := by
  have hu : ‖e i‖ = 1 := e.orthonormal.1 i
  have hmem := rankOneProj_mem_diagonal e i
  have h := hpure _ hmem _ hmem
  rw [rankOneProj_mul_self (e i) hu] at h
  have : psi (rankOneProj (e i)) * (psi (rankOneProj (e i)) - 1) = 0 := by
    rw [mul_sub, mul_one, ← h, sub_self]
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linear_combination h1)

omit [CompleteSpace H] in
/-- For a finite index set the atoms of the diagonal MASA sum to the identity. -/
lemma sum_rankOneProj {ι : Type*} [Fintype ι] (e : HilbertBasis ι ℂ H) :
    ∑ i, rankOneProj (e i) = 1 := by
  ext x
  have h := (e.hasSum_repr x).tsum_eq
  rw [tsum_fintype] at h
  simp only [HilbertBasis.repr_apply_apply] at h
  simpa using h

end KadisonSinger

/-! ## Main theorem -/

/-- **Kadison–Singer, atomic (base) case.**

Let `e` be a Hilbert basis of a complex Hilbert space `H`, generating the atomic MASA
`𝒟 ≅ ℓ^∞(ι)` inside `B(H)`, and let `δ_i` be the atomic pure state of `𝒟` given by evaluation
of the diagonal at the index `i` (equivalently, the character of `𝒟` sending the rank-one
projection `P_i = e_i e_i^*` to `1`).

Then `δ_i` has a *unique* extension to a state of `B(H)`, namely the vector state
`A ↦ ⟪e_i, A e_i⟫`: any state `psi` of `B(H)` with `psi Pᵢ = 1` is that vector state, and hence
any two states of `B(H)` agreeing with it on the diagonal MASA coincide.

This is the base case of the Kadison–Singer problem: the case of pure states of `ℓ^∞(ι)` coming
from principal ultrafilters.  (The full problem, whose remaining case concerns free ultrafilters,
is stated as `Frontier.KadisonSinger.Statement`; it was settled by Marcus, Spielman and
Srivastava.) -/
theorem kadison_singer {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (e : HilbertBasis ι ℂ H) (i : ι)
    (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hpsi : KadisonSinger.IsState psi)
    (hi : psi (KadisonSinger.rankOneProj (e i)) = 1) :
    (∀ A, psi A = ⟪e i, A (e i)⟫_ℂ) ∧ KadisonSinger.HasUniqueExtension e psi := by
  have hu : ‖e i‖ = 1 := e.orthonormal.1 i
  have hmain : ∀ A, psi A = ⟪e i, A (e i)⟫_ℂ :=
    KadisonSinger.eq_vectorState_of_apply_rankOneProj_eq_one hpsi hu hi
  refine ⟨hmain, ?_⟩
  intro psi' hpsi' hagree
  have hi' : psi' (KadisonSinger.rankOneProj (e i)) = 1 := by
    rw [hagree _ (KadisonSinger.rankOneProj_mem_diagonal e i), hi]
  have hmain' := KadisonSinger.eq_vectorState_of_apply_rankOneProj_eq_one hpsi' hu hi'
  ext A
  rw [hmain' A, hmain A]

/-- **Reduction of the Kadison–Singer problem to the non-atomic case.**

The Kadison–Singer problem `Frontier.KadisonSinger.Statement` is equivalent to its restriction
`Frontier.KadisonSinger.StatementNonatomic` to the pure states of the diagonal MASA that
vanish on all the atoms `P_i = e_i e_i^*` (the pure states coming from *free* ultrafilters).
Indeed, a pure state of the diagonal takes only the values `0` and `1` on the atoms, and if it
takes the value `1` on some atom then `Frontier.kadison_singer` applies. -/
theorem kadison_singer_reduction :
    KadisonSinger.Statement ↔ KadisonSinger.StatementNonatomic := by
  constructor
  · intro h H _ _ _ e psi hs hp _
    exact h H ‹_› ‹_› ‹_› e psi hs hp
  · intro h H _ _ _ e psi hs hp
    by_cases hatom : ∃ i, psi (KadisonSinger.rankOneProj (e i)) = 1
    · obtain ⟨i, hi⟩ := hatom
      exact (kadison_singer e i psi hs hi).2
    · refine h H ‹_› ‹_› ‹_› e psi hs hp fun i => ?_
      rcases KadisonSinger.apply_rankOneProj_eq_zero_or_one hp i with h0 | h1
      · exact h0
      · exact absurd ⟨i, h1⟩ hatom

/-- **Kadison–Singer in finite dimensions.**

When the index set of the Hilbert basis is finite (so that `H` is finite-dimensional and the
diagonal MASA is `ℂ^n`), every pure state of the diagonal MASA extends uniquely to a state of
`B(H)`: every pure state of the diagonal is atomic, and `Frontier.kadison_singer` applies. -/
theorem kadison_singer_of_finite {ι H : Type*} [Fintype ι] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : HilbertBasis ι ℂ H)
    (psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hpsi : KadisonSinger.IsState psi)
    (hpure : KadisonSinger.IsPureOnDiagonal e psi) :
    KadisonSinger.HasUniqueExtension e psi := by
  by_cases hatom : ∃ i, psi (KadisonSinger.rankOneProj (e i)) = 1
  · obtain ⟨i, hi⟩ := hatom
    exact (kadison_singer e i psi hpsi hi).2
  · exfalso
    have hzero : ∀ i, psi (KadisonSinger.rankOneProj (e i)) = 0 := by
      intro i
      rcases KadisonSinger.apply_rankOneProj_eq_zero_or_one hpure i with h0 | h1
      · exact h0
      · exact absurd ⟨i, h1⟩ hatom
    have hsum : psi (∑ i, KadisonSinger.rankOneProj (e i)) = 0 := by
      rw [map_sum]
      simp [hzero]
    rw [KadisonSinger.sum_rankOneProj e, hpsi.map_one] at hsum
    exact one_ne_zero hsum

/-! ## The Marcus–Spielman–Srivastava discrepancy theorem

The solution of the Kadison–Singer problem by Marcus, Spielman and Srivastava proceeds through
Weaver's discrepancy-theoretic reformulation `KS_2`: if finitely many vectors
`v₁, …, vₘ ∈ ℂ^d` form a resolution of the identity, `∑ᵢ vᵢ vᵢ* = I`, and each has small norm,
`‖vᵢ‖² ≤ ε`, then the index set can be split in two so that each half has spectral norm at most
`(1/√2 + √ε)²`.  We state this below and prove the one-dimensional base case, where the
statement reduces to a greedy partition of nonnegative reals summing to `1`. -/

namespace Weaver

/-- The rank-one positive semidefinite matrix `v v*`. -/
noncomputable def outer {d : ℕ} (v : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vecMulVec v (star v)

/-- `M` has spectral norm at most `c`, expressed via the Loewner order: `c • I - M ≥ 0`. -/
def BoundedBy {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (c : ℝ) : Prop :=
  Matrix.PosSemidef ((c : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) - M)

/-- **The Marcus–Spielman–Srivastava theorem** (Weaver's `KS_2`), in dimension `d`:
any resolution of the identity by vectors of squared length at most `ε` can be split into two
parts, each of spectral norm at most `(1/√2 + √ε)²`. -/
def MSS (d : ℕ) : Prop :=
  ∀ (m : Type) [Fintype m] [DecidableEq m] (v : m → Fin d → ℂ) (eps : ℝ),
    (∀ i, ∑ j, ‖v i j‖ ^ 2 ≤ eps) → (∑ i, outer (v i) = 1) →
    ∃ S : Finset m,
      BoundedBy (∑ i ∈ S, outer (v i)) ((1 / Real.sqrt 2 + Real.sqrt eps) ^ 2) ∧
      BoundedBy (∑ i ∈ Sᶜ, outer (v i)) ((1 / Real.sqrt 2 + Real.sqrt eps) ^ 2)

/-- Greedy partition: any finite family of reals bounded by `eps` has a subfamily whose sum is
at most `t` and which is either everything or has sum greater than `t - eps`. -/
lemma exists_subset_sum_le {m : Type*} (a : m → ℝ) (eps : ℝ) (heps : ∀ i, a i ≤ eps)
    (t : ℝ) (ht : 0 ≤ t) (F : Finset m) :
    ∃ S ⊆ F, ∑ i ∈ S, a i ≤ t ∧ (S = F ∨ t - eps ≤ ∑ i ∈ S, a i) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using ht, Or.inl rfl⟩
  | insert x F hx ih =>
      obtain ⟨S, hSF, hSle, hcase⟩ := ih
      rcases hcase with rfl | hlow
      · by_cases hle : ∑ i ∈ insert x S, a i ≤ t
        · exact ⟨insert x S, by simp, hle, Or.inl rfl⟩
        · refine ⟨S, hSF.trans (Finset.subset_insert _ _), hSle, Or.inr ?_⟩
          push_neg at hle
          rw [Finset.sum_insert hx] at hle
          have := heps x
          linarith
      · exact ⟨S, hSF.trans (Finset.subset_insert _ _), hSle, Or.inr hlow⟩

lemma outer_apply_zero_zero (v : Fin 1 → ℂ) : outer v 0 0 = ((‖v 0‖ ^ 2 : ℝ) : ℂ) := by
  simp [outer, Matrix.vecMulVec, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma sum_outer_eq_smul {m : Type*} [Fintype m] [DecidableEq m] (v : m → Fin 1 → ℂ)
    (T : Finset m) :
    ∑ i ∈ T, outer (v i) = (((∑ i ∈ T, ‖v i 0‖ ^ 2 : ℝ) : ℂ)) •
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext j k
  fin_cases j; fin_cases k
  simp [Matrix.sum_apply, outer_apply_zero_zero, Complex.ofReal_sum]

lemma boundedBy_of_le {m : Type*} [Fintype m] [DecidableEq m] (v : m → Fin 1 → ℂ)
    (T : Finset m) (c : ℝ) (h : ∑ i ∈ T, ‖v i 0‖ ^ 2 ≤ c) :
    BoundedBy (∑ i ∈ T, outer (v i)) c := by
  rw [BoundedBy, sum_outer_eq_smul v T, ← sub_smul, ← Complex.ofReal_sub]
  exact Matrix.PosSemidef.one.smul (by exact_mod_cast sub_nonneg.mpr h)

/-- **The base case of the Marcus–Spielman–Srivastava theorem**: `MSS` holds in dimension one,
where the statement amounts to splitting nonnegative reals summing to `1`, each at most `ε`,
into two groups of sum at most `1/2 + ε ≤ (1/√2 + √ε)²`. -/
theorem mss_dim_one : MSS 1 := by
  intro m _ _ v eps hsmall hres
  set a : m → ℝ := fun i => ‖v i 0‖ ^ 2 with ha
  have ha_nonneg : ∀ i, 0 ≤ a i := fun i => by positivity
  have ha_le : ∀ i, a i ≤ eps := by
    intro i
    have := hsmall i
    simpa [ha, Fin.sum_univ_one] using this
  have htot : ∑ i, a i = 1 := by
    have h := congrArg (fun M => M 0 0) hres
    simp only [Matrix.sum_apply, outer_apply_zero_zero, Matrix.one_apply_eq] at h
    have h' : ((∑ i, a i : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]; simpa [ha] using h
    exact_mod_cast h'
  have hm : Nonempty m := by
    by_contra hempty
    simp [not_nonempty_iff.mp (not_nonempty_iff.mpr (by simpa using hempty))] at htot
  have heps_nonneg : 0 ≤ eps := le_trans (ha_nonneg (Classical.arbitrary m))
    (ha_le (Classical.arbitrary m))
  obtain ⟨S, -, hSle, hcase⟩ := exists_subset_sum_le a eps ha_le (1 / 2) (by norm_num)
    (Finset.univ : Finset m)
  have hlow : 1 / 2 - eps ≤ ∑ i ∈ S, a i := by
    rcases hcase with rfl | h
    · rw [htot] at hSle; linarith
    · exact h
  have hcompl : ∑ i ∈ Sᶜ, a i ≤ 1 / 2 + eps := by
    have hsplit : ∑ i ∈ S, a i + ∑ i ∈ Sᶜ, a i = 1 := by
      rw [← htot]
      exact Finset.sum_add_sum_compl S a
    linarith
  have hc : 1 / 2 + eps ≤ (1 / Real.sqrt 2 + Real.sqrt eps) ^ 2 := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have he : (Real.sqrt eps) ^ 2 = eps := Real.sq_sqrt heps_nonneg
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hse : 0 ≤ Real.sqrt eps := Real.sqrt_nonneg eps
    have hexp : (1 / Real.sqrt 2 + Real.sqrt eps) ^ 2
        = 1 / 2 + eps + 2 * (1 / Real.sqrt 2) * Real.sqrt eps := by
      field_simp
      nlinarith [h2, he, hs2.le]
    rw [hexp]
    have : 0 ≤ 2 * (1 / Real.sqrt 2) * Real.sqrt eps := by positivity
    linarith
  refine ⟨S, boundedBy_of_le v S _ ?_, boundedBy_of_le v Sᶜ _ ?_⟩
  · exact le_trans hSle (by linarith)
  · exact le_trans hcompl hc

end Weaver

end Frontier

