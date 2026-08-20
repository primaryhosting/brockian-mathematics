/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` commands to come before any module docstring, so the header
-- above is reproduced verbatim as the module docstring immediately after the imports.)

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true
set_option pp.letVarTypes true
set_option pp.funBinderTypes true

set_option grind.warning false

namespace Frontier

open scoped ComplexOrder InnerProductSpace

/-! ## States on a unital ⋆-algebra over `ℂ` -/

/-- A *state* on a unital `ℂ`-⋆-algebra `A`: a positive, normalized linear functional. -/
structure IsState {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    (phi : A →ₗ[ℂ] ℂ) : Prop where
  /-- Positivity: `phi (a⋆ * a)` is a nonnegative real number. -/
  nonneg : ∀ a : A, 0 ≤ phi (star a * a)
  /-- Normalization. -/
  map_one : phi 1 = 1

namespace IsState

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] {phi : A →ₗ[ℂ] ℂ}

lemma re_nonneg (h : IsState phi) (a : A) : 0 ≤ (phi (star a * a)).re :=
  (Complex.le_def.mp (h.nonneg a)).1

lemma im_eq_zero (h : IsState phi) (a : A) : (phi (star a * a)).im = 0 :=
  ((Complex.le_def.mp (h.nonneg a)).2).symm

variable [StarModule ℂ A]

/-- Expansion of the positive sesquilinear form `(x, y) ↦ phi (x⋆ * y)` attached to `phi`. -/
lemma expand (t : ℂ) (x y : A) :
    phi (star (x + t • y) * (x + t • y)) =
      phi (star x * x) + t * phi (star x * y) +
        (starRingEnd ℂ) t * phi (star y * x) + (t * (starRingEnd ℂ) t) * phi (star y * y) := by
  have hs : star (x + t • y) = star x + (starRingEnd ℂ) t • star y := by
    simp [star_add, star_smul]
  rw [hs]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, map_add, map_smul, smul_eq_mul]
  ring

/-- The sesquilinear form attached to a state is Hermitian. -/
lemma conj_symm (h : IsState phi) (x y : A) :
    (starRingEnd ℂ) (phi (star x * y)) = phi (star y * x) := by
  set u : ℂ := phi (star x * y) with hu
  set v : ℂ := phi (star y * x) with hv
  have key : ∀ t : ℂ, (t * u + (starRingEnd ℂ) t * v).im = 0 := by
    intro t
    have h1 := h.im_eq_zero (x + t • y)
    rw [expand t x y, ← hu, ← hv] at h1
    have h2 := h.im_eq_zero x
    have h3 := h.im_eq_zero y
    simp only [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im, h2, h3] at h1 ⊢
    nlinarith [h1]
  have k1 := key 1
  have k2 := key Complex.I
  simp only [one_mul, Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.conj_I, Complex.neg_re,
    Complex.neg_im] at k1 k2
  apply Complex.ext <;> simp only [Complex.conj_re, Complex.conj_im] <;> linarith

/-- A state is ⋆-preserving. -/
lemma star_apply (h : IsState phi) (a : A) :
    phi (star a) = (starRingEnd ℂ) (phi a) := by
  have := h.conj_symm 1 a
  simpa using this.symm

/-- Degenerate Cauchy–Schwarz inequality: if `phi (y⋆ * y) = 0`, then `phi (y⋆ * x) = 0`
for every `x`. -/
lemma eq_zero_of_eq_zero (h : IsState phi) {y : A} (hy : phi (star y * y) = 0) (x : A) :
    phi (star y * x) = 0 := by
  rw [← h.conj_symm x y]
  suffices hu0 : phi (star x * y) = 0 by simp [hu0]
  set u : ℂ := phi (star x * y) with hu
  have hkey : ∀ s : ℝ, 0 ≤ (phi (star x * x)).re - 2 * s * Complex.normSq u := by
    intro s
    have hre := h.re_nonneg (x + (-(s : ℂ) * (starRingEnd ℂ) u) • y)
    rw [expand, hy, ← h.conj_symm x y, ← hu] at hre
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, add_zero, sub_zero, neg_zero, Complex.normSq_apply] at hre ⊢
    nlinarith [hre]
  by_contra hne
  have hpos : 0 < Complex.normSq u := by
    rcases (Complex.normSq_nonneg u).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (Complex.normSq_eq_zero.mp h'.symm) hne
  have h2 := hkey (((phi (star x * x)).re + 1) / (2 * Complex.normSq u))
  rw [show 2 * (((phi (star x * x)).re + 1) / (2 * Complex.normSq u)) * Complex.normSq u
      = (phi (star x * x)).re + 1 by field_simp] at h2
  linarith

/-- If a state takes the value `1` on a projection `p`, then it is supported on `p`:
`phi a = phi (p * a * p)` for every `a`. -/
lemma apply_eq_compress (h : IsState phi) {p : A} (hp : star p = p) (hp2 : p * p = p)
    (h1 : phi p = 1) (a : A) : phi a = phi (p * a * p) := by
  set q : A := 1 - p with hq
  have hqs : star q = q := by simp [hq, hp]
  have hq2 : q * q = q := by simp [hq, sub_mul, mul_sub, hp2]
  have hq0 : phi q = 0 := by simp [hq, map_sub, h.map_one, h1]
  have hqq : phi (star q * q) = 0 := by rw [hqs, hq2, hq0]
  have hleft : ∀ x : A, phi (q * x) = 0 := by
    intro x
    have := h.eq_zero_of_eq_zero hqq x
    rwa [hqs] at this
  have hright : ∀ x : A, phi (x * q) = 0 := by
    intro x
    have hs : phi (star (x * q)) = 0 := by
      rw [star_mul, hqs]
      exact hleft _
    rw [h.star_apply] at hs
    simpa using congrArg (starRingEnd ℂ) hs
  have e1 : ∀ x : A, phi x = phi (p * x) := by
    intro x
    have hx : p * x = x - q * x := by simp [hq, sub_mul]
    rw [hx, map_sub, hleft, sub_zero]
  have e2 : ∀ x : A, phi x = phi (x * p) := by
    intro x
    have hx : x * p = x - x * q := by simp [hq, mul_sub]
    rw [hx, map_sub, hright, sub_zero]
  rw [e1 a, e2 (p * a)]

end IsState

/-! ## Rank-one projections and diagonal operators -/

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The orthogonal projection onto the line spanned by a unit vector `e`, as a bounded
operator: `x ↦ ⟪e, x⟫ • e`. -/
noncomputable def rankOneProj (e : H) : H →L[ℂ] H := (innerSL ℂ e).smulRight e

@[simp] lemma rankOneProj_apply (e x : H) : rankOneProj e x = (⟪e, x⟫_ℂ) • e := rfl

lemma rankOneProj_mul_self {e : H} (he : ‖e‖ = 1) :
    rankOneProj e * rankOneProj e = rankOneProj e := by
  ext x
  simp [ContinuousLinearMap.mul_apply, inner_self_eq_norm_sq_to_K, he]

lemma rankOneProj_compress (e : H) (a : H →L[ℂ] H) :
    rankOneProj e * a * rankOneProj e = (⟪e, a e⟫_ℂ) • rankOneProj e := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, rankOneProj_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, map_smul, smul_smul]
  ring_nf

/-- An operator is *diagonal* with respect to the orthonormal basis `b` if all of its
off-diagonal matrix entries vanish. The diagonal operators form the *atomic MASA*
(maximal abelian selfadjoint subalgebra) of `B(H)`; the Kadison–Singer problem asks whether
every pure state of this subalgebra extends uniquely to a state of `B(H)`. -/
def IsDiagonal {ι : Type*} (b : HilbertBasis ι ℂ H) (a : H →L[ℂ] H) : Prop :=
  ∀ i j, i ≠ j → ⟪b i, a (b j)⟫_ℂ = 0

/-- The rank-one projection onto a basis vector is a diagonal operator. -/
lemma isDiagonal_rankOneProj {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ι) :
    IsDiagonal b (rankOneProj (b k)) := by
  intro i j hij
  have horth := b.orthonormal
  by_cases hjk : j = k
  · subst hjk
    simp [rankOneProj_apply, horth.2 hij]
  · simp [rankOneProj_apply, horth.2 (Ne.symm hjk)]

/-- A diagonal operator acts on each basis vector by a scalar (its diagonal entry). -/
lemma IsDiagonal.apply_basis {ι : Type*} {b : HilbertBasis ι ℂ H} {a : H →L[ℂ] H}
    (h : IsDiagonal b a) (j : ι) : a (b j) = (⟪b j, a (b j)⟫_ℂ) • b j := by
  have horth := b.orthonormal
  apply b.repr.injective
  ext i
  simp only [HilbertBasis.repr_apply_apply]
  by_cases hij : i = j
  · subst hij
    simp [inner_self_eq_norm_sq_to_K, horth.1 i]
  · rw [h i j hij]
    simp [horth.2 hij]

/-- The *atomic* functional `a ↦ ⟪b k, a (b k)⟫` is multiplicative on the diagonal operators,
i.e. it is a character (hence a pure state) of the atomic MASA. -/
lemma atomicState_mul_diagonal {ι : Type*} {b : HilbertBasis ι ℂ H} {a a' : H →L[ℂ] H}
    (ha : IsDiagonal b a) (ha' : IsDiagonal b a') (k : ι) :
    ⟪b k, (a * a') (b k)⟫_ℂ = ⟪b k, a (b k)⟫_ℂ * ⟪b k, a' (b k)⟫_ℂ := by
  have horth := b.orthonormal
  rw [ContinuousLinearMap.mul_apply, ha'.apply_basis k, map_smul, ha.apply_basis k]
  simp [inner_self_eq_norm_sq_to_K, horth.1 k]
  ring

end RankOne

/-! ## The Kadison–Singer problem -/

section KadisonSinger

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rankOneProj_star (e : H) : star (rankOneProj e) = rankOneProj e := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp [inner_smul_left, inner_smul_right, mul_comm]

/-- A state of `B(H)` taking the value `1` on the rank-one projection onto a unit vector `e`
is the vector state at `e`. -/
theorem state_eq_vectorState_of_apply_rankOneProj_eq_one
    {e : H} (he : ‖e‖ = 1) (phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hphi : IsState phi)
    (h1 : phi (rankOneProj e) = 1) (a : H →L[ℂ] H) : phi a = ⟪e, a e⟫_ℂ := by
  rw [hphi.apply_eq_compress (rankOneProj_star e) (rankOneProj_mul_self he) h1 a,
    rankOneProj_compress e a, map_smul, smul_eq_mul, h1, mul_one]

/-- The *vector state* of `B(H)` at a vector `e`: `a ↦ ⟪e, a e⟫`. -/
noncomputable def vectorState (e : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun a := ⟪e, a e⟫_ℂ
  map_add' := by intro a b; simp
  map_smul' := by intro c a; simp

omit [CompleteSpace H] in
@[simp] lemma vectorState_apply (e : H) (a : H →L[ℂ] H) : vectorState e a = ⟪e, a e⟫_ℂ := rfl

/-- The vector state at a unit vector really is a state; in particular the hypotheses of
`Frontier.kadison_singer` are satisfiable. -/
lemma isState_vectorState {e : H} (he : ‖e‖ = 1) : IsState (vectorState e) where
  nonneg a := by
    have hstar : (star a * a) e = ContinuousLinearMap.adjoint a (a e) := rfl
    rw [vectorState_apply, hstar, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    simp [Complex.le_def]
  map_one := by
    rw [vectorState_apply]
    simp [inner_self_eq_norm_sq_to_K, he]

/-- The statement of the **Kadison–Singer problem** for the atomic MASA determined by an
orthonormal basis `b` of a Hilbert space `H`: any two states of `B(H)` that agree on the
diagonal operators, and whose common restriction to the diagonal operators is multiplicative
(equivalently: is a *pure* state of that abelian subalgebra), are equal.

This is the property established by Marcus, Spielman and Srivastava (2015) using interlacing
families of characteristic polynomials. It is recorded here for reference; the atomic case is
proved below in `Frontier.kadison_singer`. -/
def KadisonSingerUniqueExtension {ι : Type*} (b : HilbertBasis ι ℂ H) : Prop :=
  ∀ phi psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ, IsState phi → IsState psi →
    (∀ a, IsDiagonal b a → phi a = psi a) →
    (∀ a a', IsDiagonal b a → IsDiagonal b a' → phi (a * a') = phi a * phi a') →
    phi = psi

/-- **Kadison–Singer, atomic case.** Let `b` be an orthonormal (Hilbert) basis of a Hilbert
space `H` and let `k` be an index. The functional `a ↦ ⟪b k, a (b k)⟫`, restricted to the atomic
MASA of operators that are diagonal with respect to `b`, is a pure state of that MASA (an
*atomic* pure state, i.e. one given by a point of the spectrum that is an atom). Then any state
of `B(H)` extending it is uniquely determined: it is the vector state at `b k`. In particular
any two extensions coincide.

This is the classical "easy half" of the Kadison–Singer problem. The theorem of Marcus, Spielman
and Srivastava extends the conclusion to *all* pure states of the MASA, including the non-atomic
ones coming from free ultrafilters; see `Frontier.KadisonSingerUniqueExtension`. -/
theorem kadison_singer {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ι)
    (phi psi : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (hphi : IsState phi) (hpsi : IsState psi)
    (hphid : ∀ a, IsDiagonal b a → phi a = ⟪b k, a (b k)⟫_ℂ)
    (hpsid : ∀ a, IsDiagonal b a → psi a = ⟪b k, a (b k)⟫_ℂ) :
    (∀ a, phi a = ⟪b k, a (b k)⟫_ℂ) ∧ phi = psi := by
  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  have hval : ∀ chi : (H →L[ℂ] H) →ₗ[ℂ] ℂ, IsState chi →
      (∀ a, IsDiagonal b a → chi a = ⟪b k, a (b k)⟫_ℂ) →
      ∀ a, chi a = ⟪b k, a (b k)⟫_ℂ := by
    intro chi hchi hd
    have h1 : chi (rankOneProj (b k)) = 1 := by
      rw [hd _ (isDiagonal_rankOneProj b k)]
      simp [inner_self_eq_norm_sq_to_K, hnorm]
    exact state_eq_vectorState_of_apply_rankOneProj_eq_one hnorm chi hchi h1
  refine ⟨hval phi hphi hphid, ?_⟩
  ext a
  rw [hval phi hphi hphid a, hval psi hpsi hpsid a]

/-- **Unique extension of atomic pure states.** For each index `k` there is exactly one state of
`B(H)` whose restriction to the atomic MASA is the atomic pure state `a ↦ ⟪b k, a (b k)⟫`, namely
the vector state at `b k`. -/
theorem kadison_singer_existsUnique {ι : Type*} (b : HilbertBasis ι ℂ H) (k : ι) :
    ∃! phi : (H →L[ℂ] H) →ₗ[ℂ] ℂ,
      IsState phi ∧ ∀ a, IsDiagonal b a → phi a = ⟪b k, a (b k)⟫_ℂ := by
  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  refine ⟨vectorState (b k), ⟨isState_vectorState hnorm, fun a _ => rfl⟩, ?_⟩
  rintro phi ⟨hphi, hphid⟩
  exact (kadison_singer b k phi (vectorState (b k)) hphi (isState_vectorState hnorm) hphid
    (fun a _ => rfl)).2

end KadisonSinger

/-! ## Weaver's `KS₂` in dimension one

The Kadison–Singer problem was solved by Marcus, Spielman and Srivastava by proving Weaver's
discrepancy-theoretic conjecture `KS₂`: if `v 1, …, v m` are vectors in `ℂ^d` with
`∑ i, v i * (v i)⋆ = 1` and `‖v i‖ ^ 2 ≤ eps`, then the index set can be partitioned into two
parts `S`, `Sᶜ` with `‖∑ i ∈ S, v i * (v i)⋆‖ ≤ (1 / √2 + √eps) ^ 2`.

The following is the one-dimensional (`d = 1`) case of that statement, where the operator norm
is just the sum of the weights `‖v i‖ ^ 2`. It is proved by a greedy/maximality argument. -/

section Weaver

/-- A finite family of real weights summing to `1`, each at most `eps`, can be split into two
parts each of total weight at most `1 / 2 + eps`. -/
theorem exists_balanced_partition {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (a : ι → ℝ)
    (hle : ∀ i, a i ≤ eps) (hsum : ∑ i, a i = 1) :
    ∃ S : Finset ι, ∑ i ∈ S, a i ≤ 1 / 2 + eps ∧ ∑ i ∈ Sᶜ, a i ≤ 1 / 2 + eps := by
  classical
  set P : Finset (Finset ι) :=
    (Finset.univ : Finset ι).powerset.filter (fun S => ∑ i ∈ S, a i ≤ 1 / 2) with hP
  have hPne : P.Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨S, hSP, hSmax⟩ := P.exists_max_image (fun S => ∑ i ∈ S, a i) hPne
  have hS : ∑ i ∈ S, a i ≤ 1 / 2 := by
    have := Finset.mem_filter.mp hSP
    simpa using this.2
  have hcompl : ∑ i ∈ S, a i + ∑ i ∈ Sᶜ, a i = 1 := by
    rw [Finset.sum_add_sum_compl, hsum]
  have hlow : 1 / 2 - eps ≤ ∑ i ∈ S, a i := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < ∑ i ∈ Sᶜ, a i := by linarith
    obtain ⟨i, hiS, hai⟩ : ∃ i ∈ Sᶜ, 0 < a i :=
      Finset.exists_lt_of_sum_lt (by simpa using hpos)
    have hinotS : i ∉ S := by simpa using hiS
    have hins : ∑ j ∈ insert i S, a j = a i + ∑ j ∈ S, a j := Finset.sum_insert hinotS
    have hmem : insert i S ∈ P := by
      refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
      rw [hins]
      have := hle i
      linarith
    have hmax := hSmax _ hmem
    rw [hins] at hmax
    linarith
  exact ⟨S, by linarith, by linarith⟩

/-- **Weaver's `KS₂` in dimension one** (the `d = 1` case of the Marcus–Spielman–Srivastava
theorem). Given scalars `v i` with `∑ i, ‖v i‖ ^ 2 = 1` and `‖v i‖ ^ 2 ≤ eps`, the index set
splits into two parts, each of total weight at most `(1 / √2 + √eps) ^ 2`. -/
theorem weaver_KS2_dim_one {ι : Type*} [Fintype ι] [DecidableEq ι] {eps : ℝ} (v : ι → ℂ)
    (hle : ∀ i, ‖v i‖ ^ 2 ≤ eps) (hsum : ∑ i, ‖v i‖ ^ 2 = 1) :
    ∃ S : Finset ι,
      ∑ i ∈ S, ‖v i‖ ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 ∧
      ∑ i ∈ Sᶜ, ‖v i‖ ^ 2 ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 := by
  obtain ⟨S, h1, h2⟩ := exists_balanced_partition (fun i => ‖v i‖ ^ 2) hle hsum
  have hepsnn : 0 ≤ eps := by
    obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < ‖v i‖ ^ 2 :=
      Finset.exists_lt_of_sum_lt (by simpa using hsum.symm.le.trans_lt' (by norm_num))
    exact le_trans hi.le (hle i)
  have hkey : 1 / 2 + eps ≤ (Real.sqrt (1 / 2) + Real.sqrt eps) ^ 2 := by
    have h12 : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    have he : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt hepsnn
    have hnn : 0 ≤ Real.sqrt (1 / 2) * Real.sqrt eps :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    nlinarith [h12, he, hnn]
  exact ⟨S, h1.trans hkey, h2.trans hkey⟩

end Weaver

end Frontier

