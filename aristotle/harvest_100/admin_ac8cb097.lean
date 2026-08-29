/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
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

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/
theorem exists_col_expansion {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (X : Matrix m n ℂ) :
    ∃ e cf : Fin X.rank → m → ℂ,
      ∀ i j, X i j = ∑ p, e p i * (∑ β, cf p β * X β j) := by
  classical
  set V : Submodule ℂ (m → ℂ) := Submodule.span ℂ (Set.range X.col) with hV
  have hfr : finrank ℂ V = X.rank := (Matrix.rank_eq_finrank_span_cols X).symm
  let bas : Basis (Fin X.rank) ℂ V := (Module.finBasis ℂ V).reindex (finCongr hfr)
  have hext : ∀ p : Fin X.rank, ∃ g : (m → ℂ) →ₗ[ℂ] ℂ, g.comp V.subtype = bas.coord p :=
    fun p => (bas.coord p).exists_extend
  choose g hg using hext
  refine ⟨fun p => (bas p : m → ℂ), fun p β => g p (Pi.single β 1), ?_⟩
  intro i j
  have hc : X.col j ∈ V := Submodule.subset_span ⟨j, rfl⟩
  have hrepr : ((⟨X.col j, hc⟩ : V) : m → ℂ)
      = ∑ p, (bas.coord p ⟨X.col j, hc⟩) • ((bas p : V) : m → ℂ) := by
    have h1 := bas.sum_repr ⟨X.col j, hc⟩
    calc ((⟨X.col j, hc⟩ : V) : m → ℂ)
        = ((∑ p, (bas.repr ⟨X.col j, hc⟩ p) • bas p : V) : m → ℂ) := by rw [h1]
      _ = _ := by push_cast [Submodule.coe_sum]; rfl
  have hcoord : ∀ p, (bas.coord p ⟨X.col j, hc⟩ : ℂ) = ∑ β, g p (Pi.single β 1) * X β j := by
    intro p
    have h2 : (bas.coord p) ⟨X.col j, hc⟩ = g p (X.col j) := by
      have := congrArg (fun (f : V →ₗ[ℂ] ℂ) => f ⟨X.col j, hc⟩) (hg p)
      simpa using this.symm
    rw [h2]
    have hsplit : (X.col j : m → ℂ) = ∑ β, (X β j) • (Pi.single β (1:ℂ) : m → ℂ) := by
      funext b; simp [Pi.single_apply, Matrix.col]
    rw [hsplit, map_sum]
    simp [mul_comm]
  have h3 := congrFun hrepr i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [show X i j = X.col j i from rfl, h3]
  exact Finset.sum_congr rfl (fun p _ => by rw [hcoord p]; ring)

/-- A block matrix with `card R` identical diagonal blocks `σ` has rank at least
`card R * σ.rank`. -/
theorem rank_blockdiag_ge {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    (σ : Matrix A A ℂ) :
    Fintype.card R * σ.rank ≤
      (Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σ p.2 q.2 else 0)).rank := by
  classical
  set D : Matrix (R × A) (R × A) ℂ :=
    Matrix.of (fun p q => if p.1 = q.1 then σ p.2 q.2 else 0) with hD
  set W := LinearMap.range σ.mulVecLin with hW
  have hfrW : finrank ℂ W = σ.rank := rfl
  let bs : Basis (Fin σ.rank) ℂ W := (Module.finBasis ℂ W).reindex (finCongr hfrW)
  set w : R × Fin σ.rank → (R × A → ℂ) :=
    fun x z => if z.1 = x.1 then ((bs x.2 : W) : A → ℂ) z.2 else 0 with hw
  have hmem : ∀ x, w x ∈ LinearMap.range D.mulVecLin := by
    rintro ⟨i, p⟩
    obtain ⟨y, hy⟩ := (bs p).2
    refine ⟨fun z => if z.1 = i then y z.2 else 0, ?_⟩
    funext z
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, hD, Matrix.of_apply, hw]
    by_cases h : z.1 = i
    · simp only [h]
      rw [← hy]
      simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, apply_ite]
    · simp only [h, if_false]
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases hx : x.1 = i <;> simp [hx, h]
  have hli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc x
    have hval : ∀ (j : R) (a : A), ∑ p : Fin σ.rank, c (j, p) * ((bs p : W) : A → ℂ) a = 0 := by
      intro j a
      have := congrFun hc (j, a)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hw, Pi.zero_apply,
        Fintype.sum_prod_type] at this
      simpa using this
    have hbsli : LinearIndependent ℂ (fun p : Fin σ.rank => ((bs p : W) : A → ℂ)) :=
      (bs.linearIndependent).map' W.subtype (by simp)
    rw [Fintype.linearIndependent_iff] at hbsli
    exact hbsli (fun p => c (x.1, p)) (by funext a; simpa using hval x.1 a) x.2
  have hli' := hli.of_comp (Submodule.subtype (LinearMap.range D.mulVecLin))
    (v := fun x => (⟨w x, hmem x⟩ : LinearMap.range D.mulVecLin))
  simpa [Matrix.rank, Fintype.card_prod] using hli'.fintype_card_le_finrank

/-- The `(R×A) | (B×C)` flattening of a tensor has rank at most the product of the ranks of its
`B` and `C` flattenings. -/
theorem rank_tensor_le {R A B C : Type*} [Fintype R] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] [DecidableEq R] [DecidableEq A]
    (T : R → A → B → C → ℂ) :
    (Matrix.of fun (p : R × A) (q : B × C) => T p.1 p.2 q.1 q.2).rank ≤
      (Matrix.of fun (b : B) (p : R × A × C) => T p.1 p.2.1 b p.2.2).rank *
      (Matrix.of fun (c : C) (p : R × A × B) => T p.1 p.2.1 p.2.2 c).rank := by
  classical
  set FB : Matrix B (R × A × C) ℂ := Matrix.of fun b p => T p.1 p.2.1 b p.2.2 with hFB
  set FC : Matrix C (R × A × B) ℂ := Matrix.of fun c p => T p.1 p.2.1 p.2.2 c with hFC
  obtain ⟨e, cf, he⟩ := exists_col_expansion FB
  set Z : Matrix C (Fin FB.rank × R × A) ℂ :=
    Matrix.of fun c x => ∑ β, cf x.1 β * T x.2.1 x.2.2 β c with hZ
  have hZrank : Z.rank ≤ FC.rank := by
    have hfac : Z = FC * (Matrix.of fun (y : R × A × B) (x : Fin FB.rank × R × A) =>
        if x.2 = (y.1, y.2.1) then cf x.1 y.2.2 else 0) := by
      funext c x
      simp only [hZ, hFC, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
      simp only [mul_ite, mul_zero]
      simp [Prod.ext_iff, eq_comm, ite_and, Finset.sum_ite_eq', mul_comm]
    rw [hfac]
    exact Matrix.rank_mul_le_left _ _
  obtain ⟨g, dg, hg⟩ := exists_col_expansion Z
  have key : ∀ i a b c, T i a b c
      = ∑ p : Fin FB.rank, ∑ s : Fin Z.rank,
          (e p b * g s c) * (∑ γ, dg s γ * Z γ (p, i, a)) := by
    intro i a b c
    have h1 : T i a b c = ∑ p, e p b * (∑ β, cf p β * T i a β c) := he b (i, a, c)
    have h2 : ∀ p, (∑ β, cf p β * T i a β c) = Z c (p, i, a) := by intro p; simp [hZ]
    have h3 : ∀ p, Z c (p, i, a) = ∑ s, g s c * (∑ γ, dg s γ * Z γ (p, i, a)) :=
      fun p => hg c (p, i, a)
    rw [h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [h2 p, h3 p, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hfac : (Matrix.of fun (p : R × A) (q : B × C) => T p.1 p.2 q.1 q.2)
      = (Matrix.of fun (p : R × A) (x : Fin FB.rank × Fin Z.rank) =>
            ∑ γ, dg x.2 γ * Z γ (x.1, p.1, p.2))
        * (Matrix.of fun (x : Fin FB.rank × Fin Z.rank) (q : B × C) => e x.1 q.1 * g x.2 q.2) := by
    funext p q
    simp only [Matrix.of_apply, Matrix.mul_apply, Fintype.sum_prod_type]
    rw [key p.1 p.2 q.1 q.2]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring
  rw [hfac]
  refine le_trans (Matrix.rank_mul_le_left _ _) ?_
  refine le_trans (Matrix.rank_le_card_width _) ?_
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Nat.mul_le_mul_left _ hZrank

/-- A nonzero matrix has positive rank. -/
theorem rank_pos_of_ne_zero {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (M : Matrix A B ℂ) (h : M ≠ 0) : 1 ≤ M.rank := by
  classical
  rcases Nat.eq_zero_or_pos M.rank with h0 | h1
  · exfalso
    have hb : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    apply h
    funext a b
    have hz : M.mulVec (Pi.single b 1) = 0 := by
      have hmem : M.mulVecLin (Pi.single b 1) ∈ LinearMap.range M.mulVecLin := ⟨_, rfl⟩
      rw [hb] at hmem
      simpa using hmem
    have := congrFun hz a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  · exact h1

theorem rank_smul_le {n : Type*} [Fintype n] [DecidableEq n] (c : ℂ) (X : Matrix n n ℂ) :
    (c • X).rank ≤ X.rank := by
  have h : c • X = (c • (1 : Matrix n n ℂ)) * X := by simp
  rw [h]; exact Matrix.rank_mul_le_right _ _

theorem double_sum_mul_conj_ne_zero {B C : Type*} [Fintype B] [Fintype C] (f : B → C → ℂ)
    (b0 : B) (c0 : C) (h : f b0 c0 ≠ 0) : (∑ b, ∑ c, f b c * conj (f b c)) ≠ 0 := by
  have hcast : (∑ b, ∑ c, f b c * conj (f b c))
      = ((∑ b, ∑ c, Complex.normSq (f b c) : ℝ) : ℂ) := by
    push_cast
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by
      simp [Complex.mul_conj]
  rw [hcast]
  simp only [ne_eq, Complex.ofReal_eq_zero]
  intro hz
  have hnn : ∀ b ∈ Finset.univ, (0:ℝ) ≤ ∑ c, Complex.normSq (f b c) :=
    fun b _ => Finset.sum_nonneg fun c _ => Complex.normSq_nonneg _
  have h5 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz b0 (Finset.mem_univ _)
  have h6 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun c (_ : c ∈ Finset.univ) => Complex.normSq_nonneg (f b0 c))).mp h5 c0 (Finset.mem_univ _)
  exact h (by simpa [Complex.normSq_eq_zero] using h6)

/-- **Core of the quantum Singleton bound.**

Let `T i a b c` be the coefficients of `card R` orthonormal vectors (indexed by `i : R`) in a
tripartite system `A ⊗ B ⊗ C`.  Assume that the reduced correlations on `A` and on `B` are
codeword independent (`hA`, `hB`), i.e. erasures of `A` and of `B` are correctable.  Then
`card R ≤ card C`. -/
theorem card_le_of_KL {R A B C : Type*} [Fintype R] [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (T : R → A → B → C → ℂ) (σA : Matrix A A ℂ) (σB : Matrix B B ℂ)
    (hA : ∀ i j a a', (∑ b, ∑ c, T i a b c * conj (T j a' b c)) = if i = j then σA a a' else 0)
    (hB : ∀ i j b b', (∑ a, ∑ c, T i a b c * conj (T j a b' c)) = if i = j then σB b b' else 0)
    (hne : ∃ i a b c, T i a b c ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  set K := Fintype.card R with hK
  set MA : Matrix (R × A) (B × C) ℂ := Matrix.of fun p q => T p.1 p.2 q.1 q.2 with hMA
  set MB : Matrix (R × B) (A × C) ℂ := Matrix.of fun p q => T p.1 q.1 p.2 q.2 with hMB
  set FA : Matrix A (R × B × C) ℂ := Matrix.of fun a p => T p.1 a p.2.1 p.2.2 with hFA
  set FB : Matrix B (R × A × C) ℂ := Matrix.of fun b p => T p.1 p.2.1 b p.2.2 with hFB
  set FC : Matrix C (R × A × B) ℂ := Matrix.of fun c p => T p.1 p.2.1 p.2.2 c with hFC
  -- Step 1 : correctability of `A` forces `rank MA ≥ K * rank σA`.
  have h1 : K * σA.rank ≤ MA.rank := by
    have hprod : MA * MAᴴ
        = Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σA p.2 q.2 else 0) := by
      funext p q
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMA, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def]
      exact hA p.1 q.1 p.2 q.2
    calc K * σA.rank
        ≤ (Matrix.of (fun (p q : R × A) => if p.1 = q.1 then σA p.2 q.2 else 0)).rank :=
          rank_blockdiag_ge σA
      _ = (MA * MAᴴ).rank := by rw [hprod]
      _ = MA.rank := Matrix.rank_self_mul_conjTranspose MA
  have h1' : K * σB.rank ≤ MB.rank := by
    have hprod : MB * MBᴴ
        = Matrix.of (fun (p q : R × B) => if p.1 = q.1 then σB p.2 q.2 else 0) := by
      funext p q
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMB, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def]
      exact hB p.1 q.1 p.2 q.2
    calc K * σB.rank
        ≤ (Matrix.of (fun (p q : R × B) => if p.1 = q.1 then σB p.2 q.2 else 0)).rank :=
          rank_blockdiag_ge σB
      _ = (MB * MBᴴ).rank := by rw [hprod]
      _ = MB.rank := Matrix.rank_self_mul_conjTranspose MB
  -- Step 2 : the two flattening bounds.
  have h2 : MA.rank ≤ FB.rank * FC.rank := rank_tensor_le T
  have h2' : MB.rank ≤ FA.rank * FC.rank := by
    have hmain := rank_tensor_le (fun (i : R) (b : B) (a : A) (c : C) => T i a b c)
    have e1 : (Matrix.of fun (a : A) (p : R × B × C) => T p.1 a p.2.1 p.2.2) = FA := rfl
    have e2 : (Matrix.of fun (c : C) (p : R × B × A) => T p.1 p.2.2 p.2.1 c)
        = FC.submatrix id (fun p => (p.1, p.2.2, p.2.1)) := rfl
    rw [e1, e2] at hmain
    have e3 : (FC.submatrix id (fun p : R × B × A => (p.1, p.2.2, p.2.1))).rank = FC.rank :=
      Matrix.rank_submatrix FC (Equiv.refl C) ((Equiv.refl R).prodCongr (Equiv.prodComm B A))
    rw [e3] at hmain
    exact hmain
  -- Step 3 : `rank FA ≤ rank σA` and `rank FB ≤ rank σB`.
  have h3 : FA.rank ≤ σA.rank := by
    have hprod : FA * FAᴴ = (K : ℂ) • σA := by
      funext a a'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hFA, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def, Matrix.smul_apply, smul_eq_mul]
      rw [show (∑ i : R, ∑ b : B, ∑ c : C, T i a b c * conj (T i a' b c))
            = ∑ _i : R, σA a a' from Finset.sum_congr rfl (fun i _ => by
              simpa using hA i i a a')]
      simp [hK, mul_comm]
    calc FA.rank = (FA * FAᴴ).rank := (Matrix.rank_self_mul_conjTranspose FA).symm
      _ = ((K : ℂ) • σA).rank := by rw [hprod]
      _ ≤ σA.rank := rank_smul_le _ _
  have h4 : FB.rank ≤ σB.rank := by
    have hprod : FB * FBᴴ = (K : ℂ) • σB := by
      funext b b'
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hFB, Matrix.of_apply,
        Fintype.sum_prod_type, RCLike.star_def, Matrix.smul_apply, smul_eq_mul]
      rw [show (∑ i : R, ∑ a : A, ∑ c : C, T i a b c * conj (T i a b' c))
            = ∑ _i : R, σB b b' from Finset.sum_congr rfl (fun i _ => by
              simpa using hB i i b b')]
      simp [hK, mul_comm]
    calc FB.rank = (FB * FBᴴ).rank := (Matrix.rank_self_mul_conjTranspose FB).symm
      _ = ((K : ℂ) • σB).rank := by rw [hprod]
      _ ≤ σB.rank := rank_smul_le _ _
  -- Step 4 : the reduced correlations are nonzero.
  obtain ⟨i0, a0, b0, c0, hne0⟩ := hne
  have hσA : 1 ≤ σA.rank := by
    refine rank_pos_of_ne_zero σA ?_
    intro h0
    refine double_sum_mul_conj_ne_zero (fun b c => T i0 a0 b c) b0 c0 hne0 ?_
    rw [hA i0 i0 a0 a0, h0]
    simp
  have hσB : 1 ≤ σB.rank := by
    refine rank_pos_of_ne_zero σB ?_
    intro h0
    refine double_sum_mul_conj_ne_zero (fun a c => T i0 a b0 c) a0 c0 hne0 ?_
    rw [hB i0 i0 b0 b0, h0]
    simp
  -- Step 5 : arithmetic.
  have hC : FC.rank ≤ Fintype.card C := Matrix.rank_le_card_height FC
  have i1 : K * σA.rank ≤ σB.rank * FC.rank :=
    le_trans (le_trans h1 h2) (Nat.mul_le_mul_right _ h4)
  have i2 : K * σB.rank ≤ σA.rank * FC.rank :=
    le_trans (le_trans h1' h2') (Nat.mul_le_mul_right _ h3)
  have key : K * K * (σA.rank * σB.rank) ≤ (FC.rank * FC.rank) * (σA.rank * σB.rank) := by
    calc K * K * (σA.rank * σB.rank) = (K * σA.rank) * (K * σB.rank) := by ring
      _ ≤ (σB.rank * FC.rank) * (σA.rank * FC.rank) := Nat.mul_le_mul i1 i2
      _ = (FC.rank * FC.rank) * (σA.rank * σB.rank) := by ring
  have hKK : K * K ≤ FC.rank * FC.rank :=
    Nat.le_of_mul_le_mul_right key (Nat.mul_pos hσA hσB)
  have hfin : K ≤ FC.rank := by nlinarith [hKK]
  exact le_trans hfin hC

/-! ## Part II : quantum codes

The Hilbert space of `n` qudits of local dimension `q` is `ℂ^(Fin n → Fin q)`, i.e. the space
of functions on the set `Str n q` of computational basis labels ("strings").
-/

/-- Computational basis labels ("strings") for `n` qudits of local dimension `q`. -/
abbrev Str (n q : ℕ) := Fin n → Fin q

/-- The Hilbert space of `n` qudits of local dimension `q`. -/
abbrev HSpace (n q : ℕ) := EuclideanSpace ℂ (Str n q)

/-- `glue S u w` is the string taking its coordinates on the sites `S` from `u`, and its
remaining coordinates from `w`. -/
def glue {n q : ℕ} (S : Finset (Fin n)) (u w : Str n q) : Str n q :=
  fun i => if i ∈ S then u i else w i

/-- `corr S x y u v` is the matrix element `⟪x, (|u⟩⟨v|_S ⊗ I) y⟫` of the elementary error
operator supported on the sites `S`, up to the overall normalisation `q ^ S.card`. -/
noncomputable def corr {n q : ℕ} (S : Finset (Fin n)) (x y : HSpace n q) (u v : Str n q) : ℂ :=
  ∑ w : Str n q, conj (x (glue S u w)) * y (glue S v w)

/-- The Knill–Laflamme error-detection condition for the sites `S`: for every error operator
supported on `S`, the operator acts on the code space as a multiple of the identity.  It is
enough to require this for the elementary errors `|u⟩⟨v|_S ⊗ I`, whose matrix elements are
computed by `corr`.  Equivalently, the erasure of the sites in `S` is correctable. -/
def Detects {n q : ℕ} (Code : Submodule ℂ (HSpace n q)) (S : Finset (Fin n)) : Prop :=
  ∃ sig : Str n q → Str n q → ℂ, ∀ x ∈ Code, ∀ y ∈ Code, ∀ u v : Str n q,
    corr S x y u v = inner ℂ x y * sig u v

/-- An `[[n, k, d]]_q` quantum error correcting code: a subspace of the `n`-qudit Hilbert space
of dimension `q ^ k` all of whose errors of weight `< d` are detected. -/
structure QECC (q n k d : ℕ) where
  /-- the code subspace -/
  space : Submodule ℂ (HSpace n q)
  /-- the code encodes `k` qudits -/
  dim : Module.finrank ℂ space = q ^ k
  /-- every error of weight at most `d - 1` is detected -/
  detects : ∀ S : Finset (Fin n), S.card < d → Detects space S

/-- Assembling a string out of its restrictions to `A`, to `B` and to the complement of
`A ∪ B`. -/
def asm {n q : ℕ} (A B : Finset (Fin n))
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q) : Str n q :=
  fun j => if h : j ∈ A then a ⟨j, h⟩ else if h' : j ∈ B then b ⟨j, h'⟩
    else c ⟨j, by simp [Finset.mem_compl, h, h']⟩

/-- Two disjoint sets of sites `A`, `B` and the complement of `A ∪ B` decompose a string. -/
def sitesEquiv {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    Str n q ≃
      (({i // i ∈ A} → Fin q) × ({i // i ∈ B} → Fin q) × ({i // i ∈ (A ∪ B)ᶜ} → Fin q)) where
  toFun s := (fun i => s i, fun i => s i, fun i => s i)
  invFun t := asm A B t.1 t.2.1 t.2.2
  left_inv s := by
    funext j
    simp only [asm]
    by_cases h : j ∈ A
    · simp [h]
    · by_cases h' : j ∈ B <;> simp [h, h']
  right_inv t := by
    obtain ⟨a, b, c⟩ := t
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i; simp [asm, i.2]
    · funext i
      have hnA : (i : Fin n) ∉ A := fun hc => (Finset.disjoint_left.mp hAB hc) i.2
      simp [asm, hnA, i.2]
    · funext i
      have hi := i.2
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hi
      simp [asm, hi.1, hi.2]

lemma glue_A {n q : ℕ} (A B : Finset (Fin n)) (u : Str n q)
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q) :
    glue A u (asm A B a b c) = asm A B (fun i => u i) b c := by
  funext j
  simp only [glue, asm]
  by_cases h : j ∈ A <;> simp [h]

lemma glue_B {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) (u : Str n q)
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q) :
    glue B u (asm A B a b c) = asm A B a (fun i => u i) c := by
  funext j
  simp only [glue, asm]
  by_cases h : j ∈ A
  · have hnB : j ∉ B := fun hc => (Finset.disjoint_left.mp hAB h) hc
    simp [h, hnB]
  · by_cases h' : j ∈ B <;> simp [h, h']

lemma corr_A_eq {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) (x y : HSpace n q)
    (u v : Str n q) :
    corr A x y u v = (q ^ A.card : ℂ) *
      ∑ b : {i // i ∈ B} → Fin q, ∑ c : {i // i ∈ (A ∪ B)ᶜ} → Fin q,
        conj (x (asm A B (fun i => u i) b c)) * y (asm A B (fun i => v i) b c) := by
  classical
  rw [corr, ← Equiv.sum_comp (sitesEquiv A B hAB).symm
    (fun w => conj (x (glue A u w)) * y (glue A v w))]
  show (∑ t : (_ × _ × _), conj (x (glue A u (asm A B t.1 t.2.1 t.2.2)))
      * y (glue A v (asm A B t.1 t.2.1 t.2.2))) = _
  simp only [glue_A, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp

lemma corr_B_eq {n q : ℕ} (A B : Finset (Fin n)) (hAB : Disjoint A B) (x y : HSpace n q)
    (u v : Str n q) :
    corr B x y u v = (q ^ B.card : ℂ) *
      ∑ a : {i // i ∈ A} → Fin q, ∑ c : {i // i ∈ (A ∪ B)ᶜ} → Fin q,
        conj (x (asm A B a (fun i => u i) c)) * y (asm A B a (fun i => v i) c) := by
  classical
  rw [corr, ← Equiv.sum_comp (sitesEquiv A B hAB).symm
    (fun w => conj (x (glue B u w)) * y (glue B v w))]
  show (∑ t : (_ × _ × _), conj (x (glue B u (asm A B t.1 t.2.1 t.2.2)))
      * y (glue B v (asm A B t.1 t.2.1 t.2.2))) = _
  simp only [glue_B A B hAB, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  simp

/-- If the erasures of two disjoint sets of sites `A` and `B` are both correctable, then the
dimension of the code is at most `q ^ |(A ∪ B)ᶜ|`. -/
theorem code_dim_le {q n k d : ℕ} (hq : 0 < q) (Q : QECC q n k d)
    (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : Detects Q.space A) (hB : Detects Q.space B) :
    q ^ k ≤ q ^ (A ∪ B)ᶜ.card := by
  classical
  obtain ⟨sigA, hsigA⟩ := hA
  obtain ⟨sigB, hsigB⟩ := hB
  set bas := (stdOrthonormalBasis ℂ Q.space).reindex (finCongr Q.dim) with hbas
  set x : Fin (q ^ k) → HSpace n q := fun i => ((bas i : Q.space) : HSpace n q) with hx
  have hxmem : ∀ i, x i ∈ Q.space := fun i => (bas i).2
  have hxinner : ∀ i j, inner ℂ (x i) (x j) = if i = j then (1:ℂ) else 0 := by
    intro i j
    rw [hx, ← Submodule.coe_inner]
    exact orthonormal_iff_ite.mp bas.orthonormal i j
  set a0 : {i // i ∈ A} → Fin q := fun _ => ⟨0, hq⟩ with ha0
  set b0 : {i // i ∈ B} → Fin q := fun _ => ⟨0, hq⟩ with hb0
  set c0 : {i // i ∈ (A ∪ B)ᶜ} → Fin q := fun _ => ⟨0, hq⟩ with hc0
  set T : Fin (q ^ k) → ({i // i ∈ A} → Fin q) → ({i // i ∈ B} → Fin q) →
      ({i // i ∈ (A ∪ B)ᶜ} → Fin q) → ℂ := fun i a b c => x i (asm A B a b c) with hT
  have hrA : ∀ (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
      (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q), (fun (i : {i // i ∈ A}) => (asm A B a b c) i) = a := by
    intro a b c; funext i; simp [asm, i.2]
  have hrB : ∀ (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
      (c : {i // i ∈ (A ∪ B)ᶜ} → Fin q), (fun (i : {i // i ∈ B}) => (asm A B a b c) i) = b := by
    intro a b c; funext i
    have hnA : (i : Fin n) ∉ A := fun hcc => (Finset.disjoint_left.mp hAB hcc) i.2
    simp [asm, hnA, i.2]
  have hqA : ((q : ℂ) ^ A.card) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  have hqB : ((q : ℂ) ^ B.card) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hq.ne')
  -- the reduced correlation matrices
  set sA : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ := Matrix.of fun a a' =>
    conj (sigA (asm A B a b0 c0) (asm A B a' b0 c0)) / (q : ℂ) ^ A.card with hsA
  set sB : Matrix ({i // i ∈ B} → Fin q) ({i // i ∈ B} → Fin q) ℂ := Matrix.of fun b b' =>
    conj (sigB (asm A B a0 b c0) (asm A B a0 b' c0)) / (q : ℂ) ^ B.card with hsB
  have hAcond : ∀ i j a a', (∑ b, ∑ c, T i a b c * conj (T j a' b c))
      = if i = j then sA a a' else 0 := by
    intro i j a a'
    have h := hsigA (x i) (hxmem i) (x j) (hxmem j) (asm A B a b0 c0) (asm A B a' b0 c0)
    rw [corr_A_eq A B hAB, hrA, hrA, hxinner] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_mul, map_sum, Complex.conj_conj, map_pow, Complex.conj_natCast,
      apply_ite (starRingEnd ℂ), map_one, map_zero] at h2
    have h3 : ((q : ℂ) ^ A.card) * (∑ b, ∑ c, T i a b c * conj (T j a' b c))
        = (if i = j then (1:ℂ) else 0) * conj (sigA (asm A B a b0 c0) (asm A B a' b0 c0)) := by
      rw [← h2]
    have h4 := congrArg (fun z => z / (q : ℂ) ^ A.card) h3
    simp only at h4
    rw [mul_comm, mul_div_assoc, div_self hqA, mul_one] at h4
    rw [h4, hsA]
    by_cases hij : i = j <;> simp [hij]
  have hBcond : ∀ i j b b', (∑ a, ∑ c, T i a b c * conj (T j a b' c))
      = if i = j then sB b b' else 0 := by
    intro i j b b'
    have h := hsigB (x i) (hxmem i) (x j) (hxmem j) (asm A B a0 b c0) (asm A B a0 b' c0)
    rw [corr_B_eq A B hAB, hrB, hrB, hxinner] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_mul, map_sum, Complex.conj_conj, map_pow, Complex.conj_natCast,
      apply_ite (starRingEnd ℂ), map_one, map_zero] at h2
    have h3 : ((q : ℂ) ^ B.card) * (∑ a, ∑ c, T i a b c * conj (T j a b' c))
        = (if i = j then (1:ℂ) else 0) * conj (sigB (asm A B a0 b c0) (asm A B a0 b' c0)) := by
      rw [← h2]
    have h4 := congrArg (fun z => z / (q : ℂ) ^ B.card) h3
    simp only at h4
    rw [mul_comm, mul_div_assoc, div_self hqB, mul_one] at h4
    rw [h4, hsB]
    by_cases hij : i = j <;> simp [hij]
  -- the code is nonzero
  have hknonempty : Nonempty (Fin (q ^ k)) := ⟨⟨0, pow_pos hq k⟩⟩
  obtain ⟨i0⟩ := hknonempty
  have hne : ∃ i a b c, T i a b c ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h1 : inner ℂ (x i0) (x i0) = (1:ℂ) := by rw [hxinner]; simp
    rw [PiLp.inner_apply] at h1
    have hz : ∀ s : Str n q, (inner ℂ ((x i0) s) ((x i0) s) : ℂ) = 0 := by
      intro s
      have hs : s = asm A B ((sitesEquiv A B hAB) s).1 ((sitesEquiv A B hAB) s).2.1
          ((sitesEquiv A B hAB) s).2.2 := ((sitesEquiv A B hAB).left_inv s).symm
      have hzero := hall i0 ((sitesEquiv A B hAB) s).1 ((sitesEquiv A B hAB) s).2.1
        ((sitesEquiv A B hAB) s).2.2
      rw [hT] at hzero
      simp only at hzero
      rw [← hs] at hzero
      simp [hzero]
    rw [Finset.sum_congr rfl (fun s (_ : s ∈ Finset.univ) => hz s)] at h1
    simp at h1
  -- apply the linear algebra core
  have hcard := card_le_of_KL T sA sB hAcond hBcond hne
  have hcardC : Fintype.card ({i // i ∈ (A ∪ B)ᶜ} → Fin q) = q ^ (A ∪ B)ᶜ.card := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
  rw [Fintype.card_fin, hcardC] at hcard
  exact hcard


lemma glue_empty {n q : ℕ} (u w : Str n q) : glue ∅ u w = w := by
  funext j; simp [glue]

/-- The empty set of sites is always correctable. -/
lemma detects_empty {n q : ℕ} (Code : Submodule ℂ (HSpace n q)) : Detects Code ∅ := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro x _ y _ u v
  simp only [corr, glue_empty, mul_one]
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun w _ => by simp [RCLike.inner_apply, mul_comm]

/-- A code on `n` qudits encodes at most `n` qudits. -/
theorem code_encodes_at_most_n {q n k d : ℕ} (hq : 2 ≤ q) (Q : QECC q n k d) : k ≤ n := by
  have h := code_dim_le (by omega) Q ∅ ∅ (by simp) (detects_empty _) (detects_empty _)
  simp only [Finset.union_self, Finset.compl_empty, Finset.card_univ, Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right hq).mp h

/-- **The quantum Singleton bound.**

An `[[n, k, d]]_q` quantum code with `q ≥ 2` and `k ≥ 1` satisfies `n - k ≥ 2 (d - 1)`. -/
theorem quantum_singleton {q n k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (Q : QECC q n k d) :
    2 * ((d : ℤ) - 1) ≤ (n : ℤ) - k := by
  classical
  rcases le_or_gt d 1 with hd | hd
  · have h1 : k ≤ n := code_encodes_at_most_n hq Q
    have h2 : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast h1
    have h3 : (d : ℤ) ≤ 1 := by exact_mod_cast hd
    omega
  · set a := min (d - 1) n with ha
    have haun : a ≤ (Finset.univ : Finset (Fin n)).card := by
      simp only [Finset.card_univ, Fintype.card_fin, ha]
      omega
    obtain ⟨A, -, hAcard⟩ := Finset.exists_subset_card_eq haun
    set b := min (d - 1) (n - a) with hb
    have hbun : b ≤ (Aᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, hAcard]
      simp only [Fintype.card_fin, hb]
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hbun
    have hAB : Disjoint A B :=
      Finset.disjoint_left.mpr fun z hzA hzB => (Finset.mem_compl.mp (hBsub hzB)) hzA
    have hdetA : Detects Q.space A := Q.detects A (by rw [hAcard]; omega)
    have hdetB : Detects Q.space B := Q.detects B (by rw [hBcard]; omega)
    have hle := code_dim_le (by omega) Q A B hAB hdetA hdetB
    have hcompl : (A ∪ B)ᶜ.card = n - (a + b) := by
      rw [Finset.card_compl, Finset.card_union_of_disjoint hAB, hAcard, hBcard,
        Fintype.card_fin]
    rw [hcompl] at hle
    have hkle : k ≤ n - (a + b) := (Nat.pow_le_pow_iff_right hq).mp hle
    omega


/-! ## Part III : the definitions are not vacuous -/

/-- The whole `n`-qudit space is a code encoding `n` qudits, of distance `1`.  For this code the
quantum Singleton bound is tight. -/
def trivialCode (q n : ℕ) : QECC q n n 1 where
  space := ⊤
  dim := by rw [finrank_top, finrank_euclideanSpace]; simp
  detects S hS := by
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst hS0
    exact detects_empty _

/-- A one-dimensional code detects *every* error, hence has arbitrarily large distance.  This is
why the assumption `1 ≤ k` in `QI.quantum_singleton` cannot be dropped. -/
def oneDimCode (q n d : ℕ) (s0 : Str n q) : QECC q n 0 d where
  space := Submodule.span ℂ {(EuclideanSpace.single s0 (1 : ℂ) : HSpace n q)}
  dim := by
    have hne : (EuclideanSpace.single s0 (1 : ℂ) : HSpace n q) ≠ 0 := by
      intro h
      have := congrFun (congrArg WithLp.ofLp h) s0
      simp at this
    rw [finrank_span_singleton hne, pow_zero]
  detects S _ := by
    refine ⟨fun u v => corr S (EuclideanSpace.single s0 (1 : ℂ)) (EuclideanSpace.single s0 1) u v,
      ?_⟩
    intro x hx y hy u v
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hcorr : ∀ z z' : HSpace n q, corr S (a • z) (b • z') u v
        = conj a * b * corr S z z' u v := by
      intro z z'
      simp only [corr, PiLp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => by ring
    have hone : inner ℂ (EuclideanSpace.single s0 (1 : ℂ) : HSpace n q)
        (EuclideanSpace.single s0 (1 : ℂ)) = 1 := by simp
    rw [hcorr, inner_smul_left, inner_smul_right, hone]
    ring


end QI

#print axioms QI.quantum_singleton

