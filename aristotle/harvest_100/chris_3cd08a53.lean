/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 does not allow a `/-! ... -/` module docstring to precede `import`, so the
-- required header comment is reproduced verbatim immediately after the import below.)

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
## Overview

We prove the **quantum Singleton bound** (Knill–Laflamme–Rains): an `[[n, k, d]]_q`
quantum error-correcting code satisfies `k + 2 * (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The proof given here is a purely linear-algebraic ("Rényi-0"/rank) version of the usual
entropic no-cloning argument.  Writing the code space as a tensor `T` with a reference
index `R` (of size `q ^ k`) and three groups of sites `A`, `B`, `C`, the Knill–Laflamme
conditions for the two disjoint site sets `A` and `B` say that the Gram matrices of the
code vectors, partially traced onto `A` (resp. `B`), are proportional to the identity in
the reference index.  Passing to ranks:

* `rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{RB} = |R| · rank ρ_B`  (Kronecker structure);
* `rank ρ_{BC} ≤ rank ρ_B · rank ρ_C`  (rank submultiplicativity across a tensor cut);
* `rank ρ_{RA} = rank ρ_{BC}` and `rank ρ_{RB} = rank ρ_{AC}` (purity).

Multiplying the two resulting inequalities `|R| · a ≤ b · c` and `|R| · b ≤ a · c` and
cancelling `a·b > 0` gives `|R| ≤ c ≤ q ^ |C|`, which is the bound.

No Mathlib lemma proves this statement (Mathlib contains no quantum coding theory), so the
required linear algebra — in particular a rank factorization of a matrix with one-sided
inverses, the rank of `1 ⊗ₖ S`, and submultiplicativity of the rank across a tensor cut —
is developed here from scratch.
-/

open Matrix Module Kronecker
open scoped ComplexOrder

namespace QI

/-! ### General linear algebra: rank tools -/

/-- **Rank factorization.**  Any matrix `N` factors as `N = F * G` where `F` has `rank N`
columns and a left inverse, and `G` has `rank N` rows and a right inverse. -/
theorem exists_rank_factorization {K m n : Type} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (N : Matrix m n K) :
    ∃ (r : ℕ) (F : Matrix m (Fin r) K) (G : Matrix (Fin r) n K)
      (L : Matrix (Fin r) m K) (M : Matrix n (Fin r) K),
      r = N.rank ∧ N = F * G ∧ L * F = 1 ∧ G * M = 1 := by
  classical
  set f := N.mulVecLin with hf
  have hr : Module.finrank K (LinearMap.range f) = N.rank := rfl
  let bW : Basis (Fin N.rank) K (LinearMap.range f) := Module.finBasisOfFinrankEq K _ hr
  let phi : (Fin N.rank → K) →ₗ[K] (m → K) :=
    (LinearMap.range f).subtype ∘ₗ (bW.equivFun.symm : (Fin N.rank → K) →ₗ[K] (LinearMap.range f))
  let psi : (n → K) →ₗ[K] (Fin N.rank → K) :=
    (bW.equivFun : (LinearMap.range f) →ₗ[K] (Fin N.rank → K)) ∘ₗ f.rangeRestrict
  have hcomp : phi ∘ₗ psi = f := by ext v i; simp [phi, psi]
  have hphiinj : LinearMap.ker phi = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (Submodule.injective_subtype _).comp bW.equivFun.symm.injective
  have hpsisurj : LinearMap.range psi = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact bW.equivFun.surjective.comp f.surjective_rangeRestrict
  obtain ⟨l, hl⟩ := LinearMap.exists_leftInverse_of_injective phi hphiinj
  obtain ⟨rr, hrr⟩ := LinearMap.exists_rightInverse_of_surjective psi hpsisurj
  refine ⟨N.rank, LinearMap.toMatrix' phi, LinearMap.toMatrix' psi, LinearMap.toMatrix' l,
    LinearMap.toMatrix' rr, rfl, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hcomp, hf]
    exact (LinearEquiv.symm_apply_eq LinearMap.toMatrix').mp rfl
  · rw [← LinearMap.toMatrix'_comp, hl]; simp
  · rw [← LinearMap.toMatrix'_comp, hrr]; simp

/-- The rank of `1 ⊗ₖ S` is at least `|R| * rank S` (in fact equal, but only `≥` is
needed below). -/
theorem card_mul_rank_le_rank_one_kronecker {K R A : Type} [Field K] [Fintype R] [Fintype A]
    [DecidableEq R] [DecidableEq A] (S : Matrix A A K) :
    Fintype.card R * S.rank ≤ ((1 : Matrix R R K) ⊗ₖ S).rank := by
  obtain ⟨r, F, G, L, M, hr, hFG, hLF, hGM⟩ := exists_rank_factorization S
  subst hFG
  have key : ((1 : Matrix R R K) ⊗ₖ L) *
      (((1 : Matrix R R K) ⊗ₖ (F * G)) * ((1 : Matrix R R K) ⊗ₖ M)) = 1 := by
    rw [show ((1 : Matrix R R K) ⊗ₖ (F * G))
        = ((1 : Matrix R R K) ⊗ₖ F) * ((1 : Matrix R R K) ⊗ₖ G) by
      rw [← Matrix.mul_kronecker_mul]; simp]
    rw [Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hGM, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul]
    simp [hLF]
  calc Fintype.card R * (F * G).rank = (1 : Matrix (R × Fin r) (R × Fin r) K).rank := by
        rw [Matrix.rank_one]; simp [← hr]
    _ = _ := by rw [key]
    _ ≤ (((1 : Matrix R R K) ⊗ₖ (F * G)) * ((1 : Matrix R R K) ⊗ₖ M)).rank :=
        Matrix.rank_mul_le_right _ _
    _ ≤ ((1 : Matrix R R K) ⊗ₖ (F * G)).rank := Matrix.rank_mul_le_left _ _

/-- **Submultiplicativity of the rank across a tensor cut.**  For a three-index tensor
`T : D → B → C → K`, the rank of the flattening `(B × C) × D` is at most the product of
the ranks of the flattenings `B × (D × C)` and `C × (D × B)`. -/
theorem rank_le_mul_rank {K D B C : Type} [Field K] [Fintype D] [Fintype B] [Fintype C]
    [DecidableEq D] [DecidableEq B] [DecidableEq C] (T : D → B → C → K) :
    (Matrix.of fun (p : B × C) (d : D) => T d p.1 p.2).rank
      ≤ (Matrix.of fun (b : B) (p : D × C) => T p.1 b p.2).rank
        * (Matrix.of fun (c : C) (p : D × B) => T p.1 p.2 c).rank := by
  classical
  set NB : Matrix B (D × C) K := Matrix.of fun (b : B) (p : D × C) => T p.1 b p.2 with hNB
  set NC : Matrix C (D × B) K := Matrix.of fun (c : C) (p : D × B) => T p.1 p.2 c with hNC
  set MBC : Matrix (B × C) D K := Matrix.of fun (p : B × C) (d : D) => T d p.1 p.2 with hMBC
  obtain ⟨rB, F, G, L, M, hrB, hFG, hLF, -⟩ := exists_rank_factorization NB
  obtain ⟨rC, H, J, M', -, hrC, hHJ, hMH, -⟩ := exists_rank_factorization NC
  have hP : (F * L) * NB = NB := by
    rw [hFG, Matrix.mul_assoc, ← Matrix.mul_assoc L F G, hLF, Matrix.one_mul]
  have hQ : (H * M') * NC = NC := by
    rw [hHJ, Matrix.mul_assoc, ← Matrix.mul_assoc M' H J, hMH, Matrix.one_mul]
  have keyB : ∀ (d : D) (b : B) (c : C), ∑ b', (F * L) b b' * T d b' c = T d b c := by
    intro d b c
    have := congrFun (congrFun hP b) (d, c)
    simpa [Matrix.mul_apply, hNB] using this
  have keyC : ∀ (d : D) (b : B) (c : C), ∑ c', (H * M') c c' * T d b c' = T d b c := by
    intro d b c
    have := congrFun (congrFun hQ c) (d, b)
    simpa [Matrix.mul_apply, hNC] using this
  have main : ((F * L) ⊗ₖ (H * M')) * MBC = MBC := by
    ext p d
    obtain ⟨b, c⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h : ∀ b', ∑ c', ((F * L) ⊗ₖ (H * M')) (b, c) (b', c') * MBC (b', c') d
        = (F * L) b b' * T d b' c := by
      intro b'
      simp only [Matrix.kroneckerMap_apply, hMBC, Matrix.of_apply]
      rw [← keyC d b' c, Finset.mul_sum]
      congr 1
      ext c'
      ring
    rw [Finset.sum_congr rfl (fun b' _ => h b')]
    exact keyB d b c
  have hfact : ((F * L) ⊗ₖ (H * M')) = (F ⊗ₖ H) * (L ⊗ₖ M') := by
    rw [← Matrix.mul_kronecker_mul]
  calc MBC.rank = ((F ⊗ₖ H) * ((L ⊗ₖ M') * MBC)).rank := by
        rw [← Matrix.mul_assoc, ← hfact, main]
    _ ≤ (F ⊗ₖ H).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin rB × Fin rC) := Matrix.rank_le_card_width _
    _ = NB.rank * NC.rank := by simp [hrB, hrC]

/-- A nonzero matrix has positive rank. -/
lemma rank_pos_of_ne_zero {K m n : Type} [Field K] [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n K) (h : M ≠ 0) : 1 ≤ M.rank := by
  rcases Nat.eq_zero_or_pos M.rank with h0 | h1
  · exfalso
    apply h
    have hb : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    rw [LinearMap.range_eq_bot] at hb
    have h2 : ∀ v, M *ᵥ v = 0 :=
      fun v => congrFun (congrArg (fun (f : (n → K) →ₗ[K] (m → K)) => ⇑f) hb) v
    ext i j
    have := congrFun (h2 (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  · exact h1

/-! ### The abstract no-cloning bound -/

section Abstract

variable {R A B C : Type} [Fintype R] [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq C]

local notation "conj" => (starRingEnd ℂ)

/-- **The rank form of the no-cloning bound.**

If a family of tensors `T i : A → B → C → ℂ` (`i` ranging over a reference index set `R`)
is *decoupled* both from the `A` factor and from the `B` factor — i.e. the partial Gram
matrices over `B × C` and over `A × C` are `δᵢⱼ` times fixed matrices `SA`, `SB` — and
some `T i₀` is nonzero, then `|R| ≤ |C|`.

This is the Knill–Laflamme condition for the two disjoint erasure sets `A` and `B`, and the
conclusion is the quantum Singleton bound. -/
theorem card_le_card_of_decoupled
    (T : R → A → B → C → ℂ) (SA : Matrix A A ℂ) (SB : Matrix B B ℂ)
    (hA : ∀ i j a a', ∑ b, ∑ c, T i a b c * conj (T j a' b c) = if i = j then SA a a' else 0)
    (hB : ∀ i j b b', ∑ a, ∑ c, T i a b c * conj (T j a b' c) = if i = j then SB b b' else 0)
    (i₀ : R) (hT : T i₀ ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  set MA : Matrix (B × C) (R × A) ℂ := Matrix.of fun p d => T d.1 d.2 p.1 p.2 with hMA
  set MB : Matrix (A × C) (R × B) ℂ := Matrix.of fun p d => T d.1 p.1 d.2 p.2 with hMB
  set NB1 : Matrix B ((R × A) × C) ℂ := Matrix.of fun b p => T p.1.1 p.1.2 b p.2 with hNB1
  set NC1 : Matrix C ((R × A) × B) ℂ := Matrix.of fun c p => T p.1.1 p.1.2 p.2 c with hNC1
  set NA2 : Matrix A ((R × B) × C) ℂ := Matrix.of fun a p => T p.1.1 a p.1.2 p.2 with hNA2
  set NC2 : Matrix C ((R × B) × A) ℂ := Matrix.of fun c p => T p.1.1 p.2 p.1.2 c with hNC2
  -- lower bounds coming from the Kronecker structure of the Gram matrices
  have lowA : Fintype.card R * SA.rank ≤ MA.rank := by
    have h1 : MAᴴ * MA = (1 : Matrix R R ℂ) ⊗ₖ SAᵀ := by
      ext x y
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hMA, Matrix.of_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.transpose_apply, RCLike.star_def]
      rw [show (∑ b, ∑ c, conj (T x.1 x.2 b c) * T y.1 y.2 b c)
          = ∑ b, ∑ c, T y.1 y.2 b c * conj (T x.1 x.2 b c) from
        Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun c _ => mul_comm _ _))]
      rw [hA y.1 x.1 y.2 x.2]
      by_cases h : x.1 = y.1
      · simp [h]
      · simp [h, Ne.symm h]
    calc Fintype.card R * SA.rank = Fintype.card R * SAᵀ.rank := by rw [Matrix.rank_transpose]
      _ ≤ ((1 : Matrix R R ℂ) ⊗ₖ SAᵀ).rank := card_mul_rank_le_rank_one_kronecker _
      _ = (MAᴴ * MA).rank := by rw [h1]
      _ = MA.rank := Matrix.rank_conjTranspose_mul_self _
  have lowB : Fintype.card R * SB.rank ≤ MB.rank := by
    have h1 : MBᴴ * MB = (1 : Matrix R R ℂ) ⊗ₖ SBᵀ := by
      ext x y
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hMB, Matrix.of_apply, Matrix.kroneckerMap_apply,
        Matrix.one_apply, Matrix.transpose_apply, RCLike.star_def]
      rw [show (∑ a, ∑ c, conj (T x.1 a x.2 c) * T y.1 a y.2 c)
          = ∑ a, ∑ c, T y.1 a y.2 c * conj (T x.1 a x.2 c) from
        Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => mul_comm _ _))]
      rw [hB y.1 x.1 y.2 x.2]
      by_cases h : x.1 = y.1
      · simp [h]
      · simp [h, Ne.symm h]
    calc Fintype.card R * SB.rank = Fintype.card R * SBᵀ.rank := by rw [Matrix.rank_transpose]
      _ ≤ ((1 : Matrix R R ℂ) ⊗ₖ SBᵀ).rank := card_mul_rank_le_rank_one_kronecker _
      _ = (MBᴴ * MB).rank := by rw [h1]
      _ = MB.rank := Matrix.rank_conjTranspose_mul_self _
  -- upper bounds on the single-party ranks
  have upB : NB1.rank ≤ SB.rank := by
    have h1 : NB1 * NB1ᴴ = (Fintype.card R : ℂ) • SB := by
      ext b b'
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hNB1, Matrix.of_apply, RCLike.star_def,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hB i i b b')]
      simp [Finset.sum_const, mul_comm]
    calc NB1.rank = (NB1 * NB1ᴴ).rank := (Matrix.rank_self_mul_conjTranspose _).symm
      _ = ((Fintype.card R : ℂ) • SB).rank := by rw [h1]
      _ = (((Fintype.card R : ℂ) • (1 : Matrix B B ℂ)) * SB).rank := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ ≤ SB.rank := Matrix.rank_mul_le_right _ _
  have upA : NA2.rank ≤ SA.rank := by
    have h1 : NA2 * NA2ᴴ = (Fintype.card R : ℂ) • SA := by
      ext a a'
      rw [Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp only [Matrix.conjTranspose_apply, hNA2, Matrix.of_apply, RCLike.star_def,
        Matrix.smul_apply, smul_eq_mul]
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hA i i a a')]
      simp [Finset.sum_const, mul_comm]
    calc NA2.rank = (NA2 * NA2ᴴ).rank := (Matrix.rank_self_mul_conjTranspose _).symm
      _ = ((Fintype.card R : ℂ) • SA).rank := by rw [h1]
      _ = (((Fintype.card R : ℂ) • (1 : Matrix A A ℂ)) * SA).rank := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ ≤ SA.rank := Matrix.rank_mul_le_right _ _
  -- the two `C`-flattenings have the same rank
  have hCC : NC2.rank = NC1.rank := by
    let e : (R × B) × A ≃ (R × A) × B :=
      ⟨fun p => ((p.1.1, p.2), p.1.2), fun p => ((p.1.1, p.2), p.1.2),
        by rintro ⟨⟨i, b⟩, a⟩; rfl, by rintro ⟨⟨i, a⟩, b⟩; rfl⟩
    have h : NC2 = NC1.submatrix (Equiv.refl C) e := by ext c p; rfl
    rw [h, Matrix.rank_submatrix]
  -- submultiplicativity across the two cuts
  have subA : MA.rank ≤ NB1.rank * NC1.rank :=
    rank_le_mul_rank (fun (d : R × A) b c => T d.1 d.2 b c)
  have subB : MB.rank ≤ NA2.rank * NC2.rank :=
    rank_le_mul_rank (fun (d : R × B) a c => T d.1 a d.2 c)
  -- positivity
  obtain ⟨a₀, b₀, c₀, hne⟩ : ∃ a b c, T i₀ a b c ≠ 0 := by
    by_contra h
    push_neg at h
    exact hT (funext fun a => funext fun b => funext fun c => h a b c)
  have hposA : 1 ≤ SA.rank := le_trans (rank_pos_of_ne_zero NA2 (by
    intro h
    exact hne (by simpa [hNA2] using congrFun (congrFun h a₀) ((i₀, b₀), c₀)))) upA
  have hposB : 1 ≤ SB.rank := le_trans (rank_pos_of_ne_zero NB1 (by
    intro h
    exact hne (by simpa [hNB1] using congrFun (congrFun h b₀) ((i₀, a₀), c₀)))) upB
  -- combine
  have e1 : Fintype.card R * SA.rank ≤ SB.rank * NC1.rank :=
    lowA.trans (subA.trans (Nat.mul_le_mul_right _ upB))
  have e2 : Fintype.card R * SB.rank ≤ SA.rank * NC1.rank := by
    refine lowB.trans (subB.trans ?_)
    rw [hCC]
    exact Nat.mul_le_mul_right _ upA
  have key : Fintype.card R * Fintype.card R * (SA.rank * SB.rank)
      ≤ (SA.rank * SB.rank) * (NC1.rank * NC1.rank) := by
    have := Nat.mul_le_mul e1 e2
    nlinarith [this]
  have hab : 0 < SA.rank * SB.rank := Nat.mul_pos hposA hposB
  have hsq : Fintype.card R * Fintype.card R ≤ NC1.rank * NC1.rank := by
    have h2 : (SA.rank * SB.rank) * (Fintype.card R * Fintype.card R)
        ≤ (SA.rank * SB.rank) * (NC1.rank * NC1.rank) := by linarith [key]
    exact Nat.le_of_mul_le_mul_left h2 hab
  exact (Nat.mul_self_le_mul_self_iff.mp hsq).trans (Matrix.rank_le_card_height _)

end Abstract


/-! ### Quantum error-correcting codes -/

/-- The computational-basis index set of `n` qudits of local dimension `q`. -/
abbrev Sites (n q : ℕ) : Type := Fin n → Fin q

/-- `embed A E` is the operator acting as `E` on the qudits located at the sites in `A`,
and as the identity on all the other sites. -/
def embed {n q : ℕ} (A : Finset (Fin n))
    (E : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ) :
    Matrix (Sites n q) (Sites n q) ℂ :=
  Matrix.of fun x y => if ∀ i, i ∉ A → x i = y i then E (fun i => x i.1) (fun i => y i.1) else 0

/-- An `[[n, k, d]]_q` quantum error-correcting code: an orthonormal family of `q ^ k`
states of `n` qudits of local dimension `q` (an orthonormal basis of the code space)
satisfying the Knill–Laflamme error-correction conditions for every set of at most
`d - 1` sites, i.e. the code corrects the erasure of any `d - 1` qudits, which is the
standard characterisation of having minimum distance at least `d`. -/
structure Code (n k d q : ℕ) where
  /-- An orthonormal basis of the code space. -/
  state : Fin (q ^ k) → Sites n q → ℂ
  /-- The basis is orthonormal. -/
  orthonormal : ∀ i j, ∑ x, (starRingEnd ℂ) (state i x) * state j x = if i = j then 1 else 0
  /-- Knill–Laflamme conditions: for every operator `E` supported on at most `d - 1`
  sites, `P E P = c(E) P` on the code space. -/
  knill_laflamme : ∀ (S : Finset (Fin n)), S.card ≤ d - 1 →
      ∀ E, ∃ c : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (state i x) * embed S E x y * state j y = if i = j then c else 0

section Split

variable {n q : ℕ} (A B Cs : Finset (Fin n))
  (hmem : ∀ i : Fin n, (i ∈ A ∧ i ∉ B ∧ i ∉ Cs) ∨ (i ∉ A ∧ i ∈ B ∧ i ∉ Cs)
      ∨ (i ∉ A ∧ i ∉ B ∧ i ∈ Cs))
  (hcard : A.card + B.card + Cs.card = n)

/-- The identification of a configuration of `n` qudits with the triple of its
restrictions to a partition of the sites into three groups `A`, `B`, `Cs`. -/
noncomputable def splitEquiv :
    Sites n q ≃ (({i // i ∈ A} → Fin q) × ({i // i ∈ B} → Fin q) × ({i // i ∈ Cs} → Fin q)) := by
  classical
  refine Equiv.ofBijective (fun x => (fun i => x i.1, fun i => x i.1, fun i => x i.1)) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro x y hxy
    funext i
    rcases hmem i with ⟨hi, -, -⟩ | ⟨-, hi, -⟩ | ⟨-, -, hi⟩
    · exact congrFun (congrArg Prod.fst hxy) ⟨i, hi⟩
    · exact congrFun (congrArg (fun p => p.2.1) hxy) ⟨i, hi⟩
    · exact congrFun (congrArg (fun p => p.2.2) hxy) ⟨i, hi⟩
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    rw [← pow_add, ← pow_add]
    congr 1
    omega

lemma splitEquiv_apply (x : Sites n q) :
    splitEquiv (q := q) A B Cs hmem hcard x
      = (fun i => x i.1, fun i => x i.1, fun i => x i.1) := rfl

lemma splitEquiv_symm_A (p) (i : Fin n) (hi : i ∈ A) :
    (splitEquiv (q := q) A B Cs hmem hcard).symm p i = p.1 ⟨i, hi⟩ :=
  congrFun (congrArg Prod.fst
    ((splitEquiv (q := q) A B Cs hmem hcard).apply_symm_apply p)) ⟨i, hi⟩

lemma splitEquiv_symm_B (p) (i : Fin n) (hi : i ∈ B) :
    (splitEquiv (q := q) A B Cs hmem hcard).symm p i = p.2.1 ⟨i, hi⟩ :=
  congrFun (congrArg (fun z => Prod.fst (Prod.snd z))
    ((splitEquiv (q := q) A B Cs hmem hcard).apply_symm_apply p)) ⟨i, hi⟩

lemma splitEquiv_symm_C (p) (i : Fin n) (hi : i ∈ Cs) :
    (splitEquiv (q := q) A B Cs hmem hcard).symm p i = p.2.2 ⟨i, hi⟩ :=
  congrFun (congrArg (fun z => Prod.snd (Prod.snd z))
    ((splitEquiv (q := q) A B Cs hmem hcard).apply_symm_apply p)) ⟨i, hi⟩

/-- Swapping the roles of the first two groups of sites. -/
lemma splitEquiv_swap
    (hmem' : ∀ i : Fin n, (i ∈ B ∧ i ∉ A ∧ i ∉ Cs) ∨ (i ∉ B ∧ i ∈ A ∧ i ∉ Cs)
      ∨ (i ∉ B ∧ i ∉ A ∧ i ∈ Cs))
    (hcard' : B.card + A.card + Cs.card = n)
    (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q) (c : {i // i ∈ Cs} → Fin q) :
    (splitEquiv B A Cs hmem' hcard').symm (b, a, c)
      = (splitEquiv A B Cs hmem hcard).symm (a, b, c) := by
  apply (splitEquiv (q := q) B A Cs hmem' hcard').injective
  rw [Equiv.apply_symm_apply, splitEquiv_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i; exact (splitEquiv_symm_B A B Cs hmem hcard (a, b, c) i.1 i.2).symm
  · funext i; exact (splitEquiv_symm_A A B Cs hmem hcard (a, b, c) i.1 i.2).symm
  · funext i; exact (splitEquiv_symm_C A B Cs hmem hcard (a, b, c) i.1 i.2).symm

/-- The embedded operator, written in the split coordinates. -/
lemma embed_split (E : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ)
    (a a' : {i // i ∈ A} → Fin q) (b b' : {i // i ∈ B} → Fin q)
    (c c' : {i // i ∈ Cs} → Fin q) :
    embed A E ((splitEquiv A B Cs hmem hcard).symm (a, b, c))
        ((splitEquiv A B Cs hmem hcard).symm (a', b', c'))
      = if b = b' ∧ c = c' then E a a' else 0 := by
  classical
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  have hA1 : (fun (i : {i // i ∈ A}) => (e.symm (a, b, c)) i.1) = a := by
    funext i; exact splitEquiv_symm_A A B Cs hmem hcard _ i.1 i.2
  have hA2 : (fun (i : {i // i ∈ A}) => (e.symm (a', b', c')) i.1) = a' := by
    funext i; exact splitEquiv_symm_A A B Cs hmem hcard _ i.1 i.2
  have hcond : (∀ i, i ∉ A → (e.symm (a, b, c)) i = (e.symm (a', b', c')) i)
      ↔ (b = b' ∧ c = c') := by
    constructor
    · intro h
      constructor
      · funext i
        have hiA : i.1 ∉ A := by
          rcases hmem i.1 with ⟨-, hb, -⟩ | ⟨ha, -, -⟩ | ⟨-, hb, -⟩
          · exact absurd i.2 hb
          · exact ha
          · exact absurd i.2 hb
        have h2 := h i.1 hiA
        rwa [splitEquiv_symm_B A B Cs hmem hcard _ i.1 i.2,
          splitEquiv_symm_B A B Cs hmem hcard _ i.1 i.2] at h2
      · funext i
        have hiA : i.1 ∉ A := by
          rcases hmem i.1 with ⟨-, -, hc⟩ | ⟨-, -, hc⟩ | ⟨ha, -, -⟩
          · exact absurd i.2 hc
          · exact absurd i.2 hc
          · exact ha
        have h2 := h i.1 hiA
        rwa [splitEquiv_symm_C A B Cs hmem hcard _ i.1 i.2,
          splitEquiv_symm_C A B Cs hmem hcard _ i.1 i.2] at h2
    · rintro ⟨rfl, rfl⟩ i hi
      rcases hmem i with ⟨hia, -, -⟩ | ⟨-, hib, -⟩ | ⟨-, -, hic⟩
      · exact absurd hia hi
      · rw [splitEquiv_symm_B A B Cs hmem hcard _ i hib,
          splitEquiv_symm_B A B Cs hmem hcard _ i hib]
      · rw [splitEquiv_symm_C A B Cs hmem hcard _ i hic,
          splitEquiv_symm_C A B Cs hmem hcard _ i hic]
  simp only [embed, Matrix.of_apply, hA1, hA2]
  by_cases h : b = b' ∧ c = c'
  · rw [if_pos (hcond.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hcond.mp hh)), if_neg h]

/-- The Knill–Laflamme matrix element for a matrix unit supported on `A`, expressed in
split coordinates: it is the partial Gram matrix of the code states over `B × Cs`. -/
lemma kl_sum {k d : ℕ} (Q : Code n k d q) (a a' : {i // i ∈ A} → Fin q) (i j : Fin (q ^ k)) :
    ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed A (Matrix.single a a' 1) x y * Q.state j y
      = ∑ b, ∑ c, (starRingEnd ℂ) (Q.state i ((splitEquiv A B Cs hmem hcard).symm (a, b, c)))
          * Q.state j ((splitEquiv A B Cs hmem hcard).symm (a', b, c)) := by
  classical
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  rw [← Equiv.sum_comp e.symm (fun x => ∑ y, (starRingEnd ℂ) (Q.state i x)
      * embed A (Matrix.single a a' 1) x y * Q.state j y)]
  have h1 : ∀ p, (∑ y, (starRingEnd ℂ) (Q.state i (e.symm p))
        * embed A (Matrix.single a a' 1) (e.symm p) y * Q.state j y)
      = ∑ p', (starRingEnd ℂ) (Q.state i (e.symm p))
        * embed A (Matrix.single a a' 1) (e.symm p) (e.symm p') * Q.state j (e.symm p') := by
    intro p
    rw [← Equiv.sum_comp e.symm (fun y => (starRingEnd ℂ) (Q.state i (e.symm p))
      * embed A (Matrix.single a a' 1) (e.symm p) y * Q.state j y)]
  rw [Finset.sum_congr rfl (fun p _ => h1 p)]
  simp only [Fintype.sum_prod_type, he, embed_split A B Cs hmem hcard, Matrix.single_apply,
    ite_and, mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
  simp [Finset.sum_ite_eq]

end Split

/-! ### The quantum Singleton bound -/

/-- **Key step.**  If `A` and `B` are disjoint sets of at most `d - 1` sites each, then the
dimension `q ^ k` of the code space is at most `q ^ |Cs|`, where `Cs` is the set of the
remaining `n - |A| - |B|` sites. -/
theorem dim_le_of_disjoint {n k d q : ℕ} (hq : 0 < q) (Q : Code n k d q)
    (A B : Finset (Fin n)) (hdisj : Disjoint A B)
    (hAcard : A.card ≤ d - 1) (hBcard : B.card ≤ d - 1) :
    q ^ k ≤ q ^ (n - A.card - B.card) := by
  classical
  set Cs := (A ∪ B)ᶜ with hCsdef
  have hmem : ∀ i : Fin n, (i ∈ A ∧ i ∉ B ∧ i ∉ Cs) ∨ (i ∉ A ∧ i ∈ B ∧ i ∉ Cs)
      ∨ (i ∉ A ∧ i ∉ B ∧ i ∈ Cs) := by
    intro i
    by_cases hia : i ∈ A
    · exact Or.inl ⟨hia, Finset.disjoint_left.mp hdisj hia, by simp [hCsdef, hia]⟩
    · by_cases hib : i ∈ B
      · exact Or.inr (Or.inl ⟨hia, hib, by simp [hCsdef, hib]⟩)
      · exact Or.inr (Or.inr ⟨hia, hib, by simp [hCsdef, hia, hib]⟩)
  have hmem' : ∀ i : Fin n, (i ∈ B ∧ i ∉ A ∧ i ∉ Cs) ∨ (i ∉ B ∧ i ∈ A ∧ i ∉ Cs)
      ∨ (i ∉ B ∧ i ∉ A ∧ i ∈ Cs) := by
    intro i
    rcases hmem i with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨h2, h1, h3⟩)
    · exact Or.inl ⟨h2, h1, h3⟩
    · exact Or.inr (Or.inr ⟨h2, h1, h3⟩)
  have hABcard : (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
  have hle : A.card + B.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ (A ∪ B))
    simp only [Finset.card_univ, Fintype.card_fin, hABcard] at h
    exact h
  have hCscard : Cs.card = n - A.card - B.card := by
    rw [hCsdef, Finset.card_compl, hABcard]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  have hcard : A.card + B.card + Cs.card = n := by omega
  have hcard' : B.card + A.card + Cs.card = n := by omega
  set e := splitEquiv (q := q) A B Cs hmem hcard with he
  -- the Knill-Laflamme conditions in Gram form, for `A` and for `B`
  obtain ⟨SA, hSA⟩ : ∃ SA : Matrix ({i // i ∈ A} → Fin q) ({i // i ∈ A} → Fin q) ℂ,
      ∀ (i j : Fin (q ^ k)) (a a' : {i // i ∈ A} → Fin q),
        ∑ b, ∑ c, Q.state i (e.symm (a, b, c))
            * (starRingEnd ℂ) (Q.state j (e.symm (a', b, c)))
          = if i = j then SA a a' else 0 := by
    have hch : ∀ a a' : {i // i ∈ A} → Fin q, ∃ cc : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed A (Matrix.single a a' 1) x y
          * Q.state j y = if i = j then cc else 0 :=
      fun a a' => Q.knill_laflamme A hAcard (Matrix.single a a' 1)
    choose cc hcc using hch
    refine ⟨Matrix.of fun a a' => (starRingEnd ℂ) (cc a a'), ?_⟩
    intro i j a a'
    have h := hcc a a' i j
    rw [kl_sum A B Cs hmem hcard Q a a' i j] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_sum, map_mul, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
  obtain ⟨SB, hSB⟩ : ∃ SB : Matrix ({i // i ∈ B} → Fin q) ({i // i ∈ B} → Fin q) ℂ,
      ∀ (i j : Fin (q ^ k)) (b b' : {i // i ∈ B} → Fin q),
        ∑ a, ∑ c, Q.state i (e.symm (a, b, c))
            * (starRingEnd ℂ) (Q.state j (e.symm (a, b', c)))
          = if i = j then SB b b' else 0 := by
    have hch : ∀ b b' : {i // i ∈ B} → Fin q, ∃ cc : ℂ, ∀ i j,
        ∑ x, ∑ y, (starRingEnd ℂ) (Q.state i x) * embed B (Matrix.single b b' 1) x y
          * Q.state j y = if i = j then cc else 0 :=
      fun b b' => Q.knill_laflamme B hBcard (Matrix.single b b' 1)
    choose cc hcc using hch
    refine ⟨Matrix.of fun b b' => (starRingEnd ℂ) (cc b b'), ?_⟩
    intro i j b b'
    have h := hcc b b' i j
    rw [kl_sum B A Cs hmem' hcard' Q b b' i j] at h
    simp only [splitEquiv_swap A B Cs hmem hcard hmem' hcard'] at h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [map_sum, map_mul, Complex.conj_conj, apply_ite (starRingEnd ℂ), map_zero] at h2
    rw [← h2]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
  -- a nonzero code vector
  have hpos : 0 < q ^ k := pow_pos hq k
  have hne : (fun (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
      (c : {i // i ∈ Cs} → Fin q) => Q.state ⟨0, hpos⟩ (e.symm (a, b, c))) ≠ 0 := by
    intro h
    have hzero : ∀ x, Q.state ⟨0, hpos⟩ x = 0 := by
      intro x
      have := congrFun (congrFun (congrFun h (e x).1) (e x).2.1) (e x).2.2
      simpa using this
    have h1 := Q.orthonormal ⟨0, hpos⟩ ⟨0, hpos⟩
    rw [if_pos rfl] at h1
    simp only [hzero, mul_zero, Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  -- apply the abstract bound
  have hmain := card_le_card_of_decoupled
    (fun (i : Fin (q ^ k)) a b c => Q.state i (e.symm (a, b, c))) SA SB hSA hSB ⟨0, hpos⟩ hne
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_coe, hCscard] at hmain
  exact hmain

/-- **The quantum Singleton bound.**

For an `[[n, k, d]]_q` quantum error-correcting code with `q ≥ 2` local dimensions and at
least one encoded qudit (`k ≥ 1`), one has `k + 2 (d - 1) ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The hypothesis `1 ≤ k` cannot be dropped with this (standard, Knill–Laflamme) definition of
the distance: for a one-dimensional code space the Knill–Laflamme conditions hold vacuously
for every error, so e.g. a single qubit would be an `[[1, 0, d]]` code for every `d`.  (For
`k = 0` the usual convention additionally demands that all reduced density matrices on
`d - 1` sites be maximally mixed.) -/
theorem quantum_singleton {n k d q : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (Q : Code n k d q) :
    k + 2 * (d - 1) ≤ n := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le two_pos hq
  by_cases hcase : 2 * (d - 1) ≤ n
  · -- there is room for two disjoint sets of `d - 1` sites
    obtain ⟨A, -, hA⟩ : ∃ A ⊆ (Finset.univ : Finset (Fin n)), A.card = d - 1 :=
      Finset.le_card_iff_exists_subset_card.mp (by simp; omega)
    obtain ⟨B, hBsub, hB⟩ : ∃ B ⊆ Aᶜ, B.card = d - 1 := by
      refine Finset.le_card_iff_exists_subset_card.mp ?_
      rw [Finset.card_compl, hA]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hdisj : Disjoint A B :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_compl.mp (hBsub hb)) ha
    have h := dim_le_of_disjoint hq0 Q A B hdisj (le_of_eq hA) (le_of_eq hB)
    rw [hA, hB] at h
    have := (Nat.pow_le_pow_iff_right hq).mp h
    omega
  · -- otherwise the two halves of the whole system are both correctable, forcing `k = 0`
    push_neg at hcase
    obtain ⟨A, -, hA⟩ : ∃ A ⊆ (Finset.univ : Finset (Fin n)), A.card = (n + 1) / 2 :=
      Finset.le_card_iff_exists_subset_card.mp (by simp; omega)
    obtain ⟨B, hBsub, hB⟩ : ∃ B ⊆ Aᶜ, B.card = n / 2 := by
      refine Finset.le_card_iff_exists_subset_card.mp ?_
      rw [Finset.card_compl, hA]
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    have hdisj : Disjoint A B :=
      Finset.disjoint_left.mpr fun a ha hb => (Finset.mem_compl.mp (hBsub hb)) ha
    have h := dim_le_of_disjoint hq0 Q A B hdisj (by omega) (by omega)
    rw [hA, hB] at h
    have hz : n - (n + 1) / 2 - n / 2 = 0 := by omega
    rw [hz, pow_zero] at h
    have : k = 0 := by
      by_contra hk0
      have : q ^ 1 ≤ q ^ k := Nat.pow_le_pow_right (by omega) (by omega)
      simp only [pow_one] at this
      omega
    omega

end QI

