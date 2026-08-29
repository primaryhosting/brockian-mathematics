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
open scoped Matrix
open scoped ComplexOrder

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

-- Note: the header block above is placed directly after `import Mathlib` because Lean requires
-- every `import` to precede all other commands, including module documentation comments.

namespace QI

/-! ## Auxiliary linear algebra: rank factorizations -/

/-- `LinearMap.toMatrix'` is inverse to `Matrix.mulVecLin`. -/
theorem toMatrix'_mulVecLin {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : LinearMap.toMatrix' A.mulVecLin = A :=
  (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl

/-- Every matrix factors through a space of dimension equal to its rank. -/
theorem exists_rank_factorization {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) :
    ∃ (X : Matrix m (Fin M.rank) ℂ) (Y : Matrix (Fin M.rank) n ℂ), M = X * Y := by
  classical
  set U := LinearMap.range M.mulVecLin with hU
  have hfin : Module.finrank ℂ U = M.rank := rfl
  let b : Module.Basis (Fin M.rank) ℂ U := (Module.finBasis ℂ U).reindex (finCongr hfin)
  refine ⟨Matrix.of fun i s => (b s : m → ℂ) i, Matrix.of fun s j =>
    b.repr ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩ s, ?_⟩
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  have h1 := congrArg (fun (v : U) => (v : m → ℂ) i)
    (b.sum_repr ⟨M.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩)
  simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
    smul_eq_mul] at h1
  have h2 : M.mulVecLin (Pi.single j 1) i = M i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [← h2, ← h1]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

/-- A matrix with full column rank has a left inverse. -/
theorem exists_left_inv {m : Type} [Fintype m] [DecidableEq m] {r : ℕ}
    (X : Matrix m (Fin r) ℂ) (h : X.rank = r) : ∃ L : Matrix (Fin r) m ℂ, L * X = 1 := by
  classical
  have hker : LinearMap.ker X.mulVecLin = ⊥ := by
    have h2 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [show Module.finrank ℂ (LinearMap.range X.mulVecLin) = r from h] at h2
    simp only [Module.finrank_fin_fun] at h2
    have h3 : Module.finrank ℂ (LinearMap.ker X.mulVecLin) = 0 := by omega
    exact Submodule.finrank_eq_zero.mp h3
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective X.mulVecLin hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h3 : LinearMap.toMatrix' (g ∘ₗ X.mulVecLin) = LinearMap.toMatrix' LinearMap.id := by
    rw [hg]
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulVecLin] at h3
  simpa using h3

/-- A matrix with full row rank has a right inverse. -/
theorem exists_right_inv {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
    (Y : Matrix (Fin r) n ℂ) (h : Y.rank = r) : ∃ S : Matrix n (Fin r) ℂ, Y * S = 1 := by
  classical
  have hr : LinearMap.range Y.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa using h
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective Y.mulVecLin hr
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h3 : LinearMap.toMatrix' (Y.mulVecLin ∘ₗ g) = LinearMap.toMatrix' LinearMap.id := by
    rw [hg]
  rw [LinearMap.toMatrix'_comp, toMatrix'_mulVecLin] at h3
  simpa using h3

/-- Rank is unchanged by multiplication with a nonzero scalar. -/
theorem rank_smul_ne_zero {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (c : ℂ) (hc : c ≠ 0) (M : Matrix m n ℂ) : (c • M).rank = M.rank := by
  have h : c • M = (c • (1 : Matrix m m ℂ)) * M := by simp [Matrix.smul_mul]
  rw [h]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (pow_ne_zero _ hc).isUnit

/-- A nonzero matrix has positive rank. -/
theorem rank_pos_of_ne_zero {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    {M : Matrix m n ℂ} (hM : M ≠ 0) : 1 ≤ M.rank := by
  by_contra h
  push_neg at h
  have hh : M.rank = 0 := by omega
  have hbot : LinearMap.range M.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp hh
  apply hM
  ext i j
  have hz : M.mulVecLin (Pi.single j 1) = 0 := by
    have hmem : M.mulVecLin (Pi.single j 1) ∈ LinearMap.range M.mulVecLin :=
      LinearMap.mem_range_self _ _
    rw [hbot] at hmem
    simpa using hmem
  have := congrFun hz i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-! ## Block-diagonal matrices -/

/-- Multiplication of block-diagonal matrices (all blocks equal). -/
theorem block_mul {R A B C : Type} [Fintype R] [DecidableEq R] [Fintype A] [Fintype B] [Fintype C]
    (M : Matrix A B ℂ) (N : Matrix B C ℂ) :
    (Matrix.of fun (p : R × A) (q : R × B) => if p.1 = q.1 then M p.2 q.2 else 0) *
      (Matrix.of fun (p : R × B) (q : R × C) => if p.1 = q.1 then N p.2 q.2 else 0) =
    Matrix.of fun (p : R × A) (q : R × C) => if p.1 = q.1 then (M * N) p.2 q.2 else 0 := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h]

/-- The block-diagonal matrix with identity blocks is the identity. -/
theorem block_one {R A : Type} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A] :
    (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then (1 : Matrix A A ℂ) p.2 q.2 else 0)
      = 1 := by
  ext p q
  by_cases h : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;>
    simp [Matrix.one_apply, h, h2, Prod.ext_iff]

/-- The rank of a block-diagonal matrix with `|R|` copies of `g` is `|R| * rank g`
(the inequality we need). -/
theorem card_mul_rank_le_rank_block {R A : Type} [Fintype R] [DecidableEq R] [Fintype A]
    [DecidableEq A] (g : Matrix A A ℂ) :
    Fintype.card R * g.rank ≤
      (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then g p.2 q.2 else 0).rank := by
  classical
  obtain ⟨X, Y, hXY⟩ := exists_rank_factorization g
  have hX : X.rank = g.rank := by
    refine le_antisymm (by simpa using X.rank_le_card_width) ?_
    calc g.rank = (X * Y).rank := by rw [← hXY]
      _ ≤ X.rank := Matrix.rank_mul_le_left X Y
  have hY : Y.rank = g.rank := by
    refine le_antisymm (by simpa using Y.rank_le_card_height) ?_
    calc g.rank = (X * Y).rank := by rw [← hXY]
      _ ≤ Y.rank := Matrix.rank_mul_le_right X Y
  obtain ⟨L, hL⟩ := exists_left_inv X hX
  obtain ⟨S, hS⟩ := exists_right_inv Y hY
  set BX : Matrix (R × A) (R × Fin g.rank) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then X p.2 q.2 else 0 with hBXdef
  set BY : Matrix (R × Fin g.rank) (R × A) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then Y p.2 q.2 else 0 with hBYdef
  set BL : Matrix (R × Fin g.rank) (R × A) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then L p.2 q.2 else 0 with hBLdef
  set BS : Matrix (R × A) (R × Fin g.rank) ℂ :=
    Matrix.of fun p q => if p.1 = q.1 then S p.2 q.2 else 0 with hBSdef
  have hBXY : BX * BY = Matrix.of fun (p : R × A) (q : R × A) =>
      if p.1 = q.1 then g p.2 q.2 else 0 := by
    rw [hBXdef, hBYdef, block_mul, ← hXY]
  have hBL' : BL * BX = 1 := by rw [hBLdef, hBXdef, block_mul, hL, block_one]
  have hBS' : BY * BS = 1 := by rw [hBYdef, hBSdef, block_mul, hS, block_one]
  have h1 : (Matrix.of fun (p : R × A) (q : R × A) => if p.1 = q.1 then g p.2 q.2 else 0) * BS
      = BX := by rw [← hBXY, Matrix.mul_assoc, hBS', Matrix.mul_one]
  calc Fintype.card R * g.rank
      = (1 : Matrix (R × Fin g.rank) (R × Fin g.rank) ℂ).rank := by
        rw [Matrix.rank_one, Fintype.card_prod, Fintype.card_fin]
    _ = (BL * BX).rank := by rw [hBL']
    _ ≤ BX.rank := Matrix.rank_mul_le_right BL BX
    _ = ((Matrix.of fun (p : R × A) (q : R × A) =>
          if p.1 = q.1 then g p.2 q.2 else 0) * BS).rank := by rw [h1]
    _ ≤ _ := Matrix.rank_mul_le_left _ _

/-- Entrywise complex conjugation preserves the rank. -/
theorem rank_map_conj {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℂ) : (M.map (starRingEnd ℂ)).rank = M.rank := by
  have key : ∀ N : Matrix m n ℂ, (N.map (starRingEnd ℂ)).rank ≤ N.rank := by
    intro N
    obtain ⟨X, Y, h⟩ := exists_rank_factorization N
    have hmap : N.map (starRingEnd ℂ)
        = (X.map (starRingEnd ℂ)) * (Y.map (starRingEnd ℂ)) := by
      conv_lhs => rw [h]
      rw [Matrix.map_mul]
    rw [hmap]
    calc ((X.map (starRingEnd ℂ)) * (Y.map (starRingEnd ℂ))).rank
        ≤ (X.map (starRingEnd ℂ)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin N.rank) := Matrix.rank_le_card_width _
      _ = N.rank := by simp
  refine le_antisymm (key M) ?_
  have h2 := key (M.map (starRingEnd ℂ))
  have hid : (M.map (starRingEnd ℂ)).map (starRingEnd ℂ) = M := by
    ext p q
    simp
  rwa [hid] at h2

/-- The rank of the transpose, over `ℂ`. -/
theorem rank_transpose_complex {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    (M : Matrix m n ℂ) : Mᵀ.rank = M.rank := by
  have h : Mᵀ = (Mᴴ).map (starRingEnd ℂ) := by
    ext p q
    simp
  rw [h, rank_map_conj, Matrix.rank_conjTranspose]

/-! ## The tensor flattening rank inequality -/

/-- For a three-index tensor `f p b c`, the rank of the flattening that groups `(b, c)` together
is at most the product of the ranks of the flattenings that isolate `b` and `c`.
This is the linear-algebra substitute for subadditivity of entropy. -/
theorem rank_flatten_le {P B C : Type} [Fintype P] [Fintype B] [Fintype C] [DecidableEq P]
    [DecidableEq B] [DecidableEq C] (f : P → B → C → ℂ) :
    (Matrix.of fun (q : B × C) (p : P) => f p q.1 q.2).rank ≤
      (Matrix.of fun (b : B) (p : P × C) => f p.1 b p.2).rank *
        (Matrix.of fun (c : C) (p : P × B) => f p.1 p.2 c).rank := by
  classical
  set MB : Matrix B (P × C) ℂ := Matrix.of fun b p => f p.1 b p.2 with hMBdef
  set MC : Matrix C (P × B) ℂ := Matrix.of fun c p => f p.1 p.2 c with hMCdef
  obtain ⟨XB, YB, hBfac⟩ := exists_rank_factorization MB
  obtain ⟨XC, YC, hCfac⟩ := exists_rank_factorization MC
  have hXB : XB.rank = MB.rank := by
    refine le_antisymm (by simpa using XB.rank_le_card_width) ?_
    calc MB.rank = (XB * YB).rank := by rw [← hBfac]
      _ ≤ XB.rank := Matrix.rank_mul_le_left XB YB
  obtain ⟨LB, hLB⟩ := exists_left_inv XB hXB
  have hMB : ∀ p b c, ∑ s, XB b s * YB s (p, c) = f p b c := by
    intro p b c
    have := congrFun (congrFun hBfac b) (p, c)
    simpa [hMBdef, Matrix.mul_apply] using this.symm
  have hMC : ∀ p b c, ∑ t, XC c t * YC t (p, b) = f p b c := by
    intro p b c
    have := congrFun (congrFun hCfac c) (p, b)
    simpa [hMCdef, Matrix.mul_apply] using this.symm
  have hLX : ∀ s s', (∑ b, LB s b * XB b s') = if s = s' then 1 else 0 := by
    intro s s'
    have := congrFun (congrFun hLB s) s'
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  set W : Matrix (B × C) (Fin MB.rank × Fin MC.rank) ℂ :=
    Matrix.of fun q st => XB q.1 st.1 * XC q.2 st.2 with hWdef
  set Z : Matrix (Fin MB.rank × Fin MC.rank) P ℂ :=
    Matrix.of fun st p => ∑ b, LB st.1 b * YC st.2 (p, b) with hZdef
  have key : (Matrix.of fun (q : B × C) (p : P) => f p q.1 q.2) = W * Z := by
    ext q p
    obtain ⟨b, c⟩ := q
    simp only [Matrix.of_apply, Matrix.mul_apply, hWdef, hZdef]
    symm
    rw [Fintype.sum_prod_type]
    have step1 : ∀ s : Fin MB.rank,
        (∑ t : Fin MC.rank, (XB b s * XC c t) * (∑ b', LB s b' * YC t (p, b')))
          = ∑ b', (XB b s * LB s b') * f p b' c := by
      intro s
      have hrw : ∀ b' : B, f p b' c = ∑ t, XC c t * YC t (p, b') := fun b' => (hMC p b' c).symm
      simp only [hrw]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun t _ => by ring
    simp only [step1]
    have step2 : ∀ b' : B, f p b' c = ∑ s', XB b' s' * YB s' (p, c) :=
      fun b' => (hMB p b' c).symm
    calc ∑ s : Fin MB.rank, ∑ b' : B, (XB b s * LB s b') * f p b' c
        = ∑ s : Fin MB.rank, ∑ s' : Fin MB.rank,
            XB b s * (∑ b', LB s b' * XB b' s') * YB s' (p, c) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp only [step2]
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun b' _ => by ring
      _ = ∑ s : Fin MB.rank, XB b s * YB s (p, c) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp only [hLX]
          simp [Finset.sum_ite_eq]
      _ = f p b c := hMB p b c
  calc (Matrix.of fun (q : B × C) (p : P) => f p q.1 q.2).rank
      = (W * Z).rank := by rw [key]
    _ ≤ W.rank := Matrix.rank_mul_le_left W Z
    _ ≤ Fintype.card (Fin MB.rank × Fin MC.rank) := W.rank_le_card_width
    _ = MB.rank * MC.rank := by simp

/-! ## The abstract four-partite bound -/

/-- **Core of the quantum Singleton bound.**

`ψ i a b c` is the (unnormalised) encoding tensor of a quantum code: `i` indexes an
orthonormal basis of the logical space `R`, and `a`, `b`, `c` index the physical degrees of
freedom in three disjoint regions `A`, `B`, `C`.

The hypotheses `hA` and `hB` are the Knill–Laflamme conditions saying that the erasures of the
regions `A` and of `B` are correctable: the reduced density matrix on the region, computed
between two code basis vectors, is a fixed matrix (`gA`, resp. `gB`) times `δᵢⱼ`.

Conclusion: the logical dimension is at most the dimension of the remaining region `C`. -/
theorem card_le_card_of_correctable {R A B C : Type} [Fintype R] [Fintype A] [Fintype B]
    [Fintype C] [DecidableEq R] [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (ψ : R → A → B → C → ℂ) (hψ : ψ ≠ 0) (gA : Matrix A A ℂ) (gB : Matrix B B ℂ)
    (hA : ∀ i j a a', (∑ b, ∑ c, ψ i a b c * (starRingEnd ℂ) (ψ j a' b c))
      = (if i = j then 1 else 0) * gA a a')
    (hB : ∀ i j b b', (∑ a, ∑ c, ψ i a b c * (starRingEnd ℂ) (ψ j a b' c))
      = (if i = j then 1 else 0) * gB b b') :
    Fintype.card R ≤ Fintype.card C := by
  classical
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [Fintype.card_eq_zero]
  set MA : Matrix A (R × B × C) ℂ := Matrix.of fun a p => ψ p.1 a p.2.1 p.2.2 with hMAdef
  set MB : Matrix B (R × A × C) ℂ := Matrix.of fun b p => ψ p.1 p.2.1 b p.2.2 with hMBdef
  set MC : Matrix C (R × A × B) ℂ := Matrix.of fun c p => ψ p.1 p.2.1 p.2.2 c with hMCdef
  set MRA : Matrix (R × A) (B × C) ℂ := Matrix.of fun p q => ψ p.1 p.2 q.1 q.2 with hMRAdef
  set MRB : Matrix (R × B) (A × C) ℂ := Matrix.of fun p q => ψ p.1 q.1 p.2 q.2 with hMRBdef
  -- Step 1: the Knill–Laflamme conditions as matrix identities
  have hRA : MRA * MRAᴴ
      = Matrix.of fun (p q : R × A) => if p.1 = q.1 then gA p.2 q.2 else 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hMRAdef,
      Fintype.sum_prod_type, ← starRingEnd_apply]
    rw [hA p.1 q.1 p.2 q.2]
    by_cases h : p.1 = q.1 <;> simp [h]
  have hRB : MRB * MRBᴴ
      = Matrix.of fun (p q : R × B) => if p.1 = q.1 then gB p.2 q.2 else 0 := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hMRBdef,
      Fintype.sum_prod_type, ← starRingEnd_apply]
    rw [hB p.1 q.1 p.2 q.2]
    by_cases h : p.1 = q.1 <;> simp [h]
  -- Step 2: the marginals on `A` and `B`
  have hcard : ((Fintype.card R : ℂ)) ≠ 0 := by
    simp [Fintype.card_ne_zero]
  have hMAA : MA * MAᴴ = (Fintype.card R : ℂ) • gA := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hMAdef,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, ← starRingEnd_apply]
    have : ∀ i : R, (∑ b, ∑ c, ψ i a b c * (starRingEnd ℂ) (ψ i a' b c)) = gA a a' := by
      intro i
      rw [hA i i a a']
      simp
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [mul_comm]
  have hMBB : MB * MBᴴ = (Fintype.card R : ℂ) • gB := by
    ext b b'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hMBdef,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, ← starRingEnd_apply]
    have : ∀ i : R, (∑ a, ∑ c, ψ i a b c * (starRingEnd ℂ) (ψ i a b' c)) = gB b b' := by
      intro i
      rw [hB i i b b']
      simp
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [mul_comm]
  have hrankA : MA.rank = gA.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MA, hMAA, rank_smul_ne_zero _ hcard]
  have hrankB : MB.rank = gB.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MB, hMBB, rank_smul_ne_zero _ hcard]
  -- Step 3: the two flattening inequalities
  have hflatA : Fintype.card R * gA.rank ≤ MB.rank * MC.rank := by
    have h1 : Fintype.card R * gA.rank ≤ MRA.rank := by
      rw [← Matrix.rank_self_mul_conjTranspose MRA, hRA]
      exact card_mul_rank_le_rank_block gA
    have h2 : MRA.rank = (Matrix.of fun (q : B × C) (p : R × A) => ψ p.1 p.2 q.1 q.2).rank := by
      rw [← rank_transpose_complex MRA]
      rfl
    have h3 := rank_flatten_le (P := R × A) (B := B) (C := C) fun p b c => ψ p.1 p.2 b c
    have h4 : (Matrix.of fun (b : B) (p : (R × A) × C) => ψ p.1.1 p.1.2 b p.2).rank = MB.rank := by
      have : (Matrix.of fun (b : B) (p : (R × A) × C) => ψ p.1.1 p.1.2 b p.2)
          = MB.submatrix (Equiv.refl B) (Equiv.prodAssoc R A C) := rfl
      rw [this, Matrix.rank_submatrix]
    have h5 : (Matrix.of fun (c : C) (p : (R × A) × B) => ψ p.1.1 p.1.2 p.2 c).rank = MC.rank := by
      have : (Matrix.of fun (c : C) (p : (R × A) × B) => ψ p.1.1 p.1.2 p.2 c)
          = MC.submatrix (Equiv.refl C) (Equiv.prodAssoc R A B) := rfl
      rw [this, Matrix.rank_submatrix]
    rw [h4, h5] at h3
    omega
  have hflatB : Fintype.card R * gB.rank ≤ MA.rank * MC.rank := by
    have h1 : Fintype.card R * gB.rank ≤ MRB.rank := by
      rw [← Matrix.rank_self_mul_conjTranspose MRB, hRB]
      exact card_mul_rank_le_rank_block gB
    have h2 : MRB.rank = (Matrix.of fun (q : A × C) (p : R × B) => ψ p.1 q.1 p.2 q.2).rank := by
      rw [← rank_transpose_complex MRB]
      rfl
    have h3 := rank_flatten_le (P := R × B) (B := A) (C := C) fun p a c => ψ p.1 a p.2 c
    have h4 : (Matrix.of fun (a : A) (p : (R × B) × C) => ψ p.1.1 a p.1.2 p.2).rank = MA.rank := by
      have : (Matrix.of fun (a : A) (p : (R × B) × C) => ψ p.1.1 a p.1.2 p.2)
          = MA.submatrix (Equiv.refl A) (Equiv.prodAssoc R B C) := rfl
      rw [this, Matrix.rank_submatrix]
    have h5 : (Matrix.of fun (c : C) (p : (R × B) × A) => ψ p.1.1 p.2 p.1.2 c).rank = MC.rank := by
      have : (Matrix.of fun (c : C) (p : (R × B) × A) => ψ p.1.1 p.2 p.1.2 c)
          = MC.submatrix (Equiv.refl C)
            (⟨fun p => (p.1.1, p.2, p.1.2), fun p => ((p.1, p.2.2), p.2.1),
              fun _ => rfl, fun _ => rfl⟩ : (R × B) × A ≃ R × A × B) := rfl
      rw [this, Matrix.rank_submatrix]
    rw [h4, h5] at h3
    omega
  -- Step 4: nonvanishing
  have hMAne : MA ≠ 0 := by
    intro h
    apply hψ
    funext i a b c
    have := congrFun (congrFun h a) (i, b, c)
    simpa [hMAdef] using this
  have hMBne : MB ≠ 0 := by
    intro h
    apply hψ
    funext i a b c
    have := congrFun (congrFun h b) (i, a, c)
    simpa [hMBdef] using this
  have hApos : 1 ≤ gA.rank := hrankA ▸ rank_pos_of_ne_zero hMAne
  have hBpos : 1 ≤ gB.rank := hrankB ▸ rank_pos_of_ne_zero hMBne
  -- Step 5: combine
  rw [hrankA] at hflatB
  rw [hrankB] at hflatA
  have hsq : Fintype.card R * Fintype.card R ≤ MC.rank * MC.rank := by
    have h := Nat.mul_le_mul hflatA hflatB
    have hpos : 0 < gA.rank * gB.rank := Nat.mul_pos hApos hBpos
    have : (Fintype.card R * Fintype.card R) * (gA.rank * gB.rank)
        ≤ (MC.rank * MC.rank) * (gA.rank * gB.rank) := by
      calc (Fintype.card R * Fintype.card R) * (gA.rank * gB.rank)
          = (Fintype.card R * gA.rank) * (Fintype.card R * gB.rank) := by ring
        _ ≤ (gB.rank * MC.rank) * (gA.rank * MC.rank) := h
        _ = (MC.rank * MC.rank) * (gA.rank * gB.rank) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hKC : Fintype.card R ≤ MC.rank := by
    nlinarith [hsq]
  exact hKC.trans MC.rank_le_card_height

/-! ## Codes on `n` qudits

The physical Hilbert space of `n` qudits of local dimension `q` is `ℂ^(Fin n → Fin q)`, with the
product basis indexed by configurations `Fin n → Fin q`. A code with `K` (orthonormal) basis
codewords is described by its coefficient tensor `ψ : Fin K → (Fin n → Fin q) → ℂ`.
-/

/-- `glue S a y` is the configuration that agrees with `a` on `S` and with `y` off `S`. -/
def glue {n q : ℕ} (S : Finset (Fin n)) (a : {i : Fin n // i ∈ S} → Fin q)
    (y : {i : Fin n // i ∉ S} → Fin q) : Fin n → Fin q := fun t =>
  if h : t ∈ S then a ⟨t, h⟩ else y ⟨t, h⟩

/-- The configuration assembled from data on `SA`, on `SB` and on the rest. -/
def combine {n q : ℕ} (SA SB : Finset (Fin n)) (a : {i : Fin n // i ∈ SA} → Fin q)
    (b : {i : Fin n // i ∈ SB} → Fin q) (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) :
    Fin n → Fin q := fun t =>
  if h : t ∈ SA then a ⟨t, h⟩
  else if h2 : t ∈ SB then b ⟨t, h2⟩
  else c ⟨t, Finset.mem_compl.mpr (by simp [Finset.mem_union, h, h2])⟩

/-- Data off `SA`, assembled from data on `SB` and data on the rest. -/
def mergeA {n q : ℕ} (SA SB : Finset (Fin n)) (b : {i : Fin n // i ∈ SB} → Fin q)
    (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) : {i : Fin n // i ∉ SA} → Fin q := fun t =>
  if h : t.val ∈ SB then b ⟨t.val, h⟩
  else c ⟨t.val, Finset.mem_compl.mpr (by simp [Finset.mem_union, t.2, h])⟩

/-- Data off `SB`, assembled from data on `SA` and data on the rest. -/
def mergeB {n q : ℕ} (SA SB : Finset (Fin n)) (a : {i : Fin n // i ∈ SA} → Fin q)
    (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) : {i : Fin n // i ∉ SB} → Fin q := fun t =>
  if h : t.val ∈ SA then a ⟨t.val, h⟩
  else c ⟨t.val, Finset.mem_compl.mpr (by simp [Finset.mem_union, t.2, h])⟩

/-- **Knill–Laflamme condition**: the erasure of the qudits in `S` is correctable for the code
spanned by `ψ`, i.e. the reduced density matrix on `S` between two codewords is `δᵢⱼ` times a
fixed matrix `g`. -/
def ErasureCorrectable {n q K : ℕ} (ψ : Fin K → (Fin n → Fin q) → ℂ) (S : Finset (Fin n)) : Prop :=
  ∃ g : ({i : Fin n // i ∈ S} → Fin q) → ({i : Fin n // i ∈ S} → Fin q) → ℂ,
    ∀ (i j : Fin K) (a a' : {i : Fin n // i ∈ S} → Fin q),
      (∑ y : {i : Fin n // i ∉ S} → Fin q,
        ψ i (glue S a y) * (starRingEnd ℂ) (ψ j (glue S a' y))) = (if i = j then 1 else 0) * g a a'

theorem notMem_left_of_mem_compl_union {n : ℕ} {SA SB : Finset (Fin n)} {t : Fin n}
    (h : t ∈ (SA ∪ SB)ᶜ) : t ∉ SA := by
  simp only [Finset.mem_compl, Finset.mem_union, not_or] at h
  exact h.1

theorem notMem_right_of_mem_compl_union {n : ℕ} {SA SB : Finset (Fin n)} {t : Fin n}
    (h : t ∈ (SA ∪ SB)ᶜ) : t ∉ SB := by
  simp only [Finset.mem_compl, Finset.mem_union, not_or] at h
  exact h.2

theorem combine_eq_glueA {n q : ℕ} (SA SB : Finset (Fin n)) (a : {i : Fin n // i ∈ SA} → Fin q)
    (b : {i : Fin n // i ∈ SB} → Fin q) (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) :
    combine SA SB a b c = glue SA a (mergeA SA SB b c) := by
  funext t
  by_cases h : t ∈ SA
  · simp [combine, glue, h]
  · by_cases h2 : t ∈ SB <;> simp [combine, glue, mergeA, h, h2]

theorem combine_eq_glueB {n q : ℕ} (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB)
    (a : {i : Fin n // i ∈ SA} → Fin q) (b : {i : Fin n // i ∈ SB} → Fin q)
    (c : {i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) :
    combine SA SB a b c = glue SB b (mergeB SA SB a c) := by
  funext t
  by_cases h : t ∈ SB
  · have hnA : t ∉ SA := Finset.disjoint_right.mp hdisj h
    simp [combine, glue, hnA, h]
  · by_cases h2 : t ∈ SA <;> simp [combine, glue, mergeB, h, h2]

theorem mergeA_bijective {n q : ℕ} (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB) :
    Function.Bijective (fun bc : ({i : Fin n // i ∈ SB} → Fin q) ×
      ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) => mergeA SA SB bc.1 bc.2) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => (fun s => y ⟨s.val, Finset.disjoint_right.mp hdisj s.2⟩,
    fun s => y ⟨s.val, notMem_left_of_mem_compl_union s.2⟩), ?_, ?_⟩
  · rintro ⟨b, c⟩
    refine Prod.ext ?_ ?_ <;> funext s
    · simp [mergeA, s.2]
    · have hs := s.2
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hs
      simp [mergeA, hs.2]
  · intro y
    funext t
    by_cases h : t.val ∈ SB <;> simp [mergeA, h]

theorem mergeB_bijective {n q : ℕ} (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB) :
    Function.Bijective (fun ac : ({i : Fin n // i ∈ SA} → Fin q) ×
      ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) => mergeB SA SB ac.1 ac.2) := by
  rw [Function.bijective_iff_has_inverse]
  refine ⟨fun y => (fun s => y ⟨s.val, Finset.disjoint_left.mp hdisj s.2⟩,
    fun s => y ⟨s.val, notMem_right_of_mem_compl_union s.2⟩), ?_, ?_⟩
  · rintro ⟨a, c⟩
    refine Prod.ext ?_ ?_ <;> funext s
    · simp [mergeB, s.2]
    · have hs := s.2
      simp only [Finset.mem_compl, Finset.mem_union, not_or] at hs
      simp [mergeB, hs.1]
  · intro y
    funext t
    by_cases h : t.val ∈ SA <;> simp [mergeB, h]

theorem combine_restrict {n q : ℕ} (SA SB : Finset (Fin n)) (x : Fin n → Fin q) :
    combine SA SB (fun s => x s.val) (fun s => x s.val) (fun s => x s.val) = x := by
  funext t
  by_cases h : t ∈ SA
  · simp [combine, h]
  · by_cases h2 : t ∈ SB <;> simp [combine, h, h2]

/-- If the erasures of two disjoint regions `SA` and `SB` are both correctable, then the code
dimension is at most the dimension of the complement of `SA ∪ SB`. -/
theorem card_le_of_two_correctable {n q K : ℕ} (ψ : Fin K → (Fin n → Fin q) → ℂ) (hψ : ψ ≠ 0)
    (SA SB : Finset (Fin n)) (hdisj : Disjoint SA SB)
    (hcA : ErasureCorrectable ψ SA) (hcB : ErasureCorrectable ψ SB) :
    K ≤ q ^ (n - SA.card - SB.card) := by
  classical
  obtain ⟨gA, hgA⟩ := hcA
  obtain ⟨gB, hgB⟩ := hcB
  set Ψ : Fin K → ({i : Fin n // i ∈ SA} → Fin q) → ({i : Fin n // i ∈ SB} → Fin q) →
      ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q) → ℂ :=
    fun i a b c => ψ i (combine SA SB a b c) with hΨdef
  have hΨ : Ψ ≠ 0 := by
    intro h
    apply hψ
    funext i x
    have := congrFun (congrFun (congrFun (congrFun h i) (fun s => x s.val))
      (fun s => x s.val)) (fun s => x s.val)
    simpa [hΨdef, combine_restrict] using this
  have h1 : ∀ (i j : Fin K) (a a' : {i : Fin n // i ∈ SA} → Fin q),
      (∑ b, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a' b c))
        = (if i = j then 1 else 0) * (Matrix.of gA) a a' := by
    intro i j a a'
    calc (∑ b, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a' b c))
        = ∑ bc : ({i : Fin n // i ∈ SB} → Fin q) × ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q),
            Ψ i a bc.1 bc.2 * (starRingEnd ℂ) (Ψ j a' bc.1 bc.2) :=
          (Fintype.sum_prod_type fun bc => Ψ i a bc.1 bc.2 * (starRingEnd ℂ) (Ψ j a' bc.1 bc.2)).symm
      _ = ∑ y, ψ i (glue SA a y) * (starRingEnd ℂ) (ψ j (glue SA a' y)) :=
          Fintype.sum_bijective _ (mergeA_bijective SA SB hdisj) _ _
            (fun bc => by simp [hΨdef, combine_eq_glueA])
      _ = _ := hgA i j a a'
  have h2 : ∀ (i j : Fin K) (b b' : {i : Fin n // i ∈ SB} → Fin q),
      (∑ a, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a b' c))
        = (if i = j then 1 else 0) * (Matrix.of gB) b b' := by
    intro i j b b'
    calc (∑ a, ∑ c, Ψ i a b c * (starRingEnd ℂ) (Ψ j a b' c))
        = ∑ ac : ({i : Fin n // i ∈ SA} → Fin q) × ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q),
            Ψ i ac.1 b ac.2 * (starRingEnd ℂ) (Ψ j ac.1 b' ac.2) :=
          (Fintype.sum_prod_type fun ac => Ψ i ac.1 b ac.2 * (starRingEnd ℂ) (Ψ j ac.1 b' ac.2)).symm
      _ = ∑ y, ψ i (glue SB b y) * (starRingEnd ℂ) (ψ j (glue SB b' y)) :=
          Fintype.sum_bijective _ (mergeB_bijective SA SB hdisj) _ _
            (fun ac => by simp [hΨdef, combine_eq_glueB SA SB hdisj])
      _ = _ := hgB i j b b'
  have hmain := card_le_card_of_correctable Ψ hΨ (Matrix.of gA) (Matrix.of gB) h1 h2
  have hcardC : Fintype.card ({i : Fin n // i ∈ (SA ∪ SB)ᶜ} → Fin q)
      = q ^ (n - SA.card - SB.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Finset.card_compl,
      Finset.card_union_of_disjoint hdisj]
    simp [Nat.sub_sub]
  rw [Fintype.card_fin, hcardC] at hmain
  exact hmain

/-- **Quantum Singleton bound.**

Let `ψ` be an `[[n, k, d]]_q` quantum error correcting code: a code of `q^k` orthonormal
codewords in the space of `n` qudits of local dimension `q` (`horth`) whose distance is at
least `d`, i.e. the erasure of any set of at most `d - 1` qudits is correctable in the sense of
the Knill–Laflamme conditions (`hdist`).

Then `n - k ≥ 2 (d - 1)`, stated here in the subtraction-free form `k + 2 * (d - 1) ≤ n`.

The hypothesis `1 ≤ k` (a nontrivial logical space) is necessary: for `k = 0` a single product
state on one qudit satisfies the Knill–Laflamme conditions for every one-qudit erasure, i.e. it
is a "`[[1, 0, 2]]` code", while `2 * (2 - 1) ≤ 1` fails.

The proof is the rank (Schmidt-rank) version of the entropic argument: writing `R` for the
logical index and splitting the qudits into two correctable regions `A`, `B` of size `d - 1`
and the rest `C`, the Knill–Laflamme conditions give
`rank ρ_{BC} = rank ρ_{RA} = |R| · rank ρ_A` and `rank ρ_{AC} = |R| · rank ρ_B`, while
`rank ρ_{BC} ≤ rank ρ_B · rank ρ_C` and `rank ρ_{AC} ≤ rank ρ_A · rank ρ_C`; multiplying and
cancelling yields `|R| ≤ rank ρ_C ≤ q^(n - 2(d-1))`. -/
theorem quantum_singleton {n q k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (ψ : Fin (q ^ k) → (Fin n → Fin q) → ℂ)
    (horth : ∀ i j : Fin (q ^ k),
      (∑ x : Fin n → Fin q, ψ i x * (starRingEnd ℂ) (ψ j x)) = if i = j then 1 else 0)
    (hdist : ∀ S : Finset (Fin n), S.card ≤ d - 1 → ErasureCorrectable ψ S) :
    k + 2 * (d - 1) ≤ n := by
  classical
  set e := d - 1 with he
  have hK2 : 2 ≤ q ^ k := by
    calc 2 ≤ q := hq
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hψ : ψ ≠ 0 := by
    intro h
    have hlt : 0 < q ^ k := by omega
    have h0 := horth ⟨0, hlt⟩ ⟨0, hlt⟩
    rw [h] at h0
    simp at h0
  by_cases hcase : 2 * e ≤ n
  · have hen : e ≤ n := by omega
    set fA : Fin e → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hen⟩ with hfA
    set fB : Fin e → Fin n := fun j => ⟨e + j.val, by have := j.isLt; omega⟩ with hfB
    have hinjA : Function.Injective fA := by
      intro x y hxy
      have := congrArg Fin.val hxy
      simp only [hfA] at this
      exact Fin.ext this
    have hinjB : Function.Injective fB := by
      intro x y hxy
      have := congrArg Fin.val hxy
      simp only [hfB] at this
      exact Fin.ext (by omega)
    set SA := Finset.image fA Finset.univ with hSA
    set SB := Finset.image fB Finset.univ with hSB
    have hcardA : SA.card = e := by
      rw [hSA, Finset.card_image_of_injective _ hinjA, Finset.card_univ, Fintype.card_fin]
    have hcardB : SB.card = e := by
      rw [hSB, Finset.card_image_of_injective _ hinjB, Finset.card_univ, Fintype.card_fin]
    have hdisj : Disjoint SA SB := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [hSA, Finset.mem_image] at ha
      rw [hSB, Finset.mem_image] at hb
      obtain ⟨x, -, hx⟩ := ha
      obtain ⟨y, -, hy⟩ := hb
      have hx' := congrArg Fin.val hx
      have hy' := congrArg Fin.val hy
      simp only [hfA, hfB] at hx' hy'
      have := x.isLt
      omega
    have hbound := card_le_of_two_correctable ψ hψ SA SB hdisj
      (hdist SA (by rw [hcardA])) (hdist SB (by rw [hcardB]))
    rw [hcardA, hcardB] at hbound
    have hkle : k ≤ n - e - e := (Nat.pow_le_pow_iff_right hq).mp hbound
    omega
  · exfalso
    set m := min e n with hm
    have hmn : m ≤ n := min_le_right _ _
    set fA : Fin m → Fin n := fun j => ⟨j.val, lt_of_lt_of_le j.isLt hmn⟩ with hfA
    have hinjA : Function.Injective fA := by
      intro x y hxy
      have := congrArg Fin.val hxy
      simp only [hfA] at this
      exact Fin.ext this
    set SA := Finset.image fA Finset.univ with hSA
    have hcardA : SA.card = m := by
      rw [hSA, Finset.card_image_of_injective _ hinjA, Finset.card_univ, Fintype.card_fin]
    have hcardB : (SAᶜ).card = n - m := by
      rw [Finset.card_compl, hcardA, Fintype.card_fin]
    have hbound := card_le_of_two_correctable ψ hψ SA SAᶜ disjoint_compl_right
      (hdist SA (by rw [hcardA]; omega)) (hdist SAᶜ (by rw [hcardB]; omega))
    rw [hcardA, hcardB] at hbound
    have hzero : n - m - (n - m) = 0 := by omega
    rw [hzero, pow_zero] at hbound
    omega

/-! ## Non-vacuity: the hypotheses of `quantum_singleton` are satisfiable -/

/-- Erasure of the empty region is correctable for any orthonormal family of codewords. -/
theorem erasureCorrectable_empty {n q K : ℕ} (ψ : Fin K → (Fin n → Fin q) → ℂ)
    (horth : ∀ i j : Fin K,
      (∑ x : Fin n → Fin q, ψ i x * (starRingEnd ℂ) (ψ j x)) = if i = j then 1 else 0) :
    ErasureCorrectable ψ ∅ := by
  refine ⟨fun _ _ => 1, fun i j a a' => ?_⟩
  rw [mul_one, ← horth i j]
  have hbij : Function.Bijective
      (fun y : {i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q => glue ∅ a y) := by
    rw [Function.bijective_iff_has_inverse]
    refine ⟨fun x t => x t.val, fun y => ?_, fun x => ?_⟩
    · funext t
      simp [glue]
    · funext t
      simp [glue]
  refine Fintype.sum_bijective _ hbij _
    (fun x => ψ i x * (starRingEnd ℂ) (ψ j x)) (fun y => ?_)
  have hgl : glue (∅ : Finset (Fin n)) a' y = glue ∅ a y := by
    funext t
    simp [glue]
  rw [hgl]

/-- The trivial "code" consisting of the whole `n`-qudit space is an orthonormal family whose
empty-region erasures are correctable; hence the hypotheses of `quantum_singleton` are
satisfiable (here with `k = n` and `d = 1`). -/
theorem exists_full_code (n q : ℕ) :
    ∃ ψ : Fin (q ^ n) → (Fin n → Fin q) → ℂ,
      (∀ i j : Fin (q ^ n),
        (∑ x : Fin n → Fin q, ψ i x * (starRingEnd ℂ) (ψ j x)) = if i = j then 1 else 0) ∧
      ∀ S : Finset (Fin n), S.card ≤ 1 - 1 → ErasureCorrectable ψ S := by
  classical
  have hcard : Fintype.card (Fin n → Fin q) = q ^ n := by simp
  let ee : Fin (q ^ n) ≃ (Fin n → Fin q) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i x => if x = ee i then 1 else 0, ?_, ?_⟩
  · intro i j
    by_cases h : i = j
    · subst h
      simp
    · have h' : ee i ≠ ee j := fun hc => h (ee.injective hc)
      simp [h, Ne.symm h', Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]
  · intro S hS
    have : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst this
    refine erasureCorrectable_empty _ ?_
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · have h' : ee i ≠ ee j := fun hc => h (ee.injective hc)
      simp [h, Ne.symm h', Finset.sum_ite_eq', apply_ite (starRingEnd ℂ)]

end QI

