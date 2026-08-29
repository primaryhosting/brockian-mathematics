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
