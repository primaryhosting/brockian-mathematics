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

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/
lemma rank_add_finrank_ker [Fintype X] [Fintype Y] (M : Matrix X Y ℂ) :
    M.rank + Module.finrank ℂ (LinearMap.ker M.mulVecLin) = Fintype.card Y := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℂ) M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- A nonzero matrix has positive rank. -/
lemma one_le_rank_of_ne_zero [Fintype X] [Fintype Y] [DecidableEq Y] {M : Matrix X Y ℂ}
    (hM : M ≠ 0) : 1 ≤ M.rank := by
  by_contra h
  push_neg at h
  have hr : M.rank = 0 := by omega
  have hbot : LinearMap.range M.mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]; exact hr
  rw [LinearMap.range_eq_bot] at hbot
  apply hM
  ext x y
  have h2 : M.mulVecLin (Pi.single y 1) x = 0 := by rw [hbot]; rfl
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply] at h2
  simpa using h2

/-- Rank is invariant under multiplication by a nonzero scalar. -/
lemma rank_smul_of_ne_zero [Fintype X] [Fintype Y] (M : Matrix X Y ℂ) {c : ℂ} (hc : c ≠ 0) :
    (c • M).rank = M.rank := by
  unfold Matrix.rank
  rw [show (c • M).mulVecLin = c • M.mulVecLin from
    LinearMap.CompatibleSMul.map_smul (Matrix.mulVecBilin ℂ ℂ) c M, LinearMap.range_smul _ _ hc]

/-- The rank of `1 ⊗ σ` (a block-scalar matrix) is `card R * rank σ`. -/
lemma rank_blockScalar {R A : Type*} [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    (σ : Matrix A A ℂ) :
    (Matrix.of fun p p' : R × A => (if p.1 = p'.1 then (1 : ℂ) else 0) * σ p.2 p'.2).rank
      = Fintype.card R * σ.rank := by
  classical
  set P : Matrix (R × A) (R × A) ℂ :=
    Matrix.of fun p p' : R × A => (if p.1 = p'.1 then (1 : ℂ) else 0) * σ p.2 p'.2 with hP
  have key : ∀ (v : R × A → ℂ) (r : R) (a : A),
      (P *ᵥ v) (r, a) = (σ *ᵥ (fun a' => v (r, a'))) a := by
    intro v r a
    simp only [Matrix.mulVec, dotProduct, hP, Matrix.of_apply]
    rw [Fintype.sum_prod_type]
    simp
  -- the kernel of `P` is `R` copies of the kernel of `σ`
  have hker : Module.finrank ℂ (LinearMap.ker P.mulVecLin)
      = Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin) := by
    have hmem : ∀ f : R → (LinearMap.ker σ.mulVecLin),
        P.mulVecLin (fun p => (f p.1).1 p.2) = 0 := by
      intro f
      funext p
      obtain ⟨r, a⟩ := p
      have hk : (P *ᵥ (fun p : R × A => (f p.1).1 p.2)) (r, a) = (σ *ᵥ (f r).1) a := key _ r a
      have h1 : σ *ᵥ (f r).1 = 0 := by
        have h2 := (f r).2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
      simp only [Matrix.mulVecLin_apply, hk, h1]
      rfl
    let Φ : (R → (LinearMap.ker σ.mulVecLin)) →ₗ[ℂ] (LinearMap.ker P.mulVecLin) :=
    { toFun := fun f => ⟨fun p => (f p.1).1 p.2, by rw [LinearMap.mem_ker]; exact hmem f⟩
      map_add' := by intros f g; ext p; simp
      map_smul' := by intros c f; ext p; simp }
    have hbij : Function.Bijective Φ := by
      constructor
      · intro f g hfg
        funext r
        apply Subtype.ext
        funext a
        exact congrFun (congrArg Subtype.val hfg) (r, a)
      · rintro ⟨v, hv⟩
        rw [LinearMap.mem_ker] at hv
        refine ⟨fun r => ⟨fun a => v (r, a), ?_⟩, ?_⟩
        · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          funext a
          have hk : (P *ᵥ v) (r, a) = (σ *ᵥ (fun a' => v (r, a'))) a := key v r a
          have h0 : (P *ᵥ v) (r, a) = 0 := by
            have := congrFun hv (r, a); rwa [Matrix.mulVecLin_apply] at this
          rw [← hk, h0]; rfl
        · apply Subtype.ext; funext p; rfl
    have hfr := (LinearEquiv.ofBijective Φ hbij).finrank_eq
    rw [← hfr, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have h1 := rank_add_finrank_ker P
  have h2 := rank_add_finrank_ker σ
  rw [hker, Fintype.card_prod] at h1
  have h3 : P.rank + Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin)
      = Fintype.card R * σ.rank
        + Fintype.card R * Module.finrank ℂ (LinearMap.ker σ.mulVecLin) := by
    rw [h1, ← Nat.mul_add, h2]
  exact Nat.add_right_cancel h3

/-- For a positive semidefinite bipartite matrix `ρ`, a vector killed by the partial trace
`ρX`, tensored with a basis vector of `Y`, is killed by `ρ`. -/
lemma mulVec_slice_eq_zero [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : Matrix (X × Y) (X × Y) ℂ) (hρ : ρ.PosSemidef) (u : X → ℂ)
    (hu : (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)) *ᵥ u = 0) (y0 : Y) :
    ρ *ᵥ (fun p : X × Y => if p.2 = y0 then u p.1 else 0) = 0 := by
  classical
  have hquad : ∀ y : Y, star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
        ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0)
      = ∑ x, ∑ x', (starRingEnd ℂ) (u x) * (ρ (x, y) (x', y) * u x') := by
    intro y
    simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, ite_mul, apply_ite,
      Finset.sum_ite_eq', Finset.mul_sum]
  have htot : star u ⬝ᵥ (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)) *ᵥ u
      = ∑ y, ∑ x, ∑ x', (starRingEnd ℂ) (u x) * (ρ (x, y) (x', y) * u x') := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
      Finset.mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    conv_rhs => rw [Finset.sum_comm]
  have hzero : ∑ y : Y, star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
      ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0) = 0 := by
    rw [Finset.sum_congr rfl (fun y _ => hquad y), ← htot, hu]
    simp
  have hnn : ∀ y ∈ (Finset.univ : Finset Y),
      (0 : ℂ) ≤ star (fun p : X × Y => if p.2 = y then u p.1 else 0) ⬝ᵥ
        ρ *ᵥ (fun p : X × Y => if p.2 = y then u p.1 else 0) :=
    fun y _ => hρ.dotProduct_mulVec_nonneg _
  have hy := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero y0 (Finset.mem_univ _)
  exact (hρ.dotProduct_mulVec_zero_iff _).1 hy

/-- For a positive semidefinite bipartite matrix, the rank is at most the rank of the partial
trace over the second factor, times the dimension of that factor. -/
lemma rank_le_rank_ptrace_mul [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : Matrix (X × Y) (X × Y) ℂ) (hρ : ρ.PosSemidef) :
    ρ.rank ≤ (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)).rank * Fintype.card Y := by
  classical
  set ρX : Matrix X X ℂ := Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y) with hρX
  have hmem : ∀ f : Y → (LinearMap.ker ρX.mulVecLin),
      ρ.mulVecLin (fun p : X × Y => (f p.2).1 p.1) = 0 := by
    intro f
    have hslice : ∀ y : Y, ρ *ᵥ (fun p : X × Y => if p.2 = y then (f y).1 p.1 else 0) = 0 := by
      intro y
      refine mulVec_slice_eq_zero ρ hρ _ ?_ y
      have h2 := (f y).2
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    funext p
    have hsplit : (ρ *ᵥ (fun p : X × Y => (f p.2).1 p.1)) p
        = ∑ y : Y, (ρ *ᵥ (fun p' : X × Y => if p'.2 = y then (f y).1 p'.1 else 0)) p := by
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Finset.sum_comm
    rw [Matrix.mulVecLin_apply, hsplit]
    simp [hslice]
  let Ψ : (Y → (LinearMap.ker ρX.mulVecLin)) →ₗ[ℂ] (LinearMap.ker ρ.mulVecLin) :=
  { toFun := fun f => ⟨fun p => (f p.2).1 p.1, by rw [LinearMap.mem_ker]; exact hmem f⟩
    map_add' := by intros f g; ext p; simp
    map_smul' := by intros c f; ext p; simp }
  have hinj : Function.Injective Ψ := by
    intro f g hfg
    funext y
    apply Subtype.ext
    funext x
    exact congrFun (congrArg Subtype.val hfg) (x, y)
  have hle : Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
      ≤ Module.finrank ℂ (LinearMap.ker ρ.mulVecLin) := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hinj
    rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have h1 := rank_add_finrank_ker ρ
  have h2 := rank_add_finrank_ker ρX
  rw [Fintype.card_prod] at h1
  have h3 : ρ.rank + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
      ≤ Fintype.card Y * ρX.rank
        + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin) := by
    calc ρ.rank + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
        ≤ ρ.rank + Module.finrank ℂ (LinearMap.ker ρ.mulVecLin) := by omega
      _ = Fintype.card X * Fintype.card Y := h1
      _ = Fintype.card Y * (ρX.rank + Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)) := by
            rw [h2]; ring
      _ = _ := by ring
  have h4 := Nat.add_le_add_iff_right.1 h3
  rwa [mul_comm] at h4

end RankLemmas

/-! ## The core bound

Abstract form of the quantum Singleton bound: a `K`-dimensional code inside `A ⊗ B ⊗ C`
for which both the `A`-part and the `C`-part are erasure-correctable satisfies `K ≤ dim B`. -/

theorem core_bound {K : ℕ} {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C]
    (psi : Fin K → A → B → C → ℂ)
    (hne : ∃ i a b c, psi i a b c ≠ 0)
    (σ : Matrix A A ℂ) (τ : Matrix C C ℂ)
    (hA : ∀ i j a a', (∑ b, ∑ c, psi i a b c * conj (psi j a' b c))
      = (if i = j then (1 : ℂ) else 0) * σ a a')
    (hC : ∀ i j c c', (∑ a, ∑ b, psi i a b c * conj (psi j a b c'))
      = (if i = j then (1 : ℂ) else 0) * τ c c') :
    K ≤ Fintype.card B := by
  classical
  obtain ⟨i0, a0, b0, c0, hne0⟩ := hne
  have hKpos : 0 < K := i0.pos
  have hKne : (K : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  set N₁ : Matrix (Fin K × A) (C × B) ℂ := Matrix.of fun p r => psi p.1 p.2 r.2 r.1 with hN₁
  set N₂ : Matrix (Fin K × C) (A × B) ℂ := Matrix.of fun p r => psi p.1 r.1 r.2 p.2 with hN₂
  -- the `RA` marginal is `1 ⊗ σ`
  have e1 : N₁ * N₁ᴴ
      = Matrix.of fun p p' : Fin K × A => (if p.1 = p'.1 then (1 : ℂ) else 0) * σ p.2 p'.2 := by
    ext p p'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hN₁, Matrix.of_apply,
      RCLike.star_def]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact hA p.1 p'.1 p.2 p'.2
  have r1 : N₁.rank = K * σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose N₁, e1, rank_blockScalar, Fintype.card_fin]
  -- the `RC` marginal is `1 ⊗ τ`
  have e2 : N₂ * N₂ᴴ
      = Matrix.of fun p p' : Fin K × C => (if p.1 = p'.1 then (1 : ℂ) else 0) * τ p.2 p'.2 := by
    ext p p'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hN₂, Matrix.of_apply,
      RCLike.star_def]
    rw [Fintype.sum_prod_type]
    exact hC p.1 p'.1 p.2 p'.2
  have r2 : N₂.rank = K * τ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose N₂, e2, rank_blockScalar, Fintype.card_fin]
  -- partial traces of the `BC` and `AB` marginals
  have ptr1 : (Matrix.of fun c c' : C => ∑ b, (N₁ᴴ * N₁) (c, b) (c', b)) = (K : ℂ) • τᵀ := by
    ext c c'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hN₁, Matrix.of_apply,
      RCLike.star_def, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    have hstep : ∀ i : Fin K, (∑ a, ∑ b, conj (psi i a b c) * psi i a b c') = τ c' c := by
      intro i
      have h := hC i i c' c
      rw [if_pos rfl, one_mul] at h
      rw [← h]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have ptr2 : (Matrix.of fun a a' : A => ∑ b, (N₂ᴴ * N₂) (a, b) (a', b)) = (K : ℂ) • σᵀ := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hN₂, Matrix.of_apply,
      RCLike.star_def, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    have hstep : ∀ i : Fin K, (∑ c, ∑ b, conj (psi i a b c) * psi i a' b c) = σ a' a := by
      intro i
      rw [Finset.sum_comm]
      have h := hA i i a' a
      rw [if_pos rfl, one_mul] at h
      rw [← h]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hstep i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the two rank inequalities
  have ineq1 : K * σ.rank ≤ τ.rank * Fintype.card B := by
    have h := rank_le_rank_ptrace_mul (N₁ᴴ * N₁) (Matrix.posSemidef_conjTranspose_mul_self N₁)
    rwa [ptr1, rank_smul_of_ne_zero _ hKne, Matrix.rank_transpose,
      Matrix.rank_conjTranspose_mul_self, r1] at h
  have ineq2 : K * τ.rank ≤ σ.rank * Fintype.card B := by
    have h := rank_le_rank_ptrace_mul (N₂ᴴ * N₂) (Matrix.posSemidef_conjTranspose_mul_self N₂)
    rwa [ptr2, rank_smul_of_ne_zero _ hKne, Matrix.rank_transpose,
      Matrix.rank_conjTranspose_mul_self, r2] at h
  -- both marginals are nonzero
  have hN1ne : N₁ ≠ 0 := by
    intro h0
    exact hne0 (by simpa [hN₁] using congrFun (congrFun h0 (i0, a0)) (c0, b0))
  have hN2ne : N₂ ≠ 0 := by
    intro h0
    exact hne0 (by simpa [hN₂] using congrFun (congrFun h0 (i0, c0)) (a0, b0))
  have hσ : 1 ≤ σ.rank := by
    rcases Nat.eq_zero_or_pos σ.rank with h | h
    · rw [h, Nat.mul_zero] at r1
      have := one_le_rank_of_ne_zero hN1ne
      omega
    · exact h
  have hτ : 1 ≤ τ.rank := by
    rcases Nat.eq_zero_or_pos τ.rank with h | h
    · rw [h, Nat.mul_zero] at r2
      have := one_le_rank_of_ne_zero hN2ne
      omega
    · exact h
  nlinarith [Nat.mul_le_mul ineq1 ineq2]

/-! ## Quantum codes and erasure correction -/

variable {n q K : ℕ}

/-- Glue a configuration on `S` with a configuration on the complement of `S`. -/
def glue (S : Finset (Fin n)) (x : {i : Fin n // i ∈ S} → Fin q)
    (z : {i : Fin n // i ∉ S} → Fin q) : Fin n → Fin q :=
  fun t => if h : t ∈ S then x ⟨t, h⟩ else z ⟨t, h⟩

/-- The Knill–Laflamme erasure-correction condition for the set `S` of qudits:
the partial trace over the complement of `S` of `|ψᵢ⟩⟨ψⱼ|` equals `δᵢⱼ σ` for a fixed
matrix `σ`, i.e. the qudits in `S` carry no information about the encoded state. -/
def Correctable (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (S : Finset (Fin n)) : Prop :=
  ∃ σ : Matrix ({i : Fin n // i ∈ S} → Fin q) ({i : Fin n // i ∈ S} → Fin q) ℂ,
    ∀ (i j : Fin K) (x y : {i : Fin n // i ∈ S} → Fin q),
      (∑ z : {i : Fin n // i ∉ S} → Fin q, V (glue S x z) i * conj (V (glue S y z) j))
        = (if i = j then (1 : ℂ) else 0) * σ x y

/-- Configurations on the complement of the empty set are just configurations. -/
def emptyComplEquiv (n q : ℕ) :
    (Fin n → Fin q) ≃ ({i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q) where
  toFun w t := w t.val
  invFun z i := z ⟨i, by simp⟩
  left_inv := by intro w; funext i; rfl
  right_inv := by intro z; funext t; rfl

/-- Erasing no qudit at all is always correctable for an isometric encoding.  In particular the
erasure conditions in `Correctable` are satisfiable, so the Singleton bound below is not
vacuous. -/
lemma correctable_empty (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (hV : Vᴴ * V = 1) :
    Correctable V (∅ : Finset (Fin n)) := by
  classical
  refine ⟨1, fun i j x y => ?_⟩
  have hglue : ∀ (w : Fin n → Fin q) (u : {i : Fin n // i ∈ (∅ : Finset (Fin n))} → Fin q),
      glue ∅ u (emptyComplEquiv n q w) = w := by
    intro w u
    funext t
    simp [glue, emptyComplEquiv]
  rw [← Equiv.sum_comp (emptyComplEquiv n q) (fun z => V (glue ∅ x z) i * conj (V (glue ∅ y z) j))]
  have hterm : ∀ w : Fin n → Fin q,
      V (glue ∅ x (emptyComplEquiv n q w)) i * conj (V (glue ∅ y (emptyComplEquiv n q w)) j)
      = conj (V w j) * V w i := by
    intro w; rw [hglue w x, hglue w y]; ring
  rw [Finset.sum_congr rfl (fun w _ => hterm w)]
  have h1 : (Vᴴ * V) j i = ∑ w, conj (V w j) * V w i := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [← h1, hV]
  have hxy : x = y := Subsingleton.elim _ _
  by_cases hij : i = j
  · subst hij; simp [Matrix.one_apply, hxy]
  · simp [Matrix.one_apply, hij, Ne.symm hij]

/-- Merge configurations on three disjoint parts (`S1`, the rest, `S2`). -/
def merge3 (S1 S2 : Finset (Fin n)) (a : {i : Fin n // i ∈ S1} → Fin q)
    (b : {i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q) (c : {i : Fin n // i ∈ S2} → Fin q) :
    Fin n → Fin q :=
  fun t => if h1 : t ∈ S1 then a ⟨t, h1⟩ else if h2 : t ∈ S2 then c ⟨t, h2⟩ else b ⟨t, ⟨h1, h2⟩⟩

/-- Configurations on the complement of `S1` split as (middle part) × (`S2` part). -/
def splitB (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S2 → i ∉ S1) :
    (({i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q) × ({i : Fin n // i ∈ S2} → Fin q))
      ≃ ({i : Fin n // i ∉ S1} → Fin q) where
  toFun p := fun t => if h : t.val ∈ S2 then p.2 ⟨t.val, h⟩ else p.1 ⟨t.val, ⟨t.property, h⟩⟩
  invFun z := (fun b => z ⟨b.val, b.property.1⟩, fun c => z ⟨c.val, hdisj c.val c.property⟩)
  left_inv := by
    rintro ⟨b, c⟩
    ext t
    · simp only [t.property.2, dif_neg, not_false_iff]
    · simp only [t.property, dif_pos]
  right_inv := by
    intro z
    funext t
    by_cases h : t.val ∈ S2 <;> simp [h]

/-- Configurations on the complement of `S2` split as (`S1` part) × (middle part). -/
def splitA (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S1 → i ∉ S2) :
    (({i : Fin n // i ∈ S1} → Fin q) × ({i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q))
      ≃ ({i : Fin n // i ∉ S2} → Fin q) where
  toFun p := fun t => if h : t.val ∈ S1 then p.1 ⟨t.val, h⟩ else p.2 ⟨t.val, ⟨h, t.property⟩⟩
  invFun z := (fun a => z ⟨a.val, hdisj a.val a.property⟩, fun b => z ⟨b.val, b.property.2⟩)
  left_inv := by
    rintro ⟨a, b⟩
    ext t
    · simp only [t.property, dif_pos]
    · simp only [t.property.1, dif_neg, not_false_iff]
  right_inv := by
    intro z
    funext t
    by_cases h : t.val ∈ S1 <;> simp [h]

lemma glue_splitB (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S2 → i ∉ S1)
    (a : {i : Fin n // i ∈ S1} → Fin q) (b : {i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q)
    (c : {i : Fin n // i ∈ S2} → Fin q) :
    glue S1 a (splitB S1 S2 hdisj (b, c)) = merge3 S1 S2 a b c := by
  funext t
  by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [glue, merge3, splitB, h1, h2]

lemma glue_splitA (S1 S2 : Finset (Fin n)) (hdisj : ∀ i, i ∈ S1 → i ∉ S2)
    (a : {i : Fin n // i ∈ S1} → Fin q) (b : {i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q)
    (c : {i : Fin n // i ∈ S2} → Fin q) :
    glue S2 c (splitA S1 S2 hdisj (a, b)) = merge3 S1 S2 a b c := by
  funext t
  by_cases h1 : t ∈ S1 <;> by_cases h2 : t ∈ S2 <;> simp [glue, merge3, splitA, h1, h2]
  · exact absurd h2 (hdisj t h1)

/-! ## The quantum Singleton bound -/

/-- **Quantum Singleton bound.**  Let `V` be an isometric encoding of a `K = q ^ k`-dimensional
code into `n` qudits of local dimension `q ≥ 2`, and suppose the code has distance `d ≥ 1`,
i.e. the erasure of any set of at most `d - 1` qudits is correctable (Knill–Laflamme condition).
Then `n - k ≥ 2 (d - 1)`, stated in the subtraction-free form `2 * (d - 1) + k ≤ n`.

The hypothesis `1 ≤ k` is genuinely needed: a one-dimensional "code" (`k = 0`) trivially
satisfies the erasure conditions for every set of qudits. -/
theorem quantum_singleton {q n k d K : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hd1 : 1 ≤ d)
    (hK : K = q ^ k) (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (hV : Vᴴ * V = 1)
    (hdist : ∀ S : Finset (Fin n), S.card < d → Correctable V S) :
    2 * (d - 1) + k ≤ n := by
  classical
  set m := d - 1 with hm
  set S1 : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < m) with hS1
  set S2 : Finset (Fin n) :=
    Finset.univ.filter (fun i : Fin n => m ≤ (i : ℕ) ∧ (i : ℕ) < 2 * m) with hS2
  have hmemS1 : ∀ i : Fin n, i ∈ S1 ↔ (i : ℕ) < m := by intro i; simp [hS1]
  have hmemS2 : ∀ i : Fin n, i ∈ S2 ↔ (m ≤ (i : ℕ) ∧ (i : ℕ) < 2 * m) := by intro i; simp [hS2]
  have hdisj12 : ∀ i : Fin n, i ∈ S1 → i ∉ S2 := by
    intro i h1 h2
    rw [hmemS1] at h1
    rw [hmemS2] at h2
    omega
  have hdisj21 : ∀ i : Fin n, i ∈ S2 → i ∉ S1 := by
    intro i h2 h1
    exact hdisj12 i h1 h2
  -- both erased sets have at most `d - 1` elements
  have hcard1 : S1.card < d := by
    have : Fintype.card {i : Fin n // i ∈ S1} ≤ Fintype.card (Fin m) := by
      refine Fintype.card_le_of_injective
        (fun t : {i : Fin n // i ∈ S1} =>
          (⟨t.val.val, by have := (hmemS1 t.val).1 t.property; omega⟩ : Fin m)) ?_
      intro t1 t2 h
      apply Subtype.ext
      apply Fin.ext
      simpa using congrArg Fin.val h
    rw [Fintype.card_coe, Fintype.card_fin] at this
    omega
  have hcard2 : S2.card < d := by
    have : Fintype.card {i : Fin n // i ∈ S2} ≤ Fintype.card (Fin m) := by
      refine Fintype.card_le_of_injective
        (fun t : {i : Fin n // i ∈ S2} =>
          (⟨t.val.val - m, by have := (hmemS2 t.val).1 t.property; omega⟩ : Fin m)) ?_
      intro t1 t2 h
      have h1 := (hmemS2 t1.val).1 t1.property
      have h2 := (hmemS2 t2.val).1 t2.property
      apply Subtype.ext
      apply Fin.ext
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [Fintype.card_coe, Fintype.card_fin] at this
    omega
  obtain ⟨sigma, hsigma⟩ := hdist S1 hcard1
  obtain ⟨tau, htau⟩ := hdist S2 hcard2
  -- the code vectors, split along the three parts
  set psi : Fin K → ({i : Fin n // i ∈ S1} → Fin q) → ({i : Fin n // i ∉ S1 ∧ i ∉ S2} → Fin q) →
      ({i : Fin n // i ∈ S2} → Fin q) → ℂ :=
    fun i a b c => V (merge3 S1 S2 a b c) i with hpsi
  have hAcond : ∀ (i j : Fin K) (a a' : {i : Fin n // i ∈ S1} → Fin q),
      (∑ b, ∑ c, psi i a b c * conj (psi j a' b c))
        = (if i = j then (1 : ℂ) else 0) * sigma a a' := by
    intro i j a a'
    rw [← hsigma i j a a', ← Equiv.sum_comp (splitB S1 S2 hdisj21)
      (fun z => V (glue S1 a z) i * conj (V (glue S1 a' z) j)), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [glue_splitB, glue_splitB]
  have hCcond : ∀ (i j : Fin K) (c c' : {i : Fin n // i ∈ S2} → Fin q),
      (∑ a, ∑ b, psi i a b c * conj (psi j a b c'))
        = (if i = j then (1 : ℂ) else 0) * tau c c' := by
    intro i j c c'
    rw [← htau i j c c', ← Equiv.sum_comp (splitA S1 S2 hdisj12)
      (fun z => V (glue S2 c z) i * conj (V (glue S2 c' z) j)), Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [glue_splitA, glue_splitA]
  -- the encoding is nonzero
  have hqpos : 0 < q := by omega
  have hKpos : 0 < K := by rw [hK]; exact Nat.pow_pos hqpos
  have hne : ∃ i a b c, psi i a b c ≠ 0 := by
    have hex : ∃ x : Fin n → Fin q, V x ⟨0, hKpos⟩ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      have h1 : (Vᴴ * V) ⟨0, hKpos⟩ ⟨0, hKpos⟩ = 1 := by rw [hV]; simp
      rw [Matrix.mul_apply] at h1
      simp [Matrix.conjTranspose_apply, hcon] at h1
    obtain ⟨x, hx⟩ := hex
    refine ⟨⟨0, hKpos⟩, fun t => x t.val, fun t => x t.val, fun t => x t.val, ?_⟩
    have hmg : merge3 S1 S2 (fun t : {i : Fin n // i ∈ S1} => x t.val)
        (fun t : {i : Fin n // i ∉ S1 ∧ i ∉ S2} => x t.val)
        (fun t : {i : Fin n // i ∈ S2} => x t.val) = x := by
      funext t
      simp only [merge3]
      split_ifs <;> rfl
    rw [hpsi]
    simpa [hmg] using hx
  -- the core bound
  have hbound := core_bound psi hne sigma tau hAcond hCcond
  rw [Fintype.card_fun, Fintype.card_fin] at hbound
  -- counting the untouched qudits
  have hcardB : Fintype.card {i : Fin n // i ∉ S1 ∧ i ∉ S2} ≤ n - 2 * m := by
    rw [← Fintype.card_fin (n - 2 * m)]
    refine Fintype.card_le_of_injective
      (fun t : {i : Fin n // i ∉ S1 ∧ i ∉ S2} => (⟨t.val.val - 2 * m, ?_⟩ : Fin (n - 2 * m))) ?_
    · have h1 : ¬((t.val : ℕ) < m) := by
        intro h; exact t.property.1 ((hmemS1 t.val).2 h)
      have h2 : ¬(m ≤ (t.val : ℕ) ∧ (t.val : ℕ) < 2 * m) := by
        intro h; exact t.property.2 ((hmemS2 t.val).2 h)
      have h3 := t.val.isLt
      omega
    · intro t1 t2 h
      have ha1 : ¬((t1.val : ℕ) < m) := fun hlt => t1.property.1 ((hmemS1 t1.val).2 hlt)
      have ha2 : ¬(m ≤ (t1.val : ℕ) ∧ (t1.val : ℕ) < 2 * m) := fun hlt =>
        t1.property.2 ((hmemS2 t1.val).2 hlt)
      have hb1 : ¬((t2.val : ℕ) < m) := fun hlt => t2.property.1 ((hmemS1 t2.val).2 hlt)
      have hb2 : ¬(m ≤ (t2.val : ℕ) ∧ (t2.val : ℕ) < 2 * m) := fun hlt =>
        t2.property.2 ((hmemS2 t2.val).2 hlt)
      apply Subtype.ext
      apply Fin.ext
      have := congrArg Fin.val h
      simp only at this
      omega
  have hqk : q ^ k ≤ q ^ (n - 2 * m) := by
    calc q ^ k = K := hK.symm
      _ ≤ q ^ Fintype.card {i : Fin n // i ∉ S1 ∧ i ∉ S2} := hbound
      _ ≤ q ^ (n - 2 * m) := Nat.pow_le_pow_right (by omega) hcardB
  have hkle : k ≤ n - 2 * m := (Nat.pow_le_pow_iff_right (by omega)).1 hqk
  omega

/-- The quantum Singleton bound in the literal form `n - k ≥ 2 (d - 1)`. -/
theorem quantum_singleton_sub {q n k d K : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hd1 : 1 ≤ d)
    (hK : K = q ^ k) (V : Matrix (Fin n → Fin q) (Fin K) ℂ) (hV : Vᴴ * V = 1)
    (hdist : ∀ S : Finset (Fin n), S.card < d → Correctable V S) :
    2 * (d - 1) ≤ n - k := by
  have h := quantum_singleton hq hk hd1 hK V hV hdist
  omega

end QI

import Mathlib

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
set_option pp.piBinderTypes true

set_option grind.warning false

