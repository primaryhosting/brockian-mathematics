/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Statement: Quantum Singleton bound: an [[n,k,d]] code obeys n−k ≥ 2(d−1).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Kronecker ComplexOrder
open Matrix Module

namespace QI

section LinearAlgebra

variable {X W : Type*} [Fintype X] [Fintype W] [DecidableEq X] [DecidableEq W]

/-- Rank factorization: every matrix `F` factors as `U * L * F = F` with `U` having
`F.rank` columns. -/
lemma exists_rank_factor (F : Matrix X W ℂ) :
    ∃ (U : Matrix X (Fin F.rank) ℂ) (L : Matrix (Fin F.rank) X ℂ), U * L * F = F := by
  classical
  set V := LinearMap.range F.mulVecLin with hVdef
  have hfin : finrank ℂ V = F.rank := rfl
  let bs : Basis (Fin F.rank) ℂ V := Module.finBasisOfFinrankEq ℂ V hfin
  choose g hg using fun s : Fin F.rank => LinearMap.exists_extend (bs.coord s)
  refine ⟨Matrix.of fun x s => (bs s : X → ℂ) x, Matrix.of fun s x => g s (Pi.single x 1), ?_⟩
  have hgv : ∀ (s : Fin F.rank) (v : X → ℂ), ∑ x', g s (Pi.single x' 1) * v x' = g s v := by
    intro s v
    have step : ∀ x' : X, g s (Pi.single x' 1) * v x' = g s (Pi.single x' (v x')) := by
      intro x'
      have hs : (Pi.single x' (v x') : X → ℂ) = v x' • (Pi.single x' 1 : X → ℂ) := by
        funext y; by_cases h : y = x' <;> simp [Pi.single_apply, h]
      rw [hs, map_smul, smul_eq_mul, mul_comm]
    simp_rw [step]
    rw [← map_sum, Finset.univ_sum_single]
  have hkey : ∀ v : X → ℂ, v ∈ V → ∀ x, ∑ s, (bs s : X → ℂ) x * g s v = v x := by
    intro v hv x
    have h1 : ∀ s, g s v = bs.repr ⟨v, hv⟩ s := by
      intro s
      have := congrArg (fun (m : V →ₗ[ℂ] ℂ) => m ⟨v, hv⟩) (hg s)
      simpa [Basis.coord_apply] using this
    have h3 := congrArg (fun (w : V) => (w : X → ℂ) x) (bs.sum_repr ⟨v, hv⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h3
    simp_rw [h1]
    rw [← h3]
    exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  ext x w
  have hmem : (fun x' => F x' w) ∈ V := by
    refine ⟨Pi.single w 1, ?_⟩
    funext x'
    simp [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.of_apply]
  calc ∑ s, (bs s : X → ℂ) x * ∑ x', g s (Pi.single x' 1) * F x' w
      = ∑ s, (bs s : X → ℂ) x * g s (fun x' => F x' w) :=
        Finset.sum_congr rfl fun s _ => by rw [hgv s fun x' => F x' w]
    _ = F x w := hkey _ hmem x

/-- Rank subadditivity for tensor flattenings: the rank of the `(X × Y) | Z` flattening of a
three-index array is at most the product of the ranks of the `X | (Y × Z)` and `Y | (X × Z)`
flattenings. -/
lemma rank_flatten_le {Y Z : Type*} [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z]
    (f : X → Y → Z → ℂ) :
    (Matrix.of fun (p : X × Y) (z : Z) => f p.1 p.2 z).rank ≤
      (Matrix.of fun (x : X) (p : Y × Z) => f x p.1 p.2).rank *
        (Matrix.of fun (y : Y) (p : X × Z) => f p.1 y p.2).rank := by
  classical
  set FX := Matrix.of fun (x : X) (p : Y × Z) => f x p.1 p.2 with hFX
  set FY := Matrix.of fun (y : Y) (p : X × Z) => f p.1 y p.2 with hFY
  set G := Matrix.of fun (p : X × Y) (z : Z) => f p.1 p.2 z with hG
  obtain ⟨UX, LX, hX⟩ := exists_rank_factor FX
  obtain ⟨UY, LY, hY⟩ := exists_rank_factor FY
  rw [Matrix.mul_assoc] at hX hY
  have hXe : ∀ x y z, ∑ x', (UX * LX) x x' * f x' y z = f x y z := by
    intro x y z
    have h := congrFun (congrFun hX x) (y, z)
    simp only [Matrix.mul_apply, hFX, Matrix.of_apply] at h ⊢
    rw [← h]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hYe : ∀ x y z, ∑ y', (UY * LY) y y' * f x y' z = f x y z := by
    intro x y z
    have h := congrFun (congrFun hY y) (x, z)
    simp only [Matrix.mul_apply, hFY, Matrix.of_apply] at h ⊢
    rw [← h]
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hPG : ((UX * LX) ⊗ₖ (UY * LY)) * G = G := by
    ext p z
    obtain ⟨x, y⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have key : ∀ x', ∑ y', ((UX * LX) ⊗ₖ (UY * LY)) (x, y) (x', y') * G (x', y') z
        = (UX * LX) x x' * f x' y z := by
      intro x'
      have inner : ∀ y', ((UX * LX) ⊗ₖ (UY * LY)) (x, y) (x', y') * G (x', y') z
          = (UX * LX) x x' * ((UY * LY) y y' * f x' y' z) := by
        intro y'
        simp only [Matrix.kroneckerMap_apply, hG, Matrix.of_apply]
        ring
      rw [Finset.sum_congr rfl fun y' _ => inner y', ← Finset.mul_sum, hYe]
    rw [Finset.sum_congr rfl fun x' _ => key x', hXe]
    rfl
  have hfactor : G = (UX ⊗ₖ UY) * ((LX ⊗ₖ LY) * G) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, hPG]
  calc G.rank = ((UX ⊗ₖ UY) * ((LX ⊗ₖ LY) * G)).rank := by rw [← hfactor]
    _ ≤ (UX ⊗ₖ UY).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin FX.rank × Fin FY.rank) := Matrix.rank_le_card_width _
    _ = FX.rank * FY.rank := by simp

/-- The dimension of a product of copies of a fixed submodule. -/
lemma finrank_pi_submodule {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (p : Submodule ℂ M) [FiniteDimensional ℂ p] :
    finrank ℂ (Submodule.pi (Set.univ : Set ι) (fun _ => p)) = Fintype.card ι * finrank ℂ p := by
  have e : (Submodule.pi (Set.univ : Set ι) (fun _ : ι => p)) ≃ₗ[ℂ] (ι → p) :=
    { toFun := fun v i => ⟨v.1 i, v.2 i (Set.mem_univ i)⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl
      invFun := fun w => ⟨fun i => (w i : M), fun i _ => (w i).2⟩
      left_inv := fun v => rfl
      right_inv := fun w => rfl }
  rw [e.finrank_eq, finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul]

omit [DecidableEq X] in
/-- The rank of `1 ⊗ ρ` is `K * rank ρ`. -/
lemma rank_one_kronecker {K : ℕ} (ρ : Matrix X X ℂ) :
    ((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ).rank = K * ρ.rank := by
  have key : Submodule.map (LinearEquiv.curry ℂ ℂ (Fin K) X).toLinearMap
      (LinearMap.range ((1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ).mulVecLin)
      = Submodule.pi Set.univ (fun _ : Fin K => LinearMap.range ρ.mulVecLin) := by
    apply le_antisymm
    · rintro w ⟨v, ⟨u, rfl⟩, rfl⟩
      intro i _
      refine ⟨fun y => u (i, y), ?_⟩
      funext x
      simp [LinearEquiv.curry, Matrix.mulVecLin, Matrix.mulVec, dotProduct, Matrix.kroneckerMap,
        Fintype.sum_prod_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
    · intro w hw
      choose u hu using fun i => hw i (Set.mem_univ i)
      refine ⟨_, ⟨fun p => u p.1 p.2, rfl⟩, ?_⟩
      funext i x
      have h2 := congrFun (hu i) x
      simp only [Matrix.mulVecLin_apply] at h2 ⊢
      simp [LinearEquiv.curry, Matrix.mulVec, dotProduct, Matrix.kroneckerMap,
        Fintype.sum_prod_type, Matrix.one_apply, ite_mul, Finset.sum_ite_eq] at h2 ⊢
      exact h2
  rw [Matrix.rank, ← (LinearEquiv.curry ℂ ℂ (Fin K) X).finrank_map_eq, key,
    finrank_pi_submodule, Fintype.card_fin, Matrix.rank]

/-- A nonzero matrix has rank at least one. -/
lemma one_le_rank_of_ne_zero (ρ : Matrix X X ℂ) (h : ρ ≠ 0) : 1 ≤ ρ.rank := by
  by_contra hc
  have h0 : ρ.rank = 0 := by omega
  have hb : LinearMap.range ρ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  apply h
  ext a a'
  have hmem : ρ.mulVecLin (Pi.single a' 1) ∈ LinearMap.range ρ.mulVecLin := ⟨_, rfl⟩
  rw [hb, Submodule.mem_bot] at hmem
  have := congrFun hmem a
  simpa [Matrix.mulVecLin, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using this

lemma rank_smul_of_ne_zero {c : ℂ} (hc : c ≠ 0) (ρ : Matrix X X ℂ) :
    (c • ρ).rank = ρ.rank := by
  have h1 : (c • ρ) = (c • (1 : Matrix X X ℂ)) * ρ := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [h1]
  refine Matrix.rank_mul_eq_right_of_isUnit_det _ _ ?_
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  exact (isUnit_iff_ne_zero).2 (pow_ne_zero _ hc)

end LinearAlgebra

section Core

/-- Reindexing equivalence used to compare flattenings of a three-index array. -/
def swapEquiv (S T U : Type*) : S × (T × U) ≃ T × U × S :=
  ⟨fun p => (p.2.1, p.2.2, p.1), fun p => (p.2.2, p.1, p.2.1), fun _ => rfl, fun _ => rfl⟩

/-- Reindexing equivalence used to compare flattenings of a three-index array. -/
def shuffleEquiv (S T U : Type*) : S × (T × U) ≃ T × S × U :=
  ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2), fun _ => rfl, fun _ => rfl⟩

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- Core linear-algebraic form of the quantum Singleton bound.  If `ψ` is a family of `K`
vectors in `α ⊗ β ⊗ γ` satisfying the Knill–Laflamme conditions for the registers `α` and `β`
(the reduced "density matrices" on `α` and on `β` are the same for all codewords and have no
cross terms), then `K ≤ card γ`. -/
theorem core_bound {K : ℕ} (ψ : Fin K → α × β × γ → ℂ) (ρ : Matrix α α ℂ) (σ : Matrix β β ℂ)
    (hA : ∀ i j a a', ∑ b : β, ∑ c : γ, ψ i (a, b, c) * (starRingEnd ℂ) (ψ j (a', b, c))
        = (if i = j then (1 : ℂ) else 0) * ρ a a')
    (hB : ∀ i j b b', ∑ a : α, ∑ c : γ, ψ i (a, b, c) * (starRingEnd ℂ) (ψ j (a, b', c))
        = (if i = j then (1 : ℂ) else 0) * σ b b')
    (hne : ∃ i v, ψ i v ≠ 0) :
    K ≤ Fintype.card γ := by
  classical
  obtain ⟨i0, ⟨a0, b0, c0⟩, hv0⟩ := hne
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · exact absurd i0.isLt (by omega)
    · exact h
  have hKC : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  -- the reduced operators are nonzero
  have hnorm : ∀ (i : Fin K) (a : α), ∀ b c, ρ a a = 0 → ψ i (a, b, c) = 0 := by
    intro i a b c hρ0
    have hd := hA i i a a
    rw [if_pos rfl, one_mul, hρ0] at hd
    have hsum : ∑ b' : β, ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) = 0 := by
      have hC : ((∑ b' : β, ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) : ℝ) : ℂ) = 0 := by
        push_cast
        simp_rw [← Complex.mul_conj]
        rw [hd]
      exact_mod_cast hC
    have hnn : ∀ b' ∈ Finset.univ, (0 : ℝ) ≤ ∑ c' : γ, Complex.normSq (ψ i (a, b', c')) :=
        fun b' _ => Finset.sum_nonneg fun c' _ => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum b (Finset.mem_univ b)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c' _ => Complex.normSq_nonneg (ψ i (a, b, c')))).mp h1 c (Finset.mem_univ c)
    simpa [Complex.normSq_eq_zero] using h2
  have hρ : ρ ≠ 0 := by
    intro hρ0
    exact hv0 (hnorm i0 a0 b0 c0 (by rw [hρ0]; rfl))
  have hnormB : ∀ (i : Fin K) (b : β), ∀ a c, σ b b = 0 → ψ i (a, b, c) = 0 := by
    intro i b a c hσ0
    have hd := hB i i b b
    rw [if_pos rfl, one_mul, hσ0] at hd
    have hsum : ∑ a' : α, ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) = 0 := by
      have hC : ((∑ a' : α, ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) : ℝ) : ℂ) = 0 := by
        push_cast
        simp_rw [← Complex.mul_conj]
        rw [hd]
      exact_mod_cast hC
    have hnn : ∀ a' ∈ Finset.univ, (0 : ℝ) ≤ ∑ c' : γ, Complex.normSq (ψ i (a', b, c')) :=
      fun a' _ => Finset.sum_nonneg fun c' _ => Complex.normSq_nonneg _
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum a (Finset.mem_univ a)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun c' _ => Complex.normSq_nonneg (ψ i (a, b, c')))).mp h1 c (Finset.mem_univ c)
    simpa [Complex.normSq_eq_zero] using h2
  have hσ : σ ≠ 0 := by
    intro hσ0
    exact hv0 (hnormB i0 b0 a0 c0 (by rw [hσ0]; rfl))
  -- the various flattenings of the code
  set M : Matrix (Fin K × α) (β × γ) ℂ := Matrix.of fun p r => ψ p.1 (p.2, r.1, r.2) with hM
  set N : Matrix (Fin K × β) (α × γ) ℂ := Matrix.of fun p r => ψ p.1 (r.1, p.2, r.2) with hN
  set FA : Matrix α (Fin K × β × γ) ℂ := Matrix.of fun a r => ψ r.1 (a, r.2.1, r.2.2) with hFA
  set FB : Matrix β (Fin K × α × γ) ℂ := Matrix.of fun b r => ψ r.1 (r.2.1, b, r.2.2) with hFB
  set FC : Matrix γ (Fin K × α × β) ℂ := Matrix.of fun c r => ψ r.1 (r.2.1, r.2.2, c) with hFC
  have hMM : M * Mᴴ = (1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ ρ := by
    ext p p'
    obtain ⟨i, a⟩ := p; obtain ⟨j, a'⟩ := p'
    simp only [hM, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def]
    rw [hA i j a a']
  have hNN : N * Nᴴ = (1 : Matrix (Fin K) (Fin K) ℂ) ⊗ₖ σ := by
    ext p p'
    obtain ⟨i, b⟩ := p; obtain ⟨j, b'⟩ := p'
    simp only [hN, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, RCLike.star_def]
    rw [hB i j b b']
  have hFAA : FA * FAᴴ = (K : ℂ) • ρ := by
    ext a a'
    simp only [hFA, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, RCLike.star_def]
    rw [Finset.sum_congr rfl fun i _ => hA i i a a']
    simp
  have hFBB : FB * FBᴴ = (K : ℂ) • σ := by
    ext b b'
    simp only [hFB, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type, RCLike.star_def]
    rw [Finset.sum_congr rfl fun i _ => hB i i b b']
    simp
  have hrM : M.rank = K * ρ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose M, hMM, rank_one_kronecker]
  have hrN : N.rank = K * σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose N, hNN, rank_one_kronecker]
  have hrFA : FA.rank = ρ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose FA, hFAA, rank_smul_of_ne_zero hKC]
  have hrFB : FB.rank = σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose FB, hFBB, rank_smul_of_ne_zero hKC]
  -- rank subadditivity applied to the two bipartitions
  have flat1 := rank_flatten_le (fun (b : β) (c : γ) (p : Fin K × α) => ψ p.1 (p.2, b, c))
  have flat2 := rank_flatten_le (fun (a : α) (c : γ) (p : Fin K × β) => ψ p.1 (a, p.2, c))
  have e1 : (Matrix.of fun (p : β × γ) (z : Fin K × α) => ψ z.1 (z.2, p.1, p.2)) = Mᵀ := by
    rw [hM]; rfl
  have e2 : (Matrix.of fun (b : β) (p : γ × (Fin K × α)) => ψ p.2.1 (p.2.2, b, p.1))
      = FB.submatrix ⇑(Equiv.refl β) ⇑(swapEquiv γ (Fin K) α) := by rw [hFB]; rfl
  have e3 : (Matrix.of fun (c : γ) (p : β × (Fin K × α)) => ψ p.2.1 (p.2.2, p.1, c))
      = FC.submatrix ⇑(Equiv.refl γ) ⇑(swapEquiv β (Fin K) α) := by rw [hFC]; rfl
  have e4 : (Matrix.of fun (p : α × γ) (z : Fin K × β) => ψ z.1 (p.1, z.2, p.2)) = Nᵀ := by
    rw [hN]; rfl
  have e5 : (Matrix.of fun (a : α) (p : γ × (Fin K × β)) => ψ p.2.1 (a, p.2.2, p.1))
      = FA.submatrix ⇑(Equiv.refl α) ⇑(swapEquiv γ (Fin K) β) := by rw [hFA]; rfl
  have e6 : (Matrix.of fun (c : γ) (p : α × (Fin K × β)) => ψ p.2.1 (p.1, p.2.2, c))
      = FC.submatrix ⇑(Equiv.refl γ) ⇑(shuffleEquiv α (Fin K) β) := by rw [hFC]; rfl
  rw [e1, e2, e3, Matrix.rank_transpose, Matrix.rank_submatrix, Matrix.rank_submatrix,
    hrM, hrFB] at flat1
  rw [e4, e5, e6, Matrix.rank_transpose, Matrix.rank_submatrix, Matrix.rank_submatrix,
    hrN, hrFA] at flat2
  have ha : 1 ≤ ρ.rank := one_le_rank_of_ne_zero ρ hρ
  have hb : 1 ≤ σ.rank := one_le_rank_of_ne_zero σ hσ
  have hsq : (K * K) * (ρ.rank * σ.rank) ≤ (FC.rank * FC.rank) * (ρ.rank * σ.rank) := by
    calc (K * K) * (ρ.rank * σ.rank) = (K * ρ.rank) * (K * σ.rank) := by ring
      _ ≤ (σ.rank * FC.rank) * (ρ.rank * FC.rank) := Nat.mul_le_mul flat1 flat2
      _ = (FC.rank * FC.rank) * (ρ.rank * σ.rank) := by ring
  have hKK : K * K ≤ FC.rank * FC.rank :=
    Nat.le_of_mul_le_mul_right hsq (Nat.mul_pos ha hb)
  have hKc : K ≤ FC.rank := by nlinarith
  exact hKc.trans (Matrix.rank_le_card_height FC)

end Core

section Code

variable {n q : ℕ}

/-- Glue a configuration on `S` and a configuration on the complement of `S` into a global
configuration of `n` qudits. -/
def merge (S : Finset (Fin n)) (x : {i // i ∈ S} → Fin q) (z : {i // i ∉ S} → Fin q) :
    Fin n → Fin q :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else z ⟨i, h⟩

/-- `IsQECC n q d K ψ` says that the `K` orthonormal vectors `ψ` span a `K`-dimensional
quantum code on `n` qudits of local dimension `q` with (minimum) distance at least `d`:
the Knill–Laflamme error-correction conditions hold for every set `S` of at most `d - 1`
erased qudits, i.e. the partial trace of `|ψ i⟩⟨ψ j|` over the complement of `S`
equals `δ i j • ρ` for a fixed operator `ρ` on `S`. -/
def IsQECC (n q d K : ℕ) (ψ : Fin K → ((Fin n → Fin q) → ℂ)) : Prop :=
  (∀ i j, ∑ v : Fin n → Fin q, ψ i v * (starRingEnd ℂ) (ψ j v) = if i = j then 1 else 0) ∧
  (∀ S : Finset (Fin n), S.card + 1 ≤ d →
    ∃ ρ : ({i // i ∈ S} → Fin q) → ({i // i ∈ S} → Fin q) → ℂ,
      ∀ i j x y, ∑ z : {i // i ∉ S} → Fin q,
          ψ i (merge S x z) * (starRingEnd ℂ) (ψ j (merge S y z))
        = (if i = j then (1 : ℂ) else 0) * ρ x y)

/-- Configurations on the complement of `∅` are exactly global configurations. -/
def emptyEquiv : ({i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q) ≃ (Fin n → Fin q) where
  toFun z := fun i => z ⟨i, by simp⟩
  invFun v := fun j => v j
  left_inv z := rfl
  right_inv v := rfl

/-- Sanity check: the hypotheses of the quantum Singleton bound are satisfiable.  The whole
space of `n` qudits, with the standard basis as codewords, is a code of distance at least `1`
with `q ^ n` codewords. -/
theorem exists_isQECC : ∃ ψ : Fin (q ^ n) → ((Fin n → Fin q) → ℂ), IsQECC n q 1 (q ^ n) ψ := by
  classical
  have hcard : Fintype.card (Fin n → Fin q) = q ^ n := by simp
  set e : Fin (q ^ n) ≃ (Fin n → Fin q) := (Fintype.equivFinOfCardEq hcard).symm with he
  have key : ∀ i j : Fin (q ^ n), ∑ v : Fin n → Fin q,
      (if v = e i then (1 : ℂ) else 0) * (starRingEnd ℂ) (if v = e j then 1 else 0)
        = if i = j then 1 else 0 := by
    intro i j
    simp [apply_ite (starRingEnd ℂ), mul_ite, Finset.sum_ite_eq', e.injective.eq_iff, eq_comm]
  refine ⟨fun i v => if v = e i then 1 else 0, key, ?_⟩
  intro S hS
  have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hS0
  refine ⟨fun _ _ => 1, ?_⟩
  intro i j x y
  have hm : ∀ (x : {i // i ∈ (∅ : Finset (Fin n))} → Fin q)
      (z : {i : Fin n // i ∉ (∅ : Finset (Fin n))} → Fin q),
      merge ∅ x z = emptyEquiv z := by
    intro x z; funext i; simp [merge, emptyEquiv]
  simp only [hm, mul_one]
  rw [Equiv.sum_comp emptyEquiv
    (fun v => (if v = e i then (1 : ℂ) else 0) * (starRingEnd ℂ) (if v = e j then 1 else 0))]
  exact key i j

/-- Glue configurations on `A`, on `B` and on the rest into a global configuration. -/
def merge3 (A B : Finset (Fin n)) (a : {i // i ∈ A} → Fin q) (b : {i // i ∈ B} → Fin q)
    (c : {i : Fin n // i ∉ A ∧ i ∉ B} → Fin q) : Fin n → Fin q :=
  fun i => if h : i ∈ A then a ⟨i, h⟩ else if h' : i ∈ B then b ⟨i, h'⟩ else c ⟨i, ⟨h, h'⟩⟩

/-- Splitting the complement of `A` into `B` and the remaining qudits. -/
def eA (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    (({i // i ∈ B} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)) ≃
      ({i : Fin n // i ∉ A} → Fin q) where
  toFun p := fun i => if h : (i : Fin n) ∈ B then p.1 ⟨i, h⟩ else p.2 ⟨i, ⟨i.2, h⟩⟩
  invFun z := (fun j => z ⟨j, Finset.disjoint_right.mp hAB j.2⟩, fun j => z ⟨j, j.2.1⟩)
  left_inv := by
    rintro ⟨b, c⟩
    ext j
    · simp
    · simp [j.2.2]
  right_inv := by
    intro z
    funext i
    by_cases h : (i : Fin n) ∈ B <;> simp [h]

/-- Splitting the complement of `B` into `A` and the remaining qudits. -/
def eB (A B : Finset (Fin n)) (hAB : Disjoint A B) :
    (({i // i ∈ A} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)) ≃
      ({i : Fin n // i ∉ B} → Fin q) where
  toFun p := fun i => if h : (i : Fin n) ∈ A then p.1 ⟨i, h⟩ else p.2 ⟨i, ⟨h, i.2⟩⟩
  invFun z := (fun j => z ⟨j, Finset.disjoint_left.mp hAB j.2⟩, fun j => z ⟨j, j.2.2⟩)
  left_inv := by
    rintro ⟨a, c⟩
    ext j
    · simp
    · simp [j.2.1]
  right_inv := by
    intro z
    funext i
    by_cases h : (i : Fin n) ∈ A <;> simp [h]

lemma merge_eA (A B : Finset (Fin n)) (hAB : Disjoint A B) (a : {i // i ∈ A} → Fin q)
    (b : {i // i ∈ B} → Fin q) (c : {i : Fin n // i ∉ A ∧ i ∉ B} → Fin q) :
    merge A a (eA A B hAB (b, c)) = merge3 A B a b c := by
  funext i
  by_cases h : i ∈ A
  · simp [merge, merge3, h]
  · by_cases h' : i ∈ B <;> simp [merge, merge3, eA, h, h']

lemma merge_eB (A B : Finset (Fin n)) (hAB : Disjoint A B) (a : {i // i ∈ A} → Fin q)
    (b : {i // i ∈ B} → Fin q) (c : {i : Fin n // i ∉ A ∧ i ∉ B} → Fin q) :
    merge B b (eB A B hAB (a, c)) = merge3 A B a b c := by
  funext i
  by_cases h' : i ∈ B
  · have h : i ∉ A := Finset.disjoint_right.mp hAB h'
    simp [merge, merge3, h, h']
  · by_cases h : i ∈ A <;> simp [merge, merge3, eB, h, h']

/-- Erasing two disjoint correctable sets of qudits: the dimension of the code is at most
`q ^ (number of remaining qudits)`. -/
theorem card_le_of_disjoint_erasures {d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)}
    (h : IsQECC n q d K ψ) (hK : 1 ≤ K) (A B : Finset (Fin n)) (hAB : Disjoint A B)
    (hA : A.card + 1 ≤ d) (hB : B.card + 1 ≤ d) :
    K ≤ q ^ (n - A.card - B.card) := by
  classical
  obtain ⟨horth, hkl⟩ := h
  obtain ⟨ρ, hρ⟩ := hkl A hA
  obtain ⟨σ, hσ⟩ := hkl B hB
  set ψ' : Fin K → (({i // i ∈ A} → Fin q) × ({i // i ∈ B} → Fin q) ×
      ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)) → ℂ :=
    fun i p => ψ i (merge3 A B p.1 p.2.1 p.2.2) with hψ'
  have hA' : ∀ i j a a', ∑ b, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a', b, c))
      = (if i = j then (1 : ℂ) else 0) * ρ a a' := by
    intro i j a a'
    calc ∑ b, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a', b, c))
        = ∑ p : ({i // i ∈ B} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q),
            ψ' i (a, p.1, p.2) * (starRingEnd ℂ) (ψ' j (a', p.1, p.2)) := by
          rw [Fintype.sum_prod_type]
      _ = ∑ p, (fun z => ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)))
            (eA A B hAB p) :=
          Finset.sum_congr rfl fun p _ => by
            simp only [hψ', merge_eA A B hAB a p.1 p.2, merge_eA A B hAB a' p.1 p.2]
      _ = ∑ z, ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)) :=
          Equiv.sum_comp (eA A B hAB)
            (fun z => ψ i (merge A a z) * (starRingEnd ℂ) (ψ j (merge A a' z)))
      _ = (if i = j then (1 : ℂ) else 0) * ρ a a' := hρ i j a a'
  have hB' : ∀ i j b b', ∑ a, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a, b', c))
      = (if i = j then (1 : ℂ) else 0) * σ b b' := by
    intro i j b b'
    calc ∑ a, ∑ c, ψ' i (a, b, c) * (starRingEnd ℂ) (ψ' j (a, b', c))
        = ∑ p : ({i // i ∈ A} → Fin q) × ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q),
            ψ' i (p.1, b, p.2) * (starRingEnd ℂ) (ψ' j (p.1, b', p.2)) := by
          rw [Fintype.sum_prod_type]
      _ = ∑ p, (fun z => ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)))
            (eB A B hAB p) :=
          Finset.sum_congr rfl fun p _ => by
            simp only [hψ', merge_eB A B hAB p.1 b p.2, merge_eB A B hAB p.1 b' p.2]
      _ = ∑ z, ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)) :=
          Equiv.sum_comp (eB A B hAB)
            (fun z => ψ i (merge B b z) * (starRingEnd ℂ) (ψ j (merge B b' z)))
      _ = (if i = j then (1 : ℂ) else 0) * σ b b' := hσ i j b b'
  have hne : ∃ i v, ψ' i v ≠ 0 := by
    set i0 : Fin K := ⟨0, hK⟩
    have h1 := horth i0 i0
    rw [if_pos rfl] at h1
    have hv : ∃ v, ψ i0 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      simp [hc] at h1
    obtain ⟨v, hv⟩ := hv
    refine ⟨i0, (fun j => v j, fun j => v j, fun j => v j), ?_⟩
    have hm : merge3 A B (fun j : {i // i ∈ A} => v j) (fun j : {i // i ∈ B} => v j)
        (fun j : {i : Fin n // i ∉ A ∧ i ∉ B} => v j) = v := by
      funext i
      by_cases h : i ∈ A
      · simp [merge3, h]
      · by_cases h' : i ∈ B <;> simp [merge3, h, h']
    simpa [hψ', hm] using hv
  have hcard : Fintype.card ({i : Fin n // i ∉ A ∧ i ∉ B} → Fin q)
      = q ^ (n - A.card - B.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype]
    congr 1
    have hf : (Finset.univ.filter fun i : Fin n => i ∉ A ∧ i ∉ B) = (A ∪ B)ᶜ := by ext i; simp
    rw [hf, Finset.card_compl, Finset.card_union_of_disjoint hAB, Fintype.card_fin]
    omega
  have hfin := core_bound ψ' ρ σ hA' hB' hne
  rwa [hcard] at hfin

/-- The number of codewords of a code on `n` qudits of local dimension `q` is at most `q ^ n`. -/
theorem card_le_pow {d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)} (h : IsQECC n q d K ψ) :
    K ≤ q ^ n := by
  classical
  set Ψ : Matrix (Fin K) (Fin n → Fin q) ℂ := Matrix.of fun i v => ψ i v with hΨ
  have h1 : Ψ * Ψᴴ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, hΨ,
      Matrix.one_apply, RCLike.star_def]
    exact h.1 i j
  have h2 : Ψ.rank = K := by
    rw [← Matrix.rank_self_mul_conjTranspose, h1, Matrix.rank_one, Fintype.card_fin]
  calc K = Ψ.rank := h2.symm
    _ ≤ Fintype.card (Fin n → Fin q) := Matrix.rank_le_card_width _
    _ = q ^ n := by simp

/-- **Quantum Singleton bound** (additive form): for an `[[n, k, d]]` quantum code with
`k ≥ 1` logical qudits, `2 * (d - 1) + k ≤ n`. -/
theorem quantum_singleton_add {k d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hK : K = q ^ k) (h : IsQECC n q d K ψ) :
    2 * (d - 1) + k ≤ n := by
  classical
  have hK1 : 1 ≤ K := by
    rw [hK]; exact Nat.one_le_pow _ _ (by omega)
  have pow_le : K ≤ q ^ n := card_le_pow h
  have disj_le : ∀ (A B : Finset (Fin n)), Disjoint A B → A.card + 1 ≤ d → B.card + 1 ≤ d →
      K ≤ q ^ (n - A.card - B.card) :=
    fun A B hAB hA hB => card_le_of_disjoint_erasures h hK1 A B hAB hA hB
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp only [Nat.zero_sub, Nat.mul_zero, Nat.zero_add]
    rw [hK] at pow_le
    exact (Nat.pow_le_pow_iff_right hq).mp pow_le
  · rcases Nat.lt_or_ge n (2 * (d - 1)) with hcase | hcase
    · exfalso
      obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := min (d - 1) n) (by simp)
      obtain ⟨B, hBsub, hB⟩ := Finset.exists_subset_card_eq (s := Aᶜ) (n := n - min (d - 1) n)
        (by rw [Finset.card_compl, hA]; simp)
      have hdisj : Disjoint A B :=
        Finset.disjoint_left.mpr fun a haA haB => (Finset.mem_compl.mp (hBsub haB)) haA
      have hle := disj_le A B hdisj (by omega) (by omega)
      rw [hA, hB, hK] at hle
      have h0 : n - min (d - 1) n - (n - min (d - 1) n) = 0 := by omega
      rw [h0, pow_zero] at hle
      have h2 : q ^ 1 ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
      simp at h2
      omega
    · obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
        (s := (Finset.univ : Finset (Fin n))) (n := d - 1) (by simp; omega)
      obtain ⟨B, hBsub, hB⟩ := Finset.exists_subset_card_eq (s := Aᶜ) (n := d - 1)
        (by rw [Finset.card_compl, hA]; simp; omega)
      have hdisj : Disjoint A B :=
        Finset.disjoint_left.mpr fun a haA haB => (Finset.mem_compl.mp (hBsub haB)) haA
      have hle := disj_le A B hdisj (by omega) (by omega)
      rw [hA, hB, hK] at hle
      have hkn : k ≤ n - (d - 1) - (d - 1) := (Nat.pow_le_pow_iff_right hq).mp hle
      omega

/-- **Quantum Singleton bound**: an `[[n, k, d]]` quantum code (with `k ≥ 1` logical qudits,
local dimension `q ≥ 2`) obeys `n - k ≥ 2 * (d - 1)`. -/
theorem quantum_singleton {k d K : ℕ} {ψ : Fin K → ((Fin n → Fin q) → ℂ)}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hK : K = q ^ k) (h : IsQECC n q d K ψ) :
    2 * (d - 1) ≤ n - k := by
  have := quantum_singleton_add hq hk hK h
  omega

end Code

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

