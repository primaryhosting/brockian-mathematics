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

open Matrix Finset Module Kronecker ComplexOrder

namespace QI

/-! ## Linear algebra preliminaries -/

/-- Swap the first two factors of a triple product type. -/
def swap12 (X Y Z : Type*) : (X × (Y × Z)) ≃ (Y × (X × Z)) :=
  ⟨fun p => (p.2.1, p.1, p.2.2), fun p => (p.2.1, p.1, p.2.2), fun _ => rfl, fun _ => rfl⟩

/-- Currying isomorphism for functions on a product index type. -/
noncomputable def curryEquiv (α κ : Type*) : ((α × κ) → ℂ) ≃ₗ[ℂ] (κ → (α → ℂ)) where
  toFun x := fun i a => x (a, i)
  map_add' x y := rfl
  map_smul' c x := rfl
  invFun y := fun p => y p.2 p.1
  left_inv x := by funext p; rfl
  right_inv y := by funext i a; rfl

/-- The submodule of `κ`-indexed families with all values in `W` is isomorphic to `κ → W`. -/
noncomputable def piSubEquiv {κ M : Type*} [Fintype κ] [AddCommGroup M] [Module ℂ M]
    (W : Submodule ℂ M) :
    ↥(Submodule.pi (Set.univ : Set κ) (fun _ : κ => W)) ≃ₗ[ℂ] (κ → W) where
  toFun x := fun i => ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  map_add' x y := by funext i; rfl
  map_smul' c x := by funext i; rfl
  invFun y := ⟨fun i => (y i : M), fun i _ => (y i).2⟩
  left_inv x := by ext i; rfl
  right_inv y := by funext i; ext; rfl

/-- Every matrix `F` admits a "projection" `P * R` of rank at most `F.rank` acting as the
identity on the column space of `F`, with `P` having exactly `F.rank` columns. -/
theorem exists_rank_proj {β X : Type*} [Fintype β] [DecidableEq β] [Fintype X] [DecidableEq X]
    (F : Matrix β X ℂ) :
    ∃ (P : Matrix β (Fin F.rank) ℂ) (R : Matrix (Fin F.rank) β ℂ), P * R * F = F := by
  classical
  have hfr : Module.finrank ℂ (LinearMap.range F.mulVecLin) = F.rank := rfl
  set W := LinearMap.range F.mulVecLin with hWdef
  let b : Basis (Fin F.rank) ℂ W := Module.finBasisOfFinrankEq ℂ _ hfr
  let P : Matrix β (Fin F.rank) ℂ := Matrix.of fun x s => ((b s : W) : β → ℂ) x
  have hPmul : ∀ v : Fin F.rank → ℂ, P.mulVec v = ∑ s, v s • ((b s : W) : β → ℂ) := by
    intro v; funext x
    simp [Matrix.mulVec, dotProduct, P, Finset.sum_apply, mul_comm]
  have hPinj : LinearMap.ker P.mulVecLin = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    rw [Matrix.mulVecLin_apply, hPmul] at hv
    have h0 : ∑ s, v s • (b s) = 0 := by
      apply Subtype.ext
      push_cast [Submodule.coe_sum]
      simpa using hv
    funext s
    exact (Fintype.linearIndependent_iff.mp b.linearIndependent) v h0 s
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective P.mulVecLin hPinj
  have hPtm : LinearMap.toMatrix' P.mulVecLin = P :=
    (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  refine ⟨P, LinearMap.toMatrix' g, ?_⟩
  have hRP : (LinearMap.toMatrix' g) * P = 1 := by
    have h := LinearMap.toMatrix'_comp g P.mulVecLin
    rw [hg, hPtm] at h
    simpa using h.symm
  have key : ∀ w ∈ W, (P * LinearMap.toMatrix' g).mulVec w = w := by
    intro w hw
    obtain ⟨c, hc⟩ : ∃ c : Fin F.rank → ℂ, P.mulVec c = w := by
      refine ⟨fun s => b.repr ⟨w, hw⟩ s, ?_⟩
      rw [hPmul]
      have h1 := congrArg (fun z : W => (z : β → ℂ)) (b.sum_repr ⟨w, hw⟩)
      push_cast [Submodule.coe_sum] at h1
      simpa using h1
    rw [← hc, Matrix.mulVec_mulVec, Matrix.mul_assoc, hRP, Matrix.mul_one]
  ext x j
  have hcol : (fun y => F y j) ∈ W :=
    ⟨Pi.single j 1, by
      funext y
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']⟩
  have h2 := key _ hcol
  have hm : ((P * LinearMap.toMatrix' g) * F) x j
      = ((P * LinearMap.toMatrix' g).mulVec (fun y => F y j)) x := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hm, h2]

/-- Multilinear ("Tucker") rank inequality: the rank of a matrix whose rows are indexed by a
product `β × γ` is at most the product of the ranks of its two mode flattenings. -/
theorem tucker_rank_le {β γ : Type*} [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    {X : Type*} [Fintype X] [DecidableEq X] (T : Matrix (β × γ) X ℂ) :
    T.rank ≤ (Matrix.of fun (b : β) (p : γ × X) => T (b, p.1) p.2).rank *
             (Matrix.of fun (c : γ) (p : β × X) => T (p.1, c) p.2).rank := by
  classical
  obtain ⟨PB, RB, hB⟩ := exists_rank_proj (Matrix.of fun (b : β) (p : γ × X) => T (b, p.1) p.2)
  obtain ⟨PC, RC, hC⟩ := exists_rank_proj (Matrix.of fun (c : γ) (p : β × X) => T (p.1, c) p.2)
  have hBe : ∀ (b : β) (c : γ) (x : X), ∑ b', (PB * RB) b b' * T (b', c) x = T (b, c) x := by
    intro b c x
    have := congrFun (congrFun hB b) (c, x)
    simpa [Matrix.mul_apply] using this
  have hCe : ∀ (b : β) (c : γ) (x : X), ∑ c', (PC * RC) c c' * T (b, c') x = T (b, c) x := by
    intro b c x
    have := congrFun (congrFun hC c) (b, x)
    simpa [Matrix.mul_apply] using this
  have key : ((PB * RB) ⊗ₖ (PC * RC)) * T = T := by
    ext p x
    obtain ⟨b, c⟩ := p
    rw [Matrix.mul_apply, Fintype.sum_prod_type]
    have h1 : ∀ b' : β, ∑ c', ((PB * RB) ⊗ₖ (PC * RC)) (b, c) (b', c') * T (b', c') x
        = ∑ c', (PB * RB) b b' * ((PC * RC) c c' * T (b', c') x) := by
      intro b'; refine Finset.sum_congr rfl fun c' _ => ?_
      rw [Matrix.kronecker_apply]; ring
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h2 : ∀ c' : γ, ∑ b', (PB * RB) b b' * ((PC * RC) c c' * T (b', c') x)
        = (PC * RC) c c' * T (b, c') x := by
      intro c'
      rw [← hBe b c' x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b' _ => by ring
    simp_rw [h2]
    exact hCe b c x
  calc T.rank = (((PB * RB) ⊗ₖ (PC * RC)) * T).rank := by rw [key]
    _ ≤ ((PB * RB) ⊗ₖ (PC * RC)).rank := Matrix.rank_mul_le_left _ _
    _ = ((PB ⊗ₖ PC) * (RB ⊗ₖ RC)).rank := by rw [Matrix.mul_kronecker_mul]
    _ ≤ (PB ⊗ₖ PC).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin _ × Fin _) := Matrix.rank_le_card_width _
    _ = _ := by simp

/-- The rank of `σ ⊗ 1` is `card κ` times the rank of `σ`. -/
theorem rank_kron_id {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]
    (σ : Matrix α α ℂ) :
    (Matrix.of fun p q : α × κ => σ p.1 q.1 * (if p.2 = q.2 then 1 else 0)).rank
      = Fintype.card κ * σ.rank := by
  classical
  set f : Matrix (α × κ) (α × κ) ℂ :=
    Matrix.of fun p q => σ p.1 q.1 * (if p.2 = q.2 then 1 else 0) with hf
  set E := curryEquiv α κ with hE
  have hcomm : (E : ((α × κ) → ℂ) →ₗ[ℂ] _) ∘ₗ f.mulVecLin
      = (σ.mulVecLin.compLeft κ) ∘ₗ (E : ((α × κ) → ℂ) →ₗ[ℂ] _) := by
    ext x i a
    simp [E, curryEquiv, Matrix.mulVec, dotProduct, f, LinearMap.compLeft,
      Fintype.sum_prod_type]
  have hmap : Submodule.map (E : ((α × κ) → ℂ) →ₗ[ℂ] _) (LinearMap.range f.mulVecLin)
      = LinearMap.range (σ.mulVecLin.compLeft κ) := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp]
    simp [LinearEquiv.range]
  have h1 : f.rank = finrank ℂ (LinearMap.range (σ.mulVecLin.compLeft κ)) := by
    rw [← hmap, Matrix.rank]
    exact (Submodule.equivMapOfInjective _ (E.injective) _).finrank_eq
  rw [h1, LinearMap.range_compLeft, (piSubEquiv (κ := κ) (LinearMap.range σ.mulVecLin)).finrank_eq,
    Module.finrank_pi_fintype]
  simp [Matrix.rank]

/-- A nonzero matrix has positive rank. -/
theorem rank_pos_of_ne_zero {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (h : A ≠ 0) : 1 ≤ A.rank := by
  rcases Nat.eq_zero_or_pos A.rank with h0 | h1
  · exfalso
    apply h
    have hb : LinearMap.range A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
    have hz : A.mulVecLin = 0 := LinearMap.range_eq_bot.mp hb
    have h2 : LinearMap.toMatrix' A.mulVecLin = A :=
      (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
    rw [← h2, hz, map_zero]
  · exact h1

/-! ## The core no-cloning dimension bound -/

section Core

variable {α β γ κ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype κ] [DecidableEq κ]

/-- **Core bound.**  Let `M` be a nonzero matrix whose columns (indexed by `κ`) are vectors in
a tripartite space `α × β × γ`.  If the reduced "densities" of the columns on the `α` part and
on the `β` part are both independent of the column (the Knill–Laflamme erasure–correction
condition for the subsystems `α` and `β`), then the number of columns is at most `card γ`. -/
theorem card_le_of_two_correctable (M : Matrix (α × β × γ) κ ℂ) (hM : M ≠ 0)
    (σA : Matrix α α ℂ)
    (hA : ∀ (a a' : α) (i j : κ),
      ∑ p : β × γ, (starRingEnd ℂ) (M (a, p.1, p.2) i) * M (a', p.1, p.2) j
        = σA a a' * (if i = j then 1 else 0))
    (σB : Matrix β β ℂ)
    (hB : ∀ (b b' : β) (i j : κ),
      ∑ p : α × γ, (starRingEnd ℂ) (M (p.1, b, p.2) i) * M (p.1, b', p.2) j
        = σB b b' * (if i = j then 1 else 0)) :
    Fintype.card κ ≤ Fintype.card γ := by
  classical
  set NA : Matrix (β × γ) (α × κ) ℂ := Matrix.of fun p q => M (q.1, p.1, p.2) q.2 with hNA
  set NB : Matrix (α × γ) (β × κ) ℂ := Matrix.of fun p q => M (p.1, q.1, p.2) q.2 with hNB
  set FA : Matrix α (β × γ × κ) ℂ := Matrix.of fun a p => M (a, p.1, p.2.1) p.2.2 with hFA
  set FB : Matrix β (α × γ × κ) ℂ := Matrix.of fun b p => M (p.1, b, p.2.1) p.2.2 with hFB
  set FC : Matrix γ (α × β × κ) ℂ := Matrix.of fun c p => M (p.1, p.2.1, c) p.2.2 with hFC
  -- Gram matrices of the two flattenings
  have hgramA : NAᴴ * NA
      = Matrix.of fun p q : α × κ => σA p.1 q.1 * (if p.2 = q.2 then 1 else 0) := by
    ext q q'
    rw [Matrix.mul_apply]
    simpa [Matrix.conjTranspose_apply, hNA] using hA q.1 q'.1 q.2 q'.2
  have hgramB : NBᴴ * NB
      = Matrix.of fun p q : β × κ => σB p.1 q.1 * (if p.2 = q.2 then 1 else 0) := by
    ext q q'
    rw [Matrix.mul_apply]
    simpa [Matrix.conjTranspose_apply, hNB] using hB q.1 q'.1 q.2 q'.2
  have hrankNA : NA.rank = Fintype.card κ * σA.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self NA, hgramA, rank_kron_id]
  have hrankNB : NB.rank = Fintype.card κ * σB.rank := by
    rw [← Matrix.rank_conjTranspose_mul_self NB, hgramB, rank_kron_id]
  -- Tucker bounds
  have htA : NA.rank ≤ FB.rank * FC.rank := by
    refine le_trans (tucker_rank_le NA) ?_
    have h1 : (Matrix.of fun (b : β) (p : γ × (α × κ)) => NA (b, p.1) p.2)
        = FB.submatrix (Equiv.refl β) (swap12 γ α κ) := rfl
    have h2 : (Matrix.of fun (c : γ) (p : β × (α × κ)) => NA (p.1, c) p.2)
        = FC.submatrix (Equiv.refl γ) (swap12 β α κ) := rfl
    rw [h1, h2, Matrix.rank_submatrix FB (Equiv.refl β) (swap12 γ α κ),
      Matrix.rank_submatrix FC (Equiv.refl γ) (swap12 β α κ)]
  have htB : NB.rank ≤ FA.rank * FC.rank := by
    refine le_trans (tucker_rank_le NB) ?_
    have h1 : (Matrix.of fun (a : α) (p : γ × (β × κ)) => NB (a, p.1) p.2)
        = FA.submatrix (Equiv.refl α) (swap12 γ β κ) := rfl
    have h2 : (Matrix.of fun (c : γ) (p : α × (β × κ)) => NB (p.1, c) p.2) = FC := rfl
    rw [h1, h2, Matrix.rank_submatrix FA (Equiv.refl α) (swap12 γ β κ)]
  -- The mode ranks are bounded by the ranks of the reduced densities
  have hFAle : FA.rank ≤ σA.rank := by
    have hkey : FA * FAᴴ = ((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) * σAᵀ := by
      ext a a'
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hr : ∑ a'', ((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) a a'' * σAᵀ a'' a'
          = (Fintype.card κ : ℂ) * σA a' a := by
        simp [Matrix.one_apply, Matrix.transpose_apply, Finset.sum_ite_eq]
      rw [hr]
      have hl : ∑ p : β × γ × κ, FA a p * (FAᴴ) p a'
          = ∑ i : κ, ∑ p : β × γ, (starRingEnd ℂ) (M (a', p.1, p.2) i) * M (a, p.1, p.2) i := by
        simp only [hFA, Matrix.of_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
        calc ∑ b : β, ∑ c : γ, ∑ i : κ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i)
            = ∑ b : β, ∑ i : κ, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i) :=
              Finset.sum_congr rfl fun b _ => Finset.sum_comm
          _ = ∑ i : κ, ∑ b : β, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a', b, c) i) :=
              Finset.sum_comm
          _ = ∑ i : κ, ∑ b : β, ∑ c : γ,
                (starRingEnd ℂ) (M (a', b, c) i) * M (a, b, c) i := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ =>
                Finset.sum_congr rfl fun c _ => by ring
      rw [hl]
      simp_rw [hA a' a]
      simp
    calc FA.rank = (FA * FAᴴ).rank := (Matrix.rank_self_mul_conjTranspose FA).symm
      _ = (((Fintype.card κ : ℂ) • (1 : Matrix α α ℂ)) * σAᵀ).rank := by rw [hkey]
      _ ≤ (σAᵀ).rank := Matrix.rank_mul_le_right _ _
      _ = σA.rank := Matrix.rank_transpose σA
  have hFBle : FB.rank ≤ σB.rank := by
    have hkey : FB * FBᴴ = ((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) * σBᵀ := by
      ext b b'
      rw [Matrix.mul_apply, Matrix.mul_apply]
      have hr : ∑ b'', ((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) b b'' * σBᵀ b'' b'
          = (Fintype.card κ : ℂ) * σB b' b := by
        simp [Matrix.one_apply, Matrix.transpose_apply, Finset.sum_ite_eq]
      rw [hr]
      have hl : ∑ p : α × γ × κ, FB b p * (FBᴴ) p b'
          = ∑ i : κ, ∑ p : α × γ, (starRingEnd ℂ) (M (p.1, b', p.2) i) * M (p.1, b, p.2) i := by
        simp only [hFB, Matrix.of_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
        calc ∑ a : α, ∑ c : γ, ∑ i : κ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i)
            = ∑ a : α, ∑ i : κ, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i) :=
              Finset.sum_congr rfl fun a _ => Finset.sum_comm
          _ = ∑ i : κ, ∑ a : α, ∑ c : γ, M (a, b, c) i * (starRingEnd ℂ) (M (a, b', c) i) :=
              Finset.sum_comm
          _ = ∑ i : κ, ∑ a : α, ∑ c : γ,
                (starRingEnd ℂ) (M (a, b', c) i) * M (a, b, c) i := by
              refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
                Finset.sum_congr rfl fun c _ => by ring
      rw [hl]
      simp_rw [hB b' b]
      simp
    calc FB.rank = (FB * FBᴴ).rank := (Matrix.rank_self_mul_conjTranspose FB).symm
      _ = (((Fintype.card κ : ℂ) • (1 : Matrix β β ℂ)) * σBᵀ).rank := by rw [hkey]
      _ ≤ (σBᵀ).rank := Matrix.rank_mul_le_right _ _
      _ = σB.rank := Matrix.rank_transpose σB
  -- positivity of the mode ranks
  have hFAne : FA ≠ 0 := by
    intro h0
    apply hM
    ext p i
    obtain ⟨a, b, c⟩ := p
    have := congrFun (congrFun h0 a) (b, c, i)
    simpa [hFA] using this
  have hFBne : FB ≠ 0 := by
    intro h0
    apply hM
    ext p i
    obtain ⟨a, b, c⟩ := p
    have := congrFun (congrFun h0 b) (a, c, i)
    simpa [hFB] using this
  have hFApos : 1 ≤ FA.rank := rank_pos_of_ne_zero _ hFAne
  have hFBpos : 1 ≤ FB.rank := rank_pos_of_ne_zero _ hFBne
  -- put everything together
  set K := Fintype.card κ
  have e1 : K * FA.rank ≤ FB.rank * FC.rank := by
    calc K * FA.rank ≤ K * σA.rank := Nat.mul_le_mul_left _ hFAle
      _ = NA.rank := hrankNA.symm
      _ ≤ FB.rank * FC.rank := htA
  have e2 : K * FB.rank ≤ FA.rank * FC.rank := by
    calc K * FB.rank ≤ K * σB.rank := Nat.mul_le_mul_left _ hFBle
      _ = NB.rank := hrankNB.symm
      _ ≤ FA.rank * FC.rank := htB
  have e3 : (K * K) * (FA.rank * FB.rank) ≤ (FC.rank * FC.rank) * (FA.rank * FB.rank) := by
    have := Nat.mul_le_mul e1 e2
    calc (K * K) * (FA.rank * FB.rank) = (K * FA.rank) * (K * FB.rank) := by ring
      _ ≤ (FB.rank * FC.rank) * (FA.rank * FC.rank) := this
      _ = (FC.rank * FC.rank) * (FA.rank * FB.rank) := by ring
  have hpos : 0 < FA.rank * FB.rank := Nat.mul_pos hFApos hFBpos
  have e4 : K * K ≤ FC.rank * FC.rank := Nat.le_of_mul_le_mul_right e3 hpos
  have e5 : K ≤ FC.rank := Nat.mul_self_le_mul_self_iff.mp e4
  exact le_trans e5 (Matrix.rank_le_card_height FC)

end Core

/-! ## Quantum codes: the Knill–Laflamme distance condition and the Singleton bound -/

section Codes

variable {n a b c q K : ℕ}

/-- `glue e P` assembles a full string of `n` letters out of the three partial strings `P`,
along the splitting `e` of the coordinate set into three blocks. -/
def glue (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) :
    ((Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) → (Fin n → Fin q) :=
  fun P i => Sum.elim (Sum.elim P.1 P.2.1) P.2.2 (e.symm i)

/-- The first of the three coordinate blocks determined by the splitting `e`. -/
def firstBlock (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) : Finset (Fin n) :=
  Finset.image (fun s : Fin a => e (Sum.inl (Sum.inl s))) Finset.univ

lemma card_firstBlock (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) : (firstBlock e).card = a := by
  rw [firstBlock, Finset.card_image_of_injective]
  · simp
  · intro s t h
    simpa using e.injective h

lemma mem_firstBlock_iff (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) (i : Fin n) :
    i ∈ firstBlock e ↔ ∃ s : Fin a, e (Sum.inl (Sum.inl s)) = i := by
  simp [firstBlock]

lemma glue_inll (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (P : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) (s : Fin a) :
    glue (q := q) e P (e (Sum.inl (Sum.inl s))) = P.1 s := by simp [glue]

lemma glue_agree_off (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (P Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) :
    (∀ i ∉ firstBlock e, glue (q := q) e P i = glue (q := q) e Q i) ↔ P.2 = Q.2 := by
  constructor
  · intro h
    have hb : ∀ s : Fin b, e (Sum.inl (Sum.inr s)) ∉ firstBlock e := by
      intro s hs
      rw [mem_firstBlock_iff] at hs
      obtain ⟨t, ht⟩ := hs
      simpa using e.injective ht
    have hc : ∀ s : Fin c, e (Sum.inr s) ∉ firstBlock e := by
      intro s hs
      rw [mem_firstBlock_iff] at hs
      obtain ⟨t, ht⟩ := hs
      simpa using e.injective ht
    refine Prod.ext ?_ ?_
    · funext s
      simpa [glue] using h _ (hb s)
    · funext s
      simpa [glue] using h _ (hc s)
  · intro h i hi
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s
    · exact absurd ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩) hi
    · have h1 : P.2.1 = Q.2.1 := congrArg Prod.fst h
      simp [glue, h1]
    · have h2 : P.2.2 = Q.2.2 := congrArg Prod.snd h
      simp [glue, h2]

lemma glue_bijective (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n) :
    Function.Bijective (glue (q := q) (a := a) (b := b) (c := c) e) := by
  constructor
  · intro P Q h
    obtain ⟨u, v, w⟩ := P
    obtain ⟨u', v', w'⟩ := Q
    have h1 : u = u' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inl (Sum.inl s)))
    have h2 : v = v' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inl (Sum.inr s)))
    have h3 : w = w' := by
      funext s; simpa [glue] using congrFun h (e (Sum.inr s))
    simp [h1, h2, h3]
  · intro x
    refine ⟨(fun s => x (e (Sum.inl (Sum.inl s))), fun s => x (e (Sum.inl (Sum.inr s))),
      fun s => x (e (Sum.inr s))), ?_⟩
    funext i
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s <;> simp [glue]

lemma sum_indicator_collapse {A' P : Type*} [Fintype A'] [DecidableEq A'] [Fintype P]
    [DecidableEq P] (f g : A' → P → ℂ) (u u' : A') :
    ∑ X : A' × P, ∑ Y : A' × P,
      f X.1 X.2 * ((if X.1 = u then (1:ℂ) else 0) * (if Y.1 = u' then 1 else 0) *
        (if X.2 = Y.2 then 1 else 0)) * g Y.1 Y.2 = ∑ p : P, f u p * g u' p := by
  simp [Fintype.sum_prod_type, Finset.sum_ite_eq', mul_comm]

/-- `E` is an error operator supported on the coordinate set `T`: outside `T` it acts as the
identity (it is of the form `F ⊗ 1`, with `F` acting on the coordinates in `T`). -/
def SupportedOn (T : Finset (Fin n)) (E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) : Prop :=
  ∃ F : (Fin n → Fin q) → (Fin n → Fin q) → ℂ,
    (∀ x x' y y' : Fin n → Fin q, (∀ i ∈ T, x i = x' i) → (∀ i ∈ T, y i = y' i) → F x y = F x' y')
      ∧ ∀ x y, E x y = if (∀ i ∉ T, x i = y i) then F x y else 0

/-- The Knill–Laflamme condition: the quantum code spanned by the columns of `M` (a code in
`(ℂ^q)^{⊗n}` of dimension `K`) has distance at least `d`, i.e. for every error operator `E`
acting on fewer than `d` of the `n` qudits, `Mᴴ E M` is a scalar multiple of the identity. -/
def HasDistanceGE (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (d : ℕ) : Prop :=
  ∀ (T : Finset (Fin n)) (E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ),
    T.card < d → SupportedOn T E → ∃ lam : ℂ, Mᴴ * E * M = lam • (1 : Matrix (Fin K) (Fin K) ℂ)

/-- Sanity check: any isometric encoding has distance at least one, so the Knill–Laflamme
condition above is satisfiable. -/
lemma hasDistanceGE_one (hq : 0 < q) (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hM : Mᴴ * M = 1) :
    HasDistanceGE M 1 := by
  classical
  rintro T E hT ⟨F, hFdep, hE⟩
  have hT0 : T = ∅ := Finset.card_eq_zero.mp (by omega)
  subst hT0
  set x₀ : Fin n → Fin q := fun _ => ⟨0, hq⟩ with hx0
  refine ⟨F x₀ x₀, ?_⟩
  have hEeq : E = (F x₀ x₀) • (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) := by
    ext x y
    rw [hE x y]
    have hcond : (∀ i ∉ (∅ : Finset (Fin n)), x i = y i) ↔ x = y := by
      constructor
      · intro h; funext i; exact h i (by simp)
      · intro h i _; rw [h]
    have hFc : F x y = F x₀ x₀ := hFdep x x₀ y x₀ (by simp) (by simp)
    simp only [hcond, hFc]
    by_cases hxy : x = y <;> simp [hxy]
  rw [hEeq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hM]

/-- A code of distance at least `d` corrects the erasure of any block of fewer than `d`
coordinates: the "reduced density matrix" on such a block does not depend on the codeword. -/
lemma correctable_of_distance {d : ℕ}
    (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hd : HasDistanceGE M d) (ha : a < d)
    (u u' : Fin a → Fin q) :
    ∃ lam : ℂ, ∀ i j : Fin K,
      ∑ p : (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M (glue e (u, p.1, p.2)) i) * M (glue e (u', p.1, p.2)) j
        = lam * (if i = j then 1 else 0) := by
  classical
  set A := firstBlock e with hA
  set F : (Fin n → Fin q) → (Fin n → Fin q) → ℂ := fun x y =>
    (if (∀ s : Fin a, x (e (Sum.inl (Sum.inl s))) = u s) then (1:ℂ) else 0) *
    (if (∀ s : Fin a, y (e (Sum.inl (Sum.inl s))) = u' s) then (1:ℂ) else 0) with hF
  set E : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ := Matrix.of fun x y =>
    if (∀ i ∉ A, x i = y i) then F x y else 0 with hE
  have hsupp : SupportedOn A E := by
    refine ⟨F, ?_, fun x y => rfl⟩
    intro x x' y y' hx hy
    have h1 : ∀ s : Fin a, x (e (Sum.inl (Sum.inl s))) = x' (e (Sum.inl (Sum.inl s))) :=
      fun s => hx _ ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩)
    have h2 : ∀ s : Fin a, y (e (Sum.inl (Sum.inl s))) = y' (e (Sum.inl (Sum.inl s))) :=
      fun s => hy _ ((mem_firstBlock_iff e _).mpr ⟨s, rfl⟩)
    simp only [hF, h1, h2]
  obtain ⟨lam, hlam⟩ := hd A E (by rw [hA, card_firstBlock]; exact ha) hsupp
  refine ⟨lam, fun i j => ?_⟩
  have hentry := congrFun (congrFun hlam i) j
  have hL : (Mᴴ * E * M) i j
      = ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
          (starRingEnd ℂ) (M x i) * E x y * M y j := by
    rw [Matrix.mul_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by simp [Matrix.conjTranspose_apply]
  have hEg : ∀ P Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
      E (glue e P) (glue e Q)
        = (if P.1 = u then (1:ℂ) else 0) * (if Q.1 = u' then 1 else 0) *
          (if P.2 = Q.2 then 1 else 0) := by
    intro P Q
    have h1 : (∀ s : Fin a, glue (q := q) e P (e (Sum.inl (Sum.inl s))) = u s) ↔ P.1 = u := by
      constructor
      · intro h; funext s; rw [← glue_inll e P s]; exact h s
      · intro h s; rw [glue_inll e P s, h]
    have h2 : (∀ s : Fin a, glue (q := q) e Q (e (Sum.inl (Sum.inl s))) = u' s) ↔ Q.1 = u' := by
      constructor
      · intro h; funext s; rw [← glue_inll e Q s]; exact h s
      · intro h s; rw [glue_inll e Q s, h]
    simp only [hE, Matrix.of_apply, hF, hA, glue_agree_off e P Q, h1, h2]
    split_ifs <;> ring
  have s1 : ∀ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (starRingEnd ℂ) (M x i) * E x y * M y j
      = ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j := fun x =>
    (Fintype.sum_bijective (glue e) (glue_bijective e)
      (fun Q => (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j)
      (fun y => (starRingEnd ℂ) (M x i) * E x y * M y j) (fun Q => rfl)).symm
  have s2 := Fintype.sum_bijective (glue e) (glue_bijective e)
      (fun P => ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M (glue e P) i) * E (glue e P) (glue e Q) * M (glue e Q) j)
      (fun x => ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M x i) * E x (glue e Q) * M (glue e Q) j) (fun P => rfl)
  have hsum : ∑ x : Fin n → Fin q, ∑ y : Fin n → Fin q,
        (starRingEnd ℂ) (M x i) * E x y * M y j
      = ∑ P : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          ∑ Q : (Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q),
          (starRingEnd ℂ) (M (glue e P) i) * E (glue e P) (glue e Q) * M (glue e Q) j := by
    simp_rw [s1]
    exact s2.symm
  rw [hL, hsum] at hentry
  simp only [hEg] at hentry
  have hone : ((lam • (1 : Matrix (Fin K) (Fin K) ℂ)) i j) = lam * (if i = j then 1 else 0) := by
    simp [Matrix.one_apply]
  rw [hone] at hentry
  rw [← hentry]
  exact (sum_indicator_collapse (A' := Fin a → Fin q)
    (P := (Fin b → Fin q) × (Fin c → Fin q))
    (fun w p => (starRingEnd ℂ) (M (glue e (w, p)) i)) (fun w p => M (glue e (w, p)) j) u u').symm

/-- If a code of dimension `K` in `(ℂ^q)^{⊗n}` has distance greater than the sizes of two
disjoint coordinate blocks of sizes `a` and `b`, then `K ≤ q ^ c`, where `c` is the number of
remaining coordinates. -/
lemma card_le_pow_of_distance {d : ℕ} (e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hMne : M ≠ 0)
    (hd : HasDistanceGE M d) (ha : a < d) (hb : b < d) :
    K ≤ q ^ c := by
  classical
  set M' : Matrix ((Fin a → Fin q) × (Fin b → Fin q) × (Fin c → Fin q)) (Fin K) ℂ :=
    Matrix.of fun P i => M (glue e P) i with hM'
  have hM'ne : M' ≠ 0 := by
    intro h0
    apply hMne
    ext x i
    obtain ⟨P, rfl⟩ := (glue_bijective e).surjective x
    simpa [hM'] using congrFun (congrFun h0 P) i
  choose σA0 hσA0 using fun u u' => correctable_of_distance e M hd ha u u'
  set e' : ((Fin b ⊕ Fin a) ⊕ Fin c) ≃ Fin n :=
    (Equiv.sumCongr (Equiv.sumComm (Fin b) (Fin a)) (Equiv.refl (Fin c))).trans e with he'
  have hglue' : ∀ (v : Fin b → Fin q) (u : Fin a → Fin q) (w : Fin c → Fin q),
      glue (q := q) e' (v, u, w) = glue (q := q) e (u, v, w) := by
    intro v u w
    funext i
    obtain ⟨z, rfl⟩ := e.surjective i
    rcases z with (s | s) | s <;> simp [glue, he']
  choose σB0 hσB0 using fun v v' => correctable_of_distance e' M hd hb v v'
  have hA' : ∀ (u u' : Fin a → Fin q) (i j : Fin K),
      ∑ p : (Fin b → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M' (u, p.1, p.2) i) * M' (u', p.1, p.2) j
        = (Matrix.of σA0) u u' * (if i = j then 1 else 0) := by
    intro u u' i j
    simpa [hM'] using hσA0 u u' i j
  have hB' : ∀ (v v' : Fin b → Fin q) (i j : Fin K),
      ∑ p : (Fin a → Fin q) × (Fin c → Fin q),
        (starRingEnd ℂ) (M' (p.1, v, p.2) i) * M' (p.1, v', p.2) j
        = (Matrix.of σB0) v v' * (if i = j then 1 else 0) := by
    intro v v' i j
    have h := hσB0 v v' i j
    simp only [hglue'] at h
    simpa [hM'] using h
  have hcard := card_le_of_two_correctable M' hM'ne (Matrix.of σA0) hA' (Matrix.of σB0) hB'
  simpa using hcard

/-- **The quantum Singleton bound.**  Let `M` be an isometric encoding of `K = q ^ k` logical
states into `n` qudits of local dimension `q ≥ 2` (the columns of `M` are an orthonormal basis
of the code), and suppose the code satisfies the Knill–Laflamme condition for distance `d`.
Then `2 * (d - 1) + k ≤ n`, i.e. `n - k ≥ 2 (d - 1)`.

The hypothesis `1 ≤ k` is needed: a one-dimensional code satisfies the Knill–Laflamme
condition vacuously for every `d`. -/
theorem quantum_singleton {n q k d K : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hK : K = q ^ k)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hM : Mᴴ * M = 1) (hd : HasDistanceGE M d) :
    2 * (d - 1) + k ≤ n := by
  classical
  have hq1 : 1 < q := hq
  have hK2 : 2 ≤ K := by
    rw [hK]
    calc (2:ℕ) = 2 ^ 1 := by norm_num
      _ ≤ q ^ 1 := Nat.pow_le_pow_left hq 1
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hMne : M ≠ 0 := by
    intro h0
    rw [h0] at hM
    have hz : (0 : Matrix (Fin K) (Fin K) ℂ) = 1 := by simpa using hM
    have h1 := congrFun (congrFun hz ⟨0, by omega⟩) ⟨0, by omega⟩
    simp at h1
  rcases le_or_gt d 1 with hd1 | hd2
  · have hdz : d - 1 = 0 := by omega
    have hKn : K ≤ q ^ n := by
      have h2 : (Mᴴ * M).rank = M.rank := Matrix.rank_conjTranspose_mul_self M
      rw [hM, Matrix.rank_one] at h2
      have h3 : M.rank ≤ Fintype.card (Fin n → Fin q) := Matrix.rank_le_card_height M
      rw [← h2] at h3
      simpa using h3
    have h4 : q ^ k ≤ q ^ n := hK ▸ hKn
    have h5 := (Nat.pow_le_pow_iff_right hq1).mp h4
    omega
  · set a := min (d - 1) n with hadef
    set b := min (d - 1) (n - a) with hbdef
    set c := n - a - b with hcdef
    have hn : n = a + b + c := by omega
    let e : ((Fin a ⊕ Fin b) ⊕ Fin c) ≃ Fin n :=
      (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin c))).trans
        (finSumFinEquiv.trans (finCongr hn.symm))
    have hKc : K ≤ q ^ c := card_le_pow_of_distance e M hMne hd (by omega) (by omega)
    have h4 : q ^ k ≤ q ^ c := hK ▸ hKc
    have h5 := (Nat.pow_le_pow_iff_right hq1).mp h4
    omega

/-- The quantum Singleton bound in the literal form `n - k ≥ 2 * (d - 1)` (natural subtraction). -/
theorem quantum_singleton_sub {n q k d K : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hK : K = q ^ k)
    (M : Matrix (Fin n → Fin q) (Fin K) ℂ) (hM : Mᴴ * M = 1) (hd : HasDistanceGE M d) :
    2 * (d - 1) ≤ n - k := by
  have := quantum_singleton hq hk hK M hM hd
  omega

end Codes

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

