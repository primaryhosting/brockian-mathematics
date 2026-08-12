import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header comment is placed directly after the `import` line: Lean 4 requires `import`
commands to come first in a file.)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

open Matrix

/-! ## Permanents as counting problems -/

/-- The permanent, written as a sum over permutations of the products `∏ i, M i (σ i)`
(Mathlib's definition uses `∏ i, M (σ i) i`; the two agree). -/
theorem permanent_eq_sum {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ) :
    M.permanent = ∑ σ : Equiv.Perm V, ∏ i, M i (σ i) := by
  classical
  have h1 : ∀ σ : Equiv.Perm V, ∏ i, M (σ i) i = ∏ i, M i (σ⁻¹ i) := by
    intro σ
    rw [← Equiv.prod_comp σ (fun i => M i (σ⁻¹ i))]
    simp
  rw [Matrix.permanent, Finset.sum_congr rfl (fun σ _ => h1 σ)]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm V)) _ _ (fun σ => rfl)

/-- Reindexing a matrix along an equivalence of index types leaves the permanent unchanged. -/
theorem permanent_submatrix_equiv {V V' : Type*} [Fintype V] [DecidableEq V] [Fintype V']
    [DecidableEq V'] (e : V ≃ V') (M : Matrix V' V' ℕ) :
    (M.submatrix e e).permanent = M.permanent := by
  classical
  refine Fintype.sum_equiv (Equiv.permCongr e) _ _ (fun σ => ?_)
  rw [← Equiv.prod_comp e (fun j => M ((e.permCongr σ) j) j)]
  simp [Matrix.submatrix, Equiv.permCongr]

/-- For a matrix with entries in `{0,1}`, the permanent counts the permutations `σ` all of whose
entries `M i (σ i)` equal `1`; i.e. the permanent of a 0/1 matrix is the number of witnesses of an
explicitly checkable relation (the "membership in `#P`" half of Valiant's theorem). -/
theorem permanent_eq_card_witnesses {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ)
    (h : ∀ i j, M i j ≤ 1) :
    M.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, M i (σ i) = 1} := by
  classical
  rw [permanent_eq_sum M, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases hs : ∀ i, M i (σ i) = 1
  · simp [hs]
  · simp only [hs, if_false]
    push_neg at hs
    obtain ⟨i, hi⟩ := hs
    have hzero : M i (σ i) = 0 := by have := h i (σ i); omega
    exact Finset.prod_eq_zero (Finset.mem_univ i) hzero

/-! ## Simulating nonnegative integer weights by 0/1 entries

Reading a square matrix `W` over `ℕ` as a weighted digraph, `W.permanent` is the total weight of
its cycle covers.  Replacing an edge `i → j` of weight `W i j` by `W i j` parallel two-step paths
through fresh vertices, each fresh vertex carrying a self-loop, produces a *0/1* matrix with the
same permanent.
-/

section Simulation

variable {n : ℕ}

/-- Internal vertices of the gadget: for each pair `(i,j)` we add `W i j` parallel intermediate
vertices. -/
abbrev Idx (W : Matrix (Fin n) (Fin n) ℕ) : Type := Σ p : Fin n × Fin n, Fin (W p.1 p.2)

/-- Vertices of the simulating 0/1 matrix. -/
abbrev Vtx (W : Matrix (Fin n) (Fin n) ℕ) : Type := Fin n ⊕ Idx W

/-- The 0/1 matrix simulating the nonnegative integer matrix `W`. -/
def gadget (W : Matrix (Fin n) (Fin n) ℕ) : Matrix (Vtx W) (Vtx W) ℕ :=
  Matrix.of fun u v =>
    match u, v with
    | Sum.inl _, Sum.inl _ => 0
    | Sum.inl i, Sum.inr t => if t.1.1 = i then 1 else 0
    | Sum.inr t, Sum.inl j => if t.1.2 = j then 1 else 0
    | Sum.inr t, Sum.inr t' => if t = t' then 1 else 0

variable (W : Matrix (Fin n) (Fin n) ℕ)

@[simp] theorem gadget_ll (i j : Fin n) : gadget W (Sum.inl i) (Sum.inl j) = 0 := rfl

@[simp] theorem gadget_lr (i : Fin n) (t : Idx W) :
    gadget W (Sum.inl i) (Sum.inr t) = if t.1.1 = i then 1 else 0 := rfl

@[simp] theorem gadget_rl (t : Idx W) (j : Fin n) :
    gadget W (Sum.inr t) (Sum.inl j) = if t.1.2 = j then 1 else 0 := rfl

@[simp] theorem gadget_rr (t t' : Idx W) :
    gadget W (Sum.inr t) (Sum.inr t') = if t = t' then 1 else 0 := rfl

theorem gadget_zeroOne (u v : Vtx W) : gadget W u v ≤ 1 := by
  cases u <;> cases v <;> simp only [gadget_ll, gadget_lr, gadget_rl, gadget_rr] <;>
    first
      | (split <;> norm_num)
      | norm_num

theorem card_Vtx : Fintype.card (Vtx W) = n + ∑ i, ∑ j, W i j := by
  simp [Fintype.card_sigma, Fintype.sum_prod_type]

/-- A cycle cover of the gadget enters an original vertex `i` through one of the fresh vertices
belonging to a pair `(i, j)`. -/
theorem gadget_witness_inl (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) (i : Fin n) :
    ∃ t : Idx W, σ (Sum.inl i) = Sum.inr t ∧ t.1.1 = i := by
  have h := hσ (Sum.inl i)
  cases hv : σ (Sum.inl i) with
  | inl j => rw [hv, gadget_ll] at h; exact absurd h (by norm_num)
  | inr t =>
    refine ⟨t, rfl, ?_⟩
    rw [hv, gadget_lr] at h
    by_contra hne
    rw [if_neg hne] at h; exact absurd h (by norm_num)

/-- A fresh vertex is either traversed (and then leads to the second component of its pair) or
covered by its self-loop. -/
theorem gadget_witness_inr (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) (s : Idx W) :
    σ (Sum.inr s) = Sum.inl s.1.2 ∨ σ (Sum.inr s) = Sum.inr s := by
  have h := hσ (Sum.inr s)
  cases hv : σ (Sum.inr s) with
  | inl j =>
    rw [hv, gadget_rl] at h
    left
    by_cases hne : s.1.2 = j
    · rw [hne]
    · rw [if_neg hne] at h; exact absurd h (by norm_num)
  | inr s' =>
    rw [hv, gadget_rr] at h
    right
    by_cases hne : s = s'
    · rw [hne]
    · rw [if_neg hne] at h; exact absurd h (by norm_num)

variable (τ : Equiv.Perm (Fin n)) (c : ∀ i, Fin (W i (τ i)))

/-- The fresh vertex used by the cycle cover associated with the permutation `τ` and the choice
function `c`. -/
def gIdx (i : Fin n) : Idx W := ⟨(i, τ i), c i⟩

/-- The cycle cover of the gadget associated with a permutation `τ` and a choice, for every `i`,
of one of the `W i (τ i)` parallel fresh vertices. -/
def gFun : Vtx W → Vtx W :=
  Sum.elim (fun i => Sum.inr (gIdx W τ c i))
    (fun s => if s = gIdx W τ c s.1.1 then Sum.inl s.1.2 else Sum.inr s)

theorem gFun_injective : Function.Injective (gFun W τ c) := by
  classical
  rintro (i | s) (i' | s') h <;> simp only [gFun, Sum.elim_inl, Sum.elim_inr] at h
  · have h1 : gIdx W τ c i = gIdx W τ c i' := Sum.inr_injective h
    have h2 := congrArg (fun z => (Sigma.fst z).1) h1
    simpa [gIdx] using h2
  · by_cases hs : s' = gIdx W τ c s'.1.1
    · rw [if_pos hs] at h; exact absurd h (by simp)
    · rw [if_neg hs] at h
      exact absurd (by rw [← Sum.inr_injective h]; rfl) hs
  · by_cases hs : s = gIdx W τ c s.1.1
    · rw [if_pos hs] at h; exact absurd h (by simp)
    · rw [if_neg hs] at h
      exact absurd (by rw [Sum.inr_injective h]; rfl) hs
  · by_cases hs : s = gIdx W τ c s.1.1 <;> by_cases hs' : s' = gIdx W τ c s'.1.1
    · rw [if_pos hs, if_pos hs'] at h
      have h2 : s.1.2 = s'.1.2 := Sum.inl_injective h
      have e1 : s.1.2 = τ s.1.1 := by
        conv_lhs => rw [hs]
        rfl
      have e2 : s'.1.2 = τ s'.1.1 := by
        conv_lhs => rw [hs']
        rfl
      have h3 : s.1.1 = s'.1.1 := τ.injective (by rw [← e1, ← e2, h2])
      rw [hs, hs', h3]
    · rw [if_pos hs, if_neg hs'] at h; exact absurd h (by simp)
    · rw [if_neg hs, if_pos hs'] at h; exact absurd h (by simp)
    · rw [if_neg hs, if_neg hs'] at h; exact h

/-- The permutation of the vertex set of the gadget determined by `(τ, c)`. -/
noncomputable def gPerm : Equiv.Perm (Vtx W) :=
  Equiv.ofBijective (gFun W τ c) (Finite.injective_iff_bijective.1 (gFun_injective W τ c))

theorem gPerm_apply (v : Vtx W) : gPerm W τ c v = gFun W τ c v := rfl

theorem gPerm_witness (v : Vtx W) : gadget W v (gPerm W τ c v) = 1 := by
  classical
  cases v with
  | inl i => simp [gPerm_apply, gFun, gIdx]
  | inr s =>
    rw [gPerm_apply]
    simp only [gFun, Sum.elim_inr]
    by_cases hs : s = gIdx W τ c s.1.1
    · rw [if_pos hs]; simp
    · rw [if_neg hs]; simp

/-- Every cycle cover of the gadget arises from a permutation `τ` together with a choice of one
parallel fresh vertex for each `i`. -/
theorem exists_gFun (σ : Equiv.Perm (Vtx W)) (hσ : ∀ v, gadget W v (σ v) = 1) :
    ∃ (τ : Equiv.Perm (Fin n)) (c : ∀ i, Fin (W i (τ i))), ∀ v, gFun W τ c v = σ v := by
  classical
  choose t ht1 ht2 using gadget_witness_inl W σ hσ
  obtain ⟨τ₀, hτ₀⟩ : ∃ f : Fin n → Fin n, ∀ i, f i = (t i).1.2 := ⟨_, fun _ => rfl⟩
  have key : ∀ s : Idx W, σ (Sum.inr s) = Sum.inl s.1.2 → t s.1.1 = s := by
    intro s hsj
    have hu := hσ (σ.symm (Sum.inr s))
    rw [Equiv.apply_symm_apply] at hu
    cases hv : σ.symm (Sum.inr s) with
    | inl a =>
      rw [hv, gadget_lr] at hu
      have has : s.1.1 = a := by
        by_contra hne; rw [if_neg hne] at hu; exact absurd hu (by norm_num)
      have hσa : σ (Sum.inl a) = Sum.inr s := by rw [← hv, Equiv.apply_symm_apply]
      rw [ht1 a] at hσa
      rw [has]
      exact Sum.inr_injective hσa
    | inr s' =>
      rw [hv, gadget_rr] at hu
      have hss : s' = s := by
        by_contra hne; rw [if_neg hne] at hu; exact absurd hu (by norm_num)
      subst hss
      have h2 := σ.apply_symm_apply (Sum.inr s')
      rw [hv, hsj] at h2
      exact absurd h2 (by simp)
  have hsurj : Function.Surjective τ₀ := by
    intro j
    have hv0 := hσ (σ.symm (Sum.inl j))
    rw [Equiv.apply_symm_apply] at hv0
    cases hv : σ.symm (Sum.inl j) with
    | inl a => rw [hv, gadget_ll] at hv0; exact absurd hv0 (by norm_num)
    | inr s =>
      rw [hv, gadget_rl] at hv0
      have hs2 : s.1.2 = j := by
        by_contra hne; rw [if_neg hne] at hv0; exact absurd hv0 (by norm_num)
      have hσs : σ (Sum.inr s) = Sum.inl s.1.2 := by
        have h2 := σ.apply_symm_apply (Sum.inl j)
        rw [hv] at h2; rw [h2, hs2]
      exact ⟨s.1.1, by rw [hτ₀, key s hσs, hs2]⟩
  set τ : Equiv.Perm (Fin n) := Equiv.ofBijective τ₀ (Finite.surjective_iff_bijective.mp hsurj)
  have hτapp : ∀ i, τ i = (t i).1.2 := fun i => hτ₀ i
  have hW : ∀ i, W (t i).1.1 (t i).1.2 = W i (τ i) := by
    intro i; rw [ht2 i, hτapp i]
  refine ⟨τ, fun i => Fin.cast (hW i) (t i).2, ?_⟩
  have hti : ∀ i, t i = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) i := by
    intro i
    refine Sigma.ext (Prod.ext (ht2 i) (hτapp i).symm) ?_
    exact (Fin.heq_ext_iff (hW i)).mpr rfl
  intro v
  cases v with
  | inl i =>
    show Sum.inr _ = _
    rw [ht1 i, ← hti i]
  | inr s =>
    show (if s = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) s.1.1 then Sum.inl s.1.2
        else Sum.inr s) = σ (Sum.inr s)
    by_cases hs : s = gIdx W τ (fun i => Fin.cast (hW i) (t i).2) s.1.1
    · rw [if_pos hs]
      rcases gadget_witness_inr W σ hσ s with h | h
      · exact h.symm
      · exfalso
        have hts : t s.1.1 = s := by rw [hti s.1.1, ← hs]
        have hcontr := ht1 s.1.1
        rw [hts, ← h] at hcontr
        exact absurd (σ.injective hcontr) (by simp)
    · rw [if_neg hs]
      rcases gadget_witness_inr W σ hσ s with h | h
      · exact absurd ((key s h).symm.trans (hti s.1.1)) hs
      · exact h.symm

theorem gPerm_bijective :
    Function.Bijective
      (fun x : Σ τ : Equiv.Perm (Fin n), ∀ i, Fin (W i (τ i)) =>
        (⟨gPerm W x.1 x.2, gPerm_witness W x.1 x.2⟩ :
          {σ : Equiv.Perm (Vtx W) // ∀ v, gadget W v (σ v) = 1})) := by
  classical
  constructor
  · rintro ⟨τ, c⟩ ⟨τ', c'⟩ h
    simp only [Subtype.mk.injEq] at h
    have hval : ∀ i, gIdx W τ c i = gIdx W τ' c' i := by
      intro i
      have h2 := congrArg (fun e : Equiv.Perm (Vtx W) => e (Sum.inl i)) h
      simp only [gPerm_apply, gFun, Sum.elim_inl] at h2
      exact Sum.inr_injective h2
    have hτ : τ = τ' := by
      refine Equiv.ext (fun i => ?_)
      have h2 := congrArg (fun z : Idx W => (Sigma.fst z).2) (hval i)
      simpa [gIdx] using h2
    subst hτ
    have hc : c = c' := by
      funext i
      have h2 := hval i
      simpa [gIdx] using h2
    rw [hc]
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, c, hτc⟩ := exists_gFun W σ hσ
    exact ⟨⟨τ, c⟩, Subtype.ext (Equiv.ext (fun v => (gPerm_apply W τ c v).trans (hτc v)))⟩

theorem permanent_gadget : (gadget W).permanent = W.permanent := by
  classical
  rw [permanent_eq_card_witnesses (gadget W) (gadget_zeroOne W), permanent_eq_sum W,
    ← Nat.card_eq_of_bijective _ (gPerm_bijective W)]
  simp [Nat.card_eq_fintype_card, Fintype.card_sigma, Fintype.card_pi]

end Simulation

/-! ## Main statement -/

/--
**Valiant's theorem on the 0/1 permanent** (core formalized content).

The two components proved here are:

1. *Membership in `#P`.*  For a matrix with entries in `{0,1}`, the permanent is literally a
   counting function: it equals the number of permutations `σ` satisfying the explicitly
   checkable condition `∀ i, M i (σ i) = 1` (equivalently, the number of perfect matchings of
   the associated bipartite graph, or the number of cycle covers of the associated digraph).

2. *0/1 entries are as hard as arbitrary nonnegative integer weights.*  For every matrix `W`
   with natural number entries there is an explicit `0/1` matrix `B`, of size
   `n + ∑ i, ∑ j, W i j`, with `B.permanent = W.permanent`.  Thus computing permanents of 0/1
   matrices is as hard as computing permanents of arbitrary nonnegative integer matrices
   (the size of `B` is linear in the total weight, i.e. polynomial in the unary encoding of `W`).

*Scope.*  These are the two statements about the 0/1 permanent that can be phrased purely
matrix-theoretically, without fixing a machine model.  The remaining ingredient of Valiant's
theorem — the gadget reduction turning a Boolean formula `φ` into a weighted matrix whose
permanent determines the number of satisfying assignments of `φ` — is not formalized here.
-/
theorem valiant_permanent :
    (∀ (V : Type) [Fintype V] [DecidableEq V] (M : Matrix V V ℕ), (∀ i j, M i j ≤ 1) →
        M.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, M i (σ i) = 1}) ∧
    (∀ (n : ℕ) (W : Matrix (Fin n) (Fin n) ℕ),
        ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ),
          N = n + ∑ i, ∑ j, W i j ∧ (∀ i j, B i j ≤ 1) ∧ B.permanent = W.permanent) := by
  classical
  refine ⟨fun V _ _ M h => permanent_eq_card_witnesses M h, fun n W => ?_⟩
  obtain ⟨e⟩ := Fintype.truncEquivFin (Vtx W)
  refine ⟨Fintype.card (Vtx W), (gadget W).submatrix e.symm e.symm, card_Vtx W, ?_, ?_⟩
  · intro i j
    exact gadget_zeroOne W _ _
  · rw [permanent_submatrix_equiv e.symm (gadget W)]
    exact permanent_gadget W

/-- Every natural number occurs as the permanent of a 0/1 matrix: the permanent of 0/1 matrices,
as a counting function, is onto `ℕ`. -/
theorem exists_zeroOne_permanent_eq (v : ℕ) :
    ∃ (N : ℕ) (B : Matrix (Fin N) (Fin N) ℕ), (∀ i j, B i j ≤ 1) ∧ B.permanent = v := by
  obtain ⟨N, B, -, hB01, hBperm⟩ := valiant_permanent.2 1 !![v]
  exact ⟨N, B, hB01, by rw [hBperm, Matrix.permanent_unique]; simp⟩

end CS

