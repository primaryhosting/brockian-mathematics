import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/
def piSub (Z : Type*) [Fintype X] (W : Submodule ℂ (X → ℂ)) : Submodule ℂ (Z × X → ℂ) where
  carrier := {v | ∀ z, (fun x => v (z, x)) ∈ W}
  add_mem' := by intro a b ha hb z; exact W.add_mem (ha z) (hb z)
  zero_mem' := fun z => W.zero_mem
  smul_mem' := by intro c a ha z; exact W.smul_mem c (ha z)

/-- `piSub Z W` is linearly isomorphic to `Z → W`. -/
noncomputable def piSubEquiv [Fintype X] (W : Submodule ℂ (X → ℂ)) :
    piSub (X := X) Z W ≃ₗ[ℂ] (Z → W) where
  toFun v := fun z => ⟨fun x => v.1 (z, x), v.2 z⟩
  map_add' := by intro a b; rfl
  map_smul' := by intro c a; rfl
  invFun g := ⟨fun p => (g p.1).1 p.2, fun z => (g z).2⟩
  left_inv := by intro v; ext p; rfl
  right_inv := by intro g; ext z x; rfl

lemma finrank_piSub [Fintype X] [Fintype Z] (W : Submodule ℂ (X → ℂ)) :
    finrank ℂ (piSub (X := X) Z W) = Fintype.card Z * finrank ℂ W := by
  rw [(piSubEquiv W).finrank_eq]
  simp [Module.finrank_pi_fintype]

/-- Moving an index from the rows to the columns can decrease the rank at most by the
factor `Fintype.card Z`. -/
lemma rank_merge_le [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq Z]
    (M : Matrix (Z × X) Y ℂ) (N : Matrix X (Z × Y) ℂ)
    (h : ∀ z x y, N x (z, y) = M (z, x) y) :
    M.rank ≤ Fintype.card Z * N.rank := by
  have hsub : LinearMap.range M.mulVecLin ≤ piSub Z (LinearMap.range N.mulVecLin) := by
    rintro _ ⟨u, rfl⟩ z
    refine ⟨fun p => if p.1 = z then u p.2 else 0, ?_⟩
    ext x
    simp only [mulVecLin_apply, mulVec, dotProduct]
    rw [Fintype.sum_prod_type]
    simp [h, Finset.sum_ite_eq' Finset.univ z]
  calc M.rank = finrank ℂ (LinearMap.range M.mulVecLin) := rfl
    _ ≤ finrank ℂ (piSub Z (LinearMap.range N.mulVecLin)) := Submodule.finrank_mono hsub
    _ = Fintype.card Z * N.rank := finrank_piSub _

/-- The rank of `1 ⊗ σ` is `(card R) * rank σ`. -/
lemma rank_id_tensor [Fintype X] [Fintype R] [DecidableEq R]
    (σ : Matrix X X ℂ) (T : Matrix (R × X) (R × X) ℂ)
    (hT : ∀ i j x x', T (i, x) (j, x') = (if i = j then (1 : ℂ) else 0) * σ x x') :
    T.rank = Fintype.card R * σ.rank := by
  have key : LinearMap.range T.mulVecLin = piSub R (LinearMap.range σ.mulVecLin) := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩ i
      refine ⟨fun x' => u (i, x'), ?_⟩
      ext x
      simp only [mulVecLin_apply, mulVec, dotProduct]
      rw [Fintype.sum_prod_type]
      simp [hT]
    · intro v hv
      choose w hw using hv
      refine ⟨fun p => w p.1 p.2, ?_⟩
      ext p
      obtain ⟨i, x⟩ := p
      simp only [mulVecLin_apply, mulVec, dotProduct]
      rw [Fintype.sum_prod_type]
      have hsum : ∀ j, ∑ x', T (i, x) (j, x') * w j x' =
          if j = i then (σ.mulVecLin (w i)) x else 0 := by
        intro j
        by_cases hj : j = i
        · subst hj; simp [hT, mulVec, dotProduct]
        · simp [hT, Ne.symm hj, hj]
      rw [Finset.sum_congr rfl (fun j _ => hsum j), Finset.sum_ite_eq' Finset.univ i]
      simp [hw i]
  calc T.rank = finrank ℂ (LinearMap.range T.mulVecLin) := rfl
    _ = finrank ℂ (piSub R (LinearMap.range σ.mulVecLin)) := by rw [key]
    _ = Fintype.card R * σ.rank := finrank_piSub _

lemma rank_smul_ne_zero [Fintype X] [Fintype Y] (c : ℂ) (hc : c ≠ 0) (M : Matrix X Y ℂ) :
    (c • M).rank = M.rank := by
  have h : LinearMap.range (c • M).mulVecLin = LinearMap.range M.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨u, rfl⟩
      exact ⟨c • u, by ext x; simp⟩
    · rintro _ ⟨u, rfl⟩
      refine ⟨c⁻¹ • u, ?_⟩
      ext x
      have hx : c⁻¹ * (c * (M *ᵥ u) x) = (M *ᵥ u) x := by field_simp
      simpa using hx
  simp only [Matrix.rank]
  rw [h]

lemma rank_pos_of_ne_zero [Fintype X] [Fintype Y] [DecidableEq Y]
    (M : Matrix X Y ℂ) (hM : M ≠ 0) : 0 < M.rank := by
  rcases Nat.eq_zero_or_pos M.rank with h | h
  · exfalso
    have hbot : LinearMap.range M.mulVecLin = ⊥ := by
      rw [← Submodule.finrank_eq_zero]; exact h
    apply hM
    ext x y
    have hzero : M.mulVecLin (Pi.single y 1) = 0 := by
      have := LinearMap.range_eq_bot.mp hbot
      simp [this]
    have := congrFun hzero x
    simpa [mulVecLin_apply, mulVec_single] using this
  · exact h

end RankTools


section CoreLemma

variable {A B C : Type*}

open ComplexConjugate

/-- **Core decoupling lemma.**
If a four-party tensor `f : R → A → B → C → ℂ` has the property that the `R`-`A` marginal
and the `R`-`B` marginal both factorize (the `R` register is decoupled from `A`, and from `B`),
then `card R ≤ card C`. -/
theorem card_le_of_decoupled [Fintype R] [DecidableEq R] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (f : R → A → B → C → ℂ) (σ : Matrix A A ℂ) (τ : Matrix B B ℂ)
    (hA : ∀ i j a a', (∑ c, ∑ b, f i a b c * conj (f j a' b c))
            = (if i = j then (1 : ℂ) else 0) * σ a a')
    (hB : ∀ i j b b', (∑ c, ∑ a, f i a b c * conj (f j a b' c))
            = (if i = j then (1 : ℂ) else 0) * τ b b')
    (hf : ∃ i a b c, f i a b c ≠ 0) :
    Fintype.card R ≤ Fintype.card C := by
  classical
  obtain ⟨i₀, a₀, b₀, c₀, hne⟩ := hf
  have hRpos : 0 < Fintype.card R := Fintype.card_pos_iff.mpr ⟨i₀⟩
  -- the four reshapings
  set MRA : Matrix (R × A) (C × B) ℂ := fun p r => f p.1 p.2 r.2 r.1 with hMRA
  set MRB : Matrix (R × B) (C × A) ℂ := fun p r => f p.1 r.2 p.2 r.1 with hMRB
  set MA : Matrix A (C × (R × B)) ℂ := fun a p => f p.2.1 a p.2.2 p.1 with hMA
  set MB : Matrix B (C × (R × A)) ℂ := fun b p => f p.2.1 p.2.2 b p.1 with hMB
  -- rank of MRA
  have hMRArank : MRA.rank = Fintype.card R * σ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MRA]
    refine rank_id_tensor σ _ ?_
    intro i j a a'
    have : (MRA * MRAᴴ) (i, a) (j, a') = ∑ r : C × B, f i a r.2 r.1 * conj (f j a' r.2 r.1) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMRA]
    rw [this, Fintype.sum_prod_type]
    exact hA i j a a'
  have hMRBrank : MRB.rank = Fintype.card R * τ.rank := by
    rw [← Matrix.rank_self_mul_conjTranspose MRB]
    refine rank_id_tensor τ _ ?_
    intro i j b b'
    have : (MRB * MRBᴴ) (i, b) (j, b') = ∑ r : C × A, f i r.2 b r.1 * conj (f j r.2 b' r.1) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMRB]
    rw [this, Fintype.sum_prod_type]
    exact hB i j b b'
  -- rank of the single-party reshapings
  have hMArank : MA.rank = σ.rank := by
    have hprod : MA * MAᴴ = (Fintype.card R : ℂ) • σ := by
      ext a a'
      have h1 : (MA * MAᴴ) a a'
          = ∑ p : C × (R × B), f p.2.1 a p.2.2 p.1 * conj (f p.2.1 a' p.2.2 p.1) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMA]
      rw [h1, Fintype.sum_prod_type]
      have h2 : ∀ c : C, (∑ p : R × B, f p.1 a p.2 c * conj (f p.1 a' p.2 c))
          = ∑ i : R, ∑ b : B, f i a b c * conj (f i a' b c) := by
        intro c; rw [Fintype.sum_prod_type]
      simp only [h2]
      rw [Finset.sum_comm]
      have h3 : ∀ i : R, (∑ c : C, ∑ b : B, f i a b c * conj (f i a' b c)) = σ a a' := by
        intro i; simpa using hA i i a a'
      rw [Finset.sum_congr rfl (fun i _ => h3 i)]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← Matrix.rank_self_mul_conjTranspose MA, hprod,
      rank_smul_ne_zero _ (by exact_mod_cast hRpos.ne') σ]
  have hMBrank : MB.rank = τ.rank := by
    have hprod : MB * MBᴴ = (Fintype.card R : ℂ) • τ := by
      ext b b'
      have h1 : (MB * MBᴴ) b b'
          = ∑ p : C × (R × A), f p.2.1 p.2.2 b p.1 * conj (f p.2.1 p.2.2 b' p.1) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, hMB]
      rw [h1, Fintype.sum_prod_type]
      have h2 : ∀ c : C, (∑ p : R × A, f p.1 p.2 b c * conj (f p.1 p.2 b' c))
          = ∑ i : R, ∑ a : A, f i a b c * conj (f i a b' c) := by
        intro c; rw [Fintype.sum_prod_type]
      simp only [h2]
      rw [Finset.sum_comm]
      have h3 : ∀ i : R, (∑ c : C, ∑ a : A, f i a b c * conj (f i a b' c)) = τ b b' := by
        intro i; simpa using hB i i b b'
      rw [Finset.sum_congr rfl (fun i _ => h3 i)]
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [← Matrix.rank_self_mul_conjTranspose MB, hprod,
      rank_smul_ne_zero _ (by exact_mod_cast hRpos.ne') τ]
  -- the two merge inequalities
  have hmerge1 : Fintype.card R * σ.rank ≤ Fintype.card C * τ.rank := by
    have h1 : (MRAᵀ).rank ≤ Fintype.card C * MB.rank := by
      refine rank_merge_le _ _ ?_
      intro c b p
      rfl
    rw [Matrix.rank_transpose, hMRArank, hMBrank] at h1
    exact h1
  have hmerge2 : Fintype.card R * τ.rank ≤ Fintype.card C * σ.rank := by
    have h1 : (MRBᵀ).rank ≤ Fintype.card C * MA.rank := by
      refine rank_merge_le _ _ ?_
      intro c a p
      rfl
    rw [Matrix.rank_transpose, hMRBrank, hMArank] at h1
    exact h1
  -- positivity of the two ranks
  have hσ0 : σ a₀ a₀ ≠ 0 := by
    have h := hA i₀ i₀ a₀ a₀
    rw [if_pos rfl, one_mul] at h
    rw [← h]
    have hreal : (∑ c, ∑ b, f i₀ a₀ b c * conj (f i₀ a₀ b c))
        = ((∑ c, ∑ b, Complex.normSq (f i₀ a₀ b c) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ =>
        (Complex.mul_conj (f i₀ a₀ b c))
    rw [hreal]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have hpos : 0 < (∑ c, ∑ b, Complex.normSq (f i₀ a₀ b c)) := by
      refine Finset.sum_pos' (fun c _ => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _)
        ⟨c₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_pos' (fun b _ => Complex.normSq_nonneg _) ⟨b₀, Finset.mem_univ _, ?_⟩
      exact Complex.normSq_pos.mpr hne
    exact hpos.ne'
  have hτ0 : τ b₀ b₀ ≠ 0 := by
    have h := hB i₀ i₀ b₀ b₀
    rw [if_pos rfl, one_mul] at h
    rw [← h]
    have hreal : (∑ c, ∑ a, f i₀ a b₀ c * conj (f i₀ a b₀ c))
        = ((∑ c, ∑ a, Complex.normSq (f i₀ a b₀ c) : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ =>
        (Complex.mul_conj (f i₀ a b₀ c))
    rw [hreal]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    have hpos : 0 < (∑ c, ∑ a, Complex.normSq (f i₀ a b₀ c)) := by
      refine Finset.sum_pos' (fun c _ => Finset.sum_nonneg fun a _ => Complex.normSq_nonneg _)
        ⟨c₀, Finset.mem_univ _, ?_⟩
      refine Finset.sum_pos' (fun a _ => Complex.normSq_nonneg _) ⟨a₀, Finset.mem_univ _, ?_⟩
      exact Complex.normSq_pos.mpr hne
    exact hpos.ne'
  have hσpos : 0 < σ.rank :=
    rank_pos_of_ne_zero σ (fun h => hσ0 (by rw [h]; rfl))
  have hτpos : 0 < τ.rank :=
    rank_pos_of_ne_zero τ (fun h => hτ0 (by rw [h]; rfl))
  -- conclude
  have hmul : (Fintype.card R * σ.rank) * (Fintype.card R * τ.rank)
      ≤ (Fintype.card C * τ.rank) * (Fintype.card C * σ.rank) :=
    Nat.mul_le_mul hmerge1 hmerge2
  have hsq : Fintype.card R * Fintype.card R ≤ Fintype.card C * Fintype.card C := by
    have hpos : 0 < σ.rank * τ.rank := Nat.mul_pos hσpos hτpos
    have : (Fintype.card R * Fintype.card R) * (σ.rank * τ.rank)
        ≤ (Fintype.card C * Fintype.card C) * (σ.rank * τ.rank) := by
      calc (Fintype.card R * Fintype.card R) * (σ.rank * τ.rank)
          = (Fintype.card R * σ.rank) * (Fintype.card R * τ.rank) := by ring
        _ ≤ (Fintype.card C * τ.rank) * (Fintype.card C * σ.rank) := hmul
        _ = (Fintype.card C * Fintype.card C) * (σ.rank * τ.rank) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  nlinarith [hsq]

end CoreLemma

end QI

/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Core

/-!
# Quantum Singleton

The quantum Singleton bound (Knill–Laflamme bound): an `[[n, k, d]]_q` quantum code obeys
`n - k ≥ 2 (d - 1)`, stated here in the subtraction-free form `k + 2 * (d - 1) ≤ n`.
-/

open Matrix ComplexConjugate

namespace QI

variable {n q K : ℕ}

/-- Assemble a configuration of the `n` qudits out of its restrictions to `SA`, to `SB`,
and to the remaining qudits. -/
def assemble (SA SB : Finset (Fin n)) (a : SA → Fin q) (b : SB → Fin q)
    (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) : Fin n → Fin q :=
  fun i => if h : i ∈ SA then a ⟨i, h⟩ else if h' : i ∈ SB then b ⟨i, h'⟩ else
    c ⟨i, by simp [h, h']⟩

/-- Splitting the qudits into the three groups `SA`, `SB` and the rest. -/
def splitEquiv (SA SB : Finset (Fin n)) (hd : Disjoint SA SB) :
    (Fin n → Fin q) ≃ (SA → Fin q) × (SB → Fin q) × ({i : Fin n // i ∉ SA ∪ SB} → Fin q) where
  toFun x := (fun i => x i, fun i => x i, fun i => x i)
  invFun p := assemble SA SB p.1 p.2.1 p.2.2
  left_inv x := by
    funext i
    simp only [assemble]
    split <;> [skip; split] <;> rfl
  right_inv p := by
    obtain ⟨a, b, c⟩ := p
    have hb : ∀ i : SB, (i : Fin n) ∉ SA := fun i hi => Finset.disjoint_left.mp hd hi i.2
    ext i <;> simp only [assemble]
    · simp [i.2]
    · simp [hb i, i.2]
    · have h1 : (i : Fin n) ∉ SA := fun h => i.2 (Finset.mem_union_left _ h)
      have h2 : (i : Fin n) ∉ SB := fun h => i.2 (Finset.mem_union_right _ h)
      simp [h1, h2]

lemma assemble_restrict (SA SB : Finset (Fin n)) (a : SA → Fin q) (b : SB → Fin q)
    (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (fun i : SA => assemble SA SB a b c i) = a := by
  funext i; simp [assemble, i.2]

lemma assemble_agree_off (SA SB : Finset (Fin n)) (hd : Disjoint SA SB)
    (a a' : SA → Fin q) (b b' : SB → Fin q)
    (c c' : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (∀ i, i ∉ SA → assemble SA SB a b c i = assemble SA SB a' b' c' i) ↔ (b = b' ∧ c = c') := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have hi : (i : Fin n) ∉ SA := Finset.disjoint_right.mp hd i.2
      simpa [assemble, hi, i.2] using h i hi
    · funext i
      have h1 : (i : Fin n) ∉ SA := fun hx => i.2 (Finset.mem_union_left _ hx)
      have h2 : (i : Fin n) ∉ SB := fun hx => i.2 (Finset.mem_union_right _ hx)
      simpa [assemble, h1, h2] using h i h1
  · rintro ⟨rfl, rfl⟩ i hi
    simp [assemble, hi]

/-- An operator acting on the qudits in `S` only, extended by the identity to all `n` qudits. -/
def extendOp (S : Finset (Fin n)) (O : Matrix (S → Fin q) (S → Fin q) ℂ) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ :=
  fun x y => if (∀ i, i ∉ S → x i = y i) then O (fun i => x i) (fun i => y i) else 0

/-- A `q`-ary quantum code on `n` qudits with `K`-dimensional code space and distance at
least `d`.

`enc` is the encoding isometry from the `K`-dimensional logical space into the `n`-qudit
space `(ℂ^q)^{⊗ n}` (whose canonical basis is indexed by `Fin n → Fin q`), and `detects` is the
Knill–Laflamme error-detection condition: for every operator `O` acting on at most `d - 1`
qudits, `P O P = c(O) P`, where `P = enc * encᴴ` is the projection onto the code space;
equivalently `encᴴ * O * enc` is a multiple of the identity. -/
structure QCode (q n K d : ℕ) where
  /-- The encoding map. -/
  enc : Matrix (Fin n → Fin q) (Fin K) ℂ
  /-- The encoding map is an isometry. -/
  isometry : encᴴ * enc = 1
  /-- Knill–Laflamme error-detection condition for all errors of weight at most `d - 1`. -/
  detects : ∀ S : Finset (Fin n), S.card + 1 ≤ d → ∀ O : Matrix (S → Fin q) (S → Fin q) ℂ,
    ∃ c : ℂ, encᴴ * extendOp S O * enc = c • 1

/-- Restriction to `SB` of an assembled configuration. -/
lemma assemble_restrict_B (SA SB : Finset (Fin n)) (hd : Disjoint SA SB) (a : SA → Fin q)
    (b : SB → Fin q) (c : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (fun i : SB => assemble SA SB a b c i) = b := by
  funext i
  have hi : (i : Fin n) ∉ SA := Finset.disjoint_right.mp hd i.2
  simp [assemble, hi, i.2]

lemma assemble_agree_off_B (SA SB : Finset (Fin n)) (hd : Disjoint SA SB)
    (a a' : SA → Fin q) (b b' : SB → Fin q)
    (c c' : {i : Fin n // i ∉ SA ∪ SB} → Fin q) :
    (∀ i, i ∉ SB → assemble SA SB a b c i = assemble SA SB a' b' c' i) ↔ (a = a' ∧ c = c') := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · funext i
      have hi : (i : Fin n) ∉ SB := Finset.disjoint_left.mp hd i.2
      simpa [assemble, hi, i.2] using h i hi
    · funext i
      have h1 : (i : Fin n) ∉ SA := fun hx => i.2 (Finset.mem_union_left _ hx)
      have h2 : (i : Fin n) ∉ SB := fun hx => i.2 (Finset.mem_union_right _ hx)
      simpa [assemble, h1, h2] using h i h2
  · rintro ⟨rfl, rfl⟩ i hi
    by_cases hA : i ∈ SA <;> simp [assemble, hi, hA]

/-- Swapping the first two components of a triple. -/
def swap12 (X Y Z : Type*) : X × Y × Z ≃ Y × X × Z where
  toFun p := (p.2.1, p.1, p.2.2)
  invFun p := (p.2.1, p.1, p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The matrix element of a weight-restricted matrix unit, computed in a splitting of the
qudits into the region `S` carrying the operator and two further groups. -/
lemma entry_formula_gen {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (S : Finset (Fin n)) (asm : (S → Fin q) → B → C → (Fin n → Fin q))
    (hbij : Function.Bijective (fun p : (S → Fin q) × B × C => asm p.1 p.2.1 p.2.2))
    (hres : ∀ a b c, (fun i : S => asm a b c i) = a)
    (hagree : ∀ a a' b b' c c', (∀ i, i ∉ S → asm a b c i = asm a' b' c' i) ↔ (b = b' ∧ c = c'))
    (E : Matrix (Fin n → Fin q) (Fin K) ℂ) (a a' : S → Fin q) (i j : Fin K) :
    (Eᴴ * extendOp S (Matrix.single a a' 1) * E) i j
      = ∑ c, ∑ b, conj (E (asm a b c) i) * E (asm a' b c) j := by
  classical
  have h0 : (Eᴴ * extendOp S (Matrix.single a a' (1:ℂ)) * E) i j
      = ∑ y, ∑ x, (conj (E x i) * extendOp S (Matrix.single a a' (1:ℂ)) x y) * E y j := by
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have hval : ∀ (p1 r1 : S → Fin q) (p21 r21 : B) (p22 r22 : C),
      extendOp S (Matrix.single a a' (1:ℂ)) (asm p1 p21 p22) (asm r1 r21 r22)
        = if p21 = r21 then (if p22 = r22 then
            (if p1 = a then (if r1 = a' then (1:ℂ) else 0) else 0) else 0) else 0 := by
    intro p1 r1 p21 r21 p22 r22
    simp only [extendOp, hagree, hres, Matrix.single_apply]
    by_cases h : p21 = r21 ∧ p22 = r22
    · rw [if_pos h, if_pos h.1, if_pos h.2]
      by_cases h1 : p1 = a
      · by_cases h2 : r1 = a'
        · simp [h1, h2]
        · simp [h1, h2, Ne.symm h2]
      · simp [h1, Ne.symm h1]
    · rw [if_neg h]
      rcases not_and_or.mp h with h' | h'
      · simp [h']
      · simp [h']
  set e := Equiv.ofBijective _ hbij with he
  have hea : ∀ p : (S → Fin q) × B × C, e p = asm p.1 p.2.1 p.2.2 := fun p => rfl
  rw [h0, ← Equiv.sum_comp e (fun y => ∑ x, (conj (E x i) *
      extendOp S (Matrix.single a a' (1:ℂ)) x y) * E y j)]
  have inner : ∀ r : (S → Fin q) × B × C,
      (∑ x, (conj (E x i) * extendOp S (Matrix.single a a' (1:ℂ)) x (e r)) * E (e r) j)
        = if r.1 = a' then conj (E (asm a r.2.1 r.2.2) i) * E (asm a' r.2.1 r.2.2) j else 0 := by
    intro r
    rw [← Equiv.sum_comp e (fun x => (conj (E x i) *
      extendOp S (Matrix.single a a' (1:ℂ)) x (e r)) * E (e r) j)]
    simp only [hea, hval, Fintype.sum_prod_type]
    simp only [mul_ite, ite_mul, zero_mul, mul_zero]
    by_cases hr : r.1 = a' <;> simp [hr]
  simp only [inner, Fintype.sum_prod_type]
  have hpull : ∀ r1 : S → Fin q,
      (∑ r21 : B, ∑ r22 : C, (if r1 = a' then
          conj (E (asm a r21 r22) i) * E (asm a' r21 r22) j else 0))
        = if r1 = a' then (∑ r21 : B, ∑ r22 : C,
            conj (E (asm a r21 r22) i) * E (asm a' r21 r22) j) else 0 := by
    intro r1; split <;> simp
  rw [Finset.sum_congr rfl (fun r1 _ => hpull r1), Finset.sum_ite_eq' Finset.univ a',
    if_pos (Finset.mem_univ _), Finset.sum_comm]

/-- The code dimension is at most `q ^ (n - |SA| - |SB|)` whenever `SA` and `SB` are two
disjoint sets of at most `d - 1` qudits. -/
lemma dim_le_of_two_regions {d : ℕ} (Q : QCode q n K d) (hK : 0 < K)
    (SA SB : Finset (Fin n)) (hd : Disjoint SA SB)
    (hSA : SA.card + 1 ≤ d) (hSB : SB.card + 1 ≤ d) :
    K ≤ q ^ (n - SA.card - SB.card) := by
  classical
  set f : Fin K → (SA → Fin q) → (SB → Fin q) → ({i : Fin n // i ∉ SA ∪ SB} → Fin q) → ℂ :=
    fun i a b c => Q.enc (assemble SA SB a b c) i with hfdef
  choose scA hscA using fun (a a' : SA → Fin q) => Q.detects SA hSA (Matrix.single a a' 1)
  choose scB hscB using fun (b b' : SB → Fin q) => Q.detects SB hSB (Matrix.single b b' 1)
  have hbijA : Function.Bijective
      (fun p : (SA → Fin q) × (SB → Fin q) × ({i : Fin n // i ∉ SA ∪ SB} → Fin q) =>
        assemble SA SB p.1 p.2.1 p.2.2) := (splitEquiv SA SB hd).symm.bijective
  have hbijB : Function.Bijective
      (fun p : (SB → Fin q) × (SA → Fin q) × ({i : Fin n // i ∉ SA ∪ SB} → Fin q) =>
        assemble SA SB p.2.1 p.1 p.2.2) :=
    ((swap12 _ _ _).trans (splitEquiv SA SB hd).symm).bijective
  -- decoupling of the logical register from the region `SA`
  have hA : ∀ i j a a', (∑ c, ∑ b, f i a b c * conj (f j a' b c))
      = (if i = j then (1 : ℂ) else 0) * conj (scA a a') := by
    intro i j a a'
    have h1 := congrFun (congrFun (hscA a a') i) j
    rw [entry_formula_gen SA (assemble SA SB) hbijA (assemble_restrict SA SB)
      (fun a a' b b' c c' => assemble_agree_off SA SB hd a a' b b' c c') Q.enc a a' i j] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_sum, map_mul, Complex.conj_conj, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_one,
      mul_zero] at h2
    rw [hfdef]
    simpa using h2
  -- decoupling of the logical register from the region `SB`
  have hB : ∀ i j b b', (∑ c, ∑ a, f i a b c * conj (f j a b' c))
      = (if i = j then (1 : ℂ) else 0) * conj (scB b b') := by
    intro i j b b'
    have h1 := congrFun (congrFun (hscB b b') i) j
    rw [entry_formula_gen SB (fun b a c => assemble SA SB a b c) hbijB
      (fun b a c => assemble_restrict_B SA SB hd a b c)
      (fun b b' a a' c c' => assemble_agree_off_B SA SB hd a a' b b' c c') Q.enc b b' i j] at h1
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_sum, map_mul, Complex.conj_conj, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, apply_ite (starRingEnd ℂ), map_zero, mul_ite, mul_one,
      mul_zero] at h2
    rw [hfdef]
    simpa using h2
  -- the encoding does not vanish identically
  have hex : ∃ i a b c, f i a b c ≠ 0 := by
    obtain ⟨i⟩ : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
    by_contra hcon
    push_neg at hcon
    have hzero : ∀ x : Fin n → Fin q, Q.enc x i = 0 := by
      intro x
      obtain ⟨p, hp⟩ := hbijA.2 x
      have := hcon i p.1 p.2.1 p.2.2
      rw [hfdef] at this
      simpa [hp] using this
    have h1 : (Q.encᴴ * Q.enc) i i = 1 := by rw [Q.isometry]; simp
    rw [Matrix.mul_apply] at h1
    simp only [Matrix.conjTranspose_apply, hzero, mul_zero,
      Finset.sum_const_zero] at h1
    exact zero_ne_one h1
  have hcard := QI.card_le_of_decoupled f (fun a a' => conj (scA a a'))
    (fun b b' => conj (scB b b')) hA hB hex
  rw [Fintype.card_fin] at hcard
  have hcardC : Fintype.card ({i : Fin n // i ∉ SA ∪ SB} → Fin q)
      = q ^ (n - SA.card - SB.card) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_subtype_compl]
    congr 1
    rw [Fintype.card_subtype, Finset.filter_mem_eq_inter]
    simp [Finset.card_union_of_disjoint hd]
    omega
  rw [hcardC] at hcard
  exact hcard

/-- The dimension of a code is at most the dimension of the ambient space. -/
lemma dim_le_ambient {d : ℕ} (Q : QCode q n K d) : K ≤ q ^ n := by
  have h2 := Matrix.rank_mul_le_right Q.encᴴ Q.enc
  rw [Q.isometry, Matrix.rank_one] at h2
  have h3 : Q.enc.rank ≤ Fintype.card (Fin n → Fin q) := Matrix.rank_le_card_height Q.enc
  simp only [Fintype.card_fun, Fintype.card_fin] at h3
  simpa using h2.trans h3

/-- **Quantum Singleton bound** (Knill–Laflamme bound).
An `[[n, k, d]]_q` quantum code with `q ≥ 2`, `k ≥ 1` and distance at least `d` satisfies
`n - k ≥ 2 (d - 1)`, here in the subtraction-free form `k + 2 * (d - 1) ≤ n`. -/
theorem quantum_singleton {k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) (Q : QCode q n (q ^ k) d) :
    k + 2 * (d - 1) ≤ n := by
  have hq0 : 0 < q := by omega
  have hK : 0 < q ^ k := Nat.pow_pos hq0
  rcases Nat.eq_zero_or_pos d with rfl | hd1
  · have h := dim_le_ambient Q
    have : k ≤ n := (Nat.pow_le_pow_iff_right hq).mp h
    omega
  set m := d - 1 with hm
  by_cases hcase : 2 * m ≤ n
  · obtain ⟨SA, -, hSA⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := m)
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    have hcompl : ((Finset.univ : Finset (Fin n)) \ SA).card = n - m := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hSA]
      simp
    obtain ⟨SB, hsub, hSB⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n)) \ SA) (n := m) (by rw [hcompl]; omega)
    have hdisj : Disjoint SA SB :=
      Finset.disjoint_left.mpr fun x hx hxB => (Finset.mem_sdiff.mp (hsub hxB)).2 hx
    have hle := dim_le_of_two_regions Q hK SA SB hdisj (by omega) (by omega)
    rw [hSA, hSB] at hle
    have : k ≤ n - m - m := (Nat.pow_le_pow_iff_right hq).mp hle
    omega
  · exfalso
    obtain ⟨SA, -, hSA⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n))) (n := min m n)
      (by simp only [Finset.card_univ, Fintype.card_fin]; omega)
    have hcompl : ((Finset.univ : Finset (Fin n)) \ SA).card = n - min m n := by
      rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl, hSA]
      simp
    obtain ⟨SB, hsub, hSB⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin n)) \ SA) (n := n - min m n) (by rw [hcompl])
    have hdisj : Disjoint SA SB :=
      Finset.disjoint_left.mpr fun x hx hxB => (Finset.mem_sdiff.mp (hsub hxB)).2 hx
    have hle := dim_le_of_two_regions Q hK SA SB hdisj (by omega) (by omega)
    rw [hSA, hSB] at hle
    have hz : n - min m n - (n - min m n) = 0 := by omega
    rw [hz, pow_zero] at hle
    have : k ≤ 0 := (Nat.pow_le_pow_iff_right hq).mp (by simpa using hle)
    omega

/-- Extending an operator supported on no qudits at all just rescales the identity. -/
lemma extendOp_empty (O : Matrix ((∅ : Finset (Fin n)) → Fin q) ((∅ : Finset (Fin n)) → Fin q) ℂ)
    (e : (∅ : Finset (Fin n)) → Fin q) :
    extendOp (∅ : Finset (Fin n)) O = (O e e) • (1 : Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ) := by
  classical
  ext x y
  have hsub : ∀ g h : (∅ : Finset (Fin n)) → Fin q, g = h := by
    intro g h; funext i; exact (Finset.notMem_empty _ i.2).elim
  by_cases hxy : x = y
  · subst hxy
    simp only [extendOp, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    rw [if_pos (by simp), hsub (fun i : (∅ : Finset (Fin n)) => x i) e]
  · have hne : ¬ (∀ i, i ∉ (∅ : Finset (Fin n)) → x i = y i) := by
      intro h; exact hxy (funext fun i => h i (Finset.notMem_empty i))
    simp only [extendOp, if_neg hne, Matrix.smul_apply, Matrix.one_apply_ne hxy, smul_eq_mul,
      mul_zero]

/-- The unencoded encoding map on `n` qudits. -/
def trivialEnc (q n : ℕ) : Matrix (Fin n → Fin q) (Fin (q ^ n)) ℂ :=
  fun x i => if x = finFunctionFinEquiv.symm i then 1 else 0

lemma trivialEnc_isometry (q n : ℕ) : (trivialEnc q n)ᴴ * trivialEnc q n = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [trivialEnc, Matrix.conjTranspose_apply, RCLike.star_def,
    apply_ite (starRingEnd ℂ), map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (finFunctionFinEquiv.symm i)]
  by_cases h : i = j
  · subst h; simp
  · have hne : ¬ (finFunctionFinEquiv.symm i = finFunctionFinEquiv.symm j) :=
      fun hx => h (finFunctionFinEquiv.symm.injective hx)
    simp [h, hne]

/-- The trivial (unencoded) code `[[n, n, 1]]_q`, which shows that the definition of `QCode`
is satisfiable; the bound then reads `n + 2 * 0 ≤ n`. -/
def trivialCode (q n : ℕ) : QCode q n (q ^ n) 1 where
  enc := trivialEnc q n
  isometry := trivialEnc_isometry q n
  detects := by
    classical
    intro S hS O
    obtain rfl : S = ∅ := Finset.card_eq_zero.mp (by omega)
    refine ⟨O (fun i => (Finset.notMem_empty _ i.2).elim)
      (fun i => (Finset.notMem_empty _ i.2).elim), ?_⟩
    rw [extendOp_empty O (fun i => (Finset.notMem_empty _ i.2).elim), Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, trivialEnc_isometry]

/-- The encoding into a fixed basis state, i.e. a one-dimensional code space. -/
def pointEnc (q n : ℕ) (hq : 0 < q) : Matrix (Fin n → Fin q) (Fin 1) ℂ :=
  fun x _ => if x = (fun _ => (⟨0, hq⟩ : Fin q)) then 1 else 0

lemma pointEnc_isometry (q n : ℕ) (hq : 0 < q) :
    (pointEnc q n hq)ᴴ * pointEnc q n hq = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [pointEnc, Matrix.conjTranspose_apply, RCLike.star_def, apply_ite (starRingEnd ℂ),
    map_one, map_zero, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (fun _ => (⟨0, hq⟩ : Fin q))]
  simp [Matrix.one_apply, Subsingleton.elim i j]

/-- A one-dimensional code space (`K = 1`, i.e. `k = 0`) satisfies the Knill–Laflamme
condition for errors of *every* weight. -/
def pointCode (q n d : ℕ) (hq : 0 < q) : QCode q n 1 d where
  enc := pointEnc q n hq
  isometry := pointEnc_isometry q n hq
  detects := by
    intro S _ O
    refine ⟨((pointEnc q n hq)ᴴ * extendOp S O * pointEnc q n hq) 0 0, ?_⟩
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simp

/-- The hypothesis `1 ≤ k` in `quantum_singleton` cannot be dropped: the one-dimensional code
on a single qubit has distance at least `2`, and `0 + 2 * (2 - 1) ≤ 1` is false. -/
theorem singleton_needs_pos_dim : ∃ _Q : QCode 2 1 (2 ^ 0) 2, ¬ (0 + 2 * (2 - 1) ≤ 1) :=
  ⟨pointCode 2 1 2 (by norm_num), by decide⟩

end QI

