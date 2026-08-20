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
