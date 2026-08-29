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


