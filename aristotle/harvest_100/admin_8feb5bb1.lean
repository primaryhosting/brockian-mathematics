import Mathlib

/-!
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
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

set_option grind.warning false

namespace Frontier

open Finset
open scoped Matrix

/-! ## The Boolean hypercube -/

/-- Vertices of the `n`-dimensional Boolean hypercube. -/
abbrev Cube (n : ℕ) := Fin n → Bool

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a hypercube vertex. -/
def flipAt (x : Cube n) (i : Fin n) : Cube n := Function.update x i (!x i)

@[simp] lemma flipAt_self (x : Cube n) (i : Fin n) : flipAt x i i = !x i := by
  simp [flipAt]

lemma flipAt_of_ne (x : Cube n) {i j : Fin n} (h : j ≠ i) : flipAt x i j = x j := by
  simp [flipAt, h]

@[simp] lemma flipAt_flipAt (x : Cube n) (i : Fin n) : flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipAt_of_ne _ h]

lemma flipAt_ne (x : Cube n) (i : Fin n) : flipAt x i ≠ x := by
  intro h
  have := congrArg (fun z => z i) h
  simp at this

lemma flipAt_left_injective (x : Cube n) {i k : Fin n} (h : flipAt x i = flipAt x k) : i = k := by
  by_contra hik
  have h1 : flipAt x i i = flipAt x k i := congrArg (fun z => z i) h
  rw [flipAt_self, flipAt_of_ne _ hik] at h1
  simp at h1

/-! ## Huang's signed adjacency matrix -/

/-- The number of coordinates above `i` at which `x` is `true`. -/
def hcount (x : Cube n) (i : Fin n) : ℕ := #{j ∈ Finset.univ | i < j ∧ x j = true}

/-- The sign attached to the hypercube edge `{x, flipAt x i}` in Huang's matrix. -/
def hsign (x : Cube n) (i : Fin n) : ℝ := (-1 : ℝ) ^ hcount x i

lemma hsign_sq (x : Cube n) (i : Fin n) : hsign x i * hsign x i = 1 := by
  simp [hsign, ← pow_add, ← two_mul, pow_mul]

lemma abs_hsign (x : Cube n) (i : Fin n) : |hsign x i| = 1 := by
  simp [hsign, abs_pow]

lemma hcount_flipAt_self (x : Cube n) (i : Fin n) : hcount (flipAt x i) i = hcount x i := by
  unfold hcount
  congr 1
  apply Finset.filter_congr
  intro j _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (ne_of_gt h1)] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (ne_of_gt h1)]⟩

lemma hsign_flipAt_self (x : Cube n) (i : Fin n) : hsign (flipAt x i) i = hsign x i := by
  simp [hsign, hcount_flipAt_self]

lemma hcount_flipAt_gt (x : Cube n) {i k : Fin n} (h : i < k) :
    hcount (flipAt x i) k = hcount x k := by
  unfold hcount
  congr 1
  apply Finset.filter_congr
  intro j _
  have hj : ∀ _hjk : k < j, j ≠ i := fun hjk => ne_of_gt (lt_trans h hjk)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (hj h1)] at h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rwa [flipAt_of_ne _ (hj h1)]⟩

lemma hsign_flipAt_gt (x : Cube n) {i k : Fin n} (h : i < k) :
    hsign (flipAt x i) k = hsign x k := by
  simp [hsign, hcount_flipAt_gt x h]

lemma hcount_flipAt_lt_of_true (x : Cube n) {i k : Fin n} (h : i < k) (hk : x k = true) :
    hcount x i = hcount (flipAt x k) i + 1 := by
  unfold hcount
  have hmem : k ∉ ({j ∈ Finset.univ | i < j ∧ flipAt x k j = true} : Finset (Fin n)) := by
    simp [hk]
  have hset : ({j ∈ Finset.univ | i < j ∧ x j = true} : Finset (Fin n))
      = insert k ({j ∈ Finset.univ | i < j ∧ flipAt x k j = true} : Finset (Fin n)) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hjk : j = k
      · exact Or.inl hjk
      · exact Or.inr ⟨h1, by rwa [flipAt_of_ne _ hjk]⟩
    · rintro (rfl | ⟨h1, h2⟩)
      · exact ⟨h, hk⟩
      · by_cases hjk : j = k
        · subst hjk; simp [hk] at h2
        · rw [flipAt_of_ne _ hjk] at h2; exact ⟨h1, h2⟩
  rw [hset, Finset.card_insert_of_notMem hmem]

lemma hsign_flipAt_lt (x : Cube n) {i k : Fin n} (h : i < k) :
    hsign (flipAt x k) i = - hsign x i := by
  by_cases hk : x k = true
  · have hc := hcount_flipAt_lt_of_true x h hk
    simp only [hsign, hc, pow_succ]
    ring
  · have hk' : (flipAt x k) k = true := by
      simp only [Bool.not_eq_true] at hk
      simp [hk]
    have hc := hcount_flipAt_lt_of_true (flipAt x k) h hk'
    rw [flipAt_flipAt] at hc
    simp only [hsign, hc, pow_succ]
    ring

lemma flipAt_comm (x : Cube n) {i k : Fin n} (h : i ≠ k) :
    flipAt (flipAt x i) k = flipAt (flipAt x k) i := by
  funext j
  by_cases hji : j = i
  · subst hji
    rw [flipAt_of_ne _ h, flipAt_self, flipAt_self, flipAt_of_ne _ h]
  · by_cases hjk : j = k
    · subst hjk
      rw [flipAt_self, flipAt_of_ne _ (Ne.symm h), flipAt_of_ne _ (Ne.symm h), flipAt_self]
    · rw [flipAt_of_ne _ hjk, flipAt_of_ne _ hji, flipAt_of_ne _ hji, flipAt_of_ne _ hjk]

lemma flipAt_flipAt_ne (x : Cube n) {i k : Fin n} (h : k ≠ i) : flipAt (flipAt x i) k ≠ x := by
  intro hc
  have := congrArg (fun z => z k) hc
  simp only [flipAt_self, flipAt_of_ne _ h] at this
  simp at this

lemma hsign_pair_cancel (x : Cube n) {i k : Fin n} (h : i ≠ k) :
    hsign x i * hsign (flipAt x i) k + hsign x k * hsign (flipAt x k) i = 0 := by
  rcases lt_or_gt_of_ne h with hlt | hlt
  · rw [hsign_flipAt_gt x hlt, hsign_flipAt_lt x hlt]
    ring
  · rw [hsign_flipAt_gt x hlt, hsign_flipAt_lt x hlt]
    ring

/-- Huang's signed adjacency matrix of the `n`-dimensional hypercube. -/
def huangMatrix (n : ℕ) : Matrix (Cube n) (Cube n) ℝ :=
  fun x y => ∑ i : Fin n, if flipAt x i = y then hsign x i else 0

lemma huangMatrix_row_sum (g : Cube n → ℝ) (x : Cube n) :
    ∑ y, huangMatrix n x y * g y = ∑ i, hsign x i * g (flipAt x i) := by
  simp only [huangMatrix, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (flipAt x i) (fun y => hsign x i * g y)]
  simp

lemma huangMatrix_mulVec (v : Cube n → ℝ) (x : Cube n) :
    (huangMatrix n *ᵥ v) x = ∑ i, hsign x i * v (flipAt x i) := by
  exact huangMatrix_row_sum v x

lemma huangMatrix_apply_flip (x z : Cube n) (i : Fin n) :
    huangMatrix n (flipAt x i) z
      = ∑ k, if flipAt (flipAt x i) k = z then hsign (flipAt x i) k else 0 := rfl

lemma huangMatrix_flip_self (x : Cube n) (i : Fin n) :
    huangMatrix n (flipAt x i) x = hsign x i := by
  rw [huangMatrix_apply_flip]
  rw [Finset.sum_eq_single i]
  · rw [if_pos (flipAt_flipAt x i), hsign_flipAt_self]
  · intro k _ hk
    rw [if_neg (flipAt_flipAt_ne x hk)]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma huang_offdiag_term_diag (x z : Cube n) (hz : ¬ z = x) (i : Fin n) :
    (if flipAt (flipAt x i) i = z then hsign x i * hsign (flipAt x i) i else 0) = 0 := by
  rw [flipAt_flipAt, if_neg (fun h => hz h.symm)]

lemma huang_offdiag_sum (x z : Cube n) (hz : ¬ z = x) :
    ∑ p : Fin n × Fin n,
      (if flipAt (flipAt x p.1) p.2 = z then hsign x p.1 * hsign (flipAt x p.1) p.2 else 0)
      = 0 := by
  refine Finset.sum_ninvolution (fun p => (p.2, p.1)) ?_ ?_ (fun _ => Finset.mem_univ _)
    (fun _ => rfl)
  · rintro ⟨i, k⟩
    show (if flipAt (flipAt x i) k = z then hsign x i * hsign (flipAt x i) k else 0)
        + (if flipAt (flipAt x k) i = z then hsign x k * hsign (flipAt x k) i else 0) = 0
    by_cases hik : i = k
    · subst hik
      rw [huang_offdiag_term_diag x z hz i, add_zero]
    · by_cases hc : flipAt (flipAt x i) k = z
      · have hc' : flipAt (flipAt x k) i = z := by rw [← flipAt_comm x hik]; exact hc
        rw [if_pos hc, if_pos hc']
        exact hsign_pair_cancel x hik
      · have hc' : ¬ flipAt (flipAt x k) i = z := by
          rw [← flipAt_comm x hik]; exact hc
        rw [if_neg hc, if_neg hc', add_zero]
  · rintro ⟨i, k⟩ hne hcon
    rw [Prod.ext_iff] at hcon
    obtain ⟨h1, -⟩ := hcon
    exact hne (by
      simp only at h1 ⊢
      subst h1
      exact huang_offdiag_term_diag x z hz k)

lemma huangMatrix_sq :
    huangMatrix n * huangMatrix n = (n : ℝ) • (1 : Matrix (Cube n) (Cube n) ℝ) := by
  ext x z
  rw [Matrix.mul_apply, huangMatrix_row_sum (fun y => huangMatrix n y z) x]
  by_cases hz : z = x
  · subst hz
    have hterm : ∀ i : Fin n, hsign z i * huangMatrix n (flipAt z i) z = 1 := by
      intro i
      rw [huangMatrix_flip_self, hsign_sq]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    simp
  · have hrew : ∑ i, hsign x i * huangMatrix n (flipAt x i) z
        = ∑ p : Fin n × Fin n,
            (if flipAt (flipAt x p.1) p.2 = z then hsign x p.1 * hsign (flipAt x p.1) p.2
              else 0) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [huangMatrix_apply_flip, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      split <;> simp
    rw [hrew, huang_offdiag_sum x z hz]
    rw [Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hz)]
    simp

lemma huangMatrix_diag (x : Cube n) : huangMatrix n x x = 0 := by
  unfold huangMatrix
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg (flipAt_ne x i)]

lemma huangMatrix_trace : Matrix.trace (huangMatrix n) = 0 := by
  simp [Matrix.trace, Matrix.diag, huangMatrix_diag]

end Frontier

