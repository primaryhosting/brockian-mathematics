/-
# Huang Sensitivity
Category: Frontier — Fields Medal Work
Target: Frontier.huang_sensitivity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The hypercube and its signed adjacency operator -/

variable {n : ℕ}

/-- Flip the `i`-th coordinate of a point of the Boolean hypercube. -/
def flipAt (x : Fin n → Bool) (i : Fin n) : Fin n → Bool := Function.update x i (!x i)

/-- The sign attached to the hypercube edge `{x, flipAt x i}` in Huang's signed
adjacency matrix: `(-1)` to the number of `true` coordinates of `x` below `i`. -/
def sgn (x : Fin n → Bool) (i : Fin n) : ℝ :=
  (-1) ^ (Finset.univ.filter (fun j => j < i ∧ x j = true)).card

@[simp] lemma flipAt_apply_self (x : Fin n → Bool) (i : Fin n) : flipAt x i i = !x i := by
  simp [flipAt]

lemma flipAt_apply_of_ne (x : Fin n → Bool) {i j : Fin n} (h : j ≠ i) :
    flipAt x i j = x j := by
  simp [flipAt, Function.update_of_ne h]

@[simp] lemma flipAt_flipAt_self (x : Fin n → Bool) (i : Fin n) :
    flipAt (flipAt x i) i = x := by
  funext j
  by_cases h : j = i
  · subst h; simp
  · simp [flipAt_apply_of_ne _ h]

lemma flipAt_ne (x : Fin n → Bool) (i : Fin n) : flipAt x i ≠ x := by
  intro h
  have := congrFun h i
  simp at this

lemma flipAt_comm (x : Fin n → Bool) {i j : Fin n} (h : i ≠ j) :
    flipAt (flipAt x i) j = flipAt (flipAt x j) i := by
  funext k
  by_cases hk : k = i <;> by_cases hk2 : k = j <;>
    simp_all [flipAt, Function.update_apply]

lemma sgn_mul_self (x : Fin n → Bool) (i : Fin n) : sgn x i * sgn x i = 1 := by
  simp [sgn, ← pow_add, ← two_mul, pow_mul]

lemma sgn_ne_zero (x : Fin n → Bool) (i : Fin n) : sgn x i ≠ 0 := by
  intro h
  have := sgn_mul_self x i
  rw [h] at this
  norm_num at this

lemma abs_sgn (x : Fin n → Bool) (i : Fin n) : |sgn x i| = 1 := by
  simp [sgn, abs_pow]

/-- Flipping a coordinate `i` does not change the sign at a smaller index `j`. -/
lemma sgn_flipAt_of_lt {x : Fin n → Bool} {i j : Fin n} (h : j < i) :
    sgn (flipAt x i) j = sgn x j := by
  have hfilter : Finset.univ.filter (fun k => k < j ∧ flipAt x i k = true)
      = Finset.univ.filter (fun k => k < j ∧ x k = true) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt (hk.trans h))] at hx⟩
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt (hk.trans h))]⟩
  unfold sgn
  rw [hfilter]

/-- Flipping a coordinate `i` reverses the sign at a larger index `j`. -/
lemma sgn_flipAt_of_gt {x : Fin n → Bool} {i j : Fin n} (h : i < j) :
    sgn (flipAt x i) j = - sgn x j := by
  set T : Finset (Fin n) := Finset.univ.filter (fun k => k < j ∧ x k = true) with hT
  set T' : Finset (Fin n) := Finset.univ.filter (fun k => k < j ∧ flipAt x i k = true) with hT'
  have key : ∀ k : Fin n, k ≠ i → (k ∈ T ↔ k ∈ T') := by
    intro k hk
    simp only [hT, hT', Finset.mem_filter, Finset.mem_univ, true_and,
      flipAt_apply_of_ne _ hk]
  by_cases hx : x i = true
  · have hiT : i ∈ T := by simp [hT, h, hx]
    have : T' = T.erase i := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hT', hx, h]
      · simp only [Finset.mem_erase, hk, ne_eq, not_false_eq_true, true_and]
        exact (key k hk).symm
    have hcard : T'.card = T.card - 1 := by rw [this, Finset.card_erase_of_mem hiT]
    have hpos : 1 ≤ T.card := Finset.card_pos.2 ⟨i, hiT⟩
    unfold sgn
    rw [← hT, ← hT', hcard]
    obtain ⟨m, hm⟩ : ∃ m, T.card = m + 1 := ⟨T.card - 1, by omega⟩
    rw [hm]
    simp [pow_succ]
  · have hx' : x i = false := by simpa using hx
    have hiT : i ∉ T := by simp [hT, hx']
    have : T' = insert i T := by
      ext k
      by_cases hk : k = i
      · subst hk
        simp [hT', hx', h]
      · simp only [Finset.mem_insert, hk, false_or]
        exact (key k hk).symm
    have hcard : T'.card = T.card + 1 := by rw [this, Finset.card_insert_of_notMem hiT]
    unfold sgn
    rw [← hT, ← hT', hcard]
    simp [pow_succ]

lemma sgn_flipAt_self (x : Fin n → Bool) (i : Fin n) : sgn (flipAt x i) i = sgn x i := by
  have hfilter : Finset.univ.filter (fun k => k < i ∧ flipAt x i k = true)
      = Finset.univ.filter (fun k => k < i ∧ x k = true) := by
    apply Finset.filter_congr
    intro k _
    constructor
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt hk)] at hx⟩
    · rintro ⟨hk, hx⟩
      exact ⟨hk, by rwa [flipAt_apply_of_ne _ (ne_of_lt hk)]⟩
  unfold sgn
  rw [hfilter]


/-! ## Huang's signed adjacency operator -/

/-- Huang's signed adjacency operator of the `n`-dimensional hypercube, acting on
real-valued functions on `Fin n → Bool`. -/
def hop (n : ℕ) : ((Fin n → Bool) → ℝ) →ₗ[ℝ] ((Fin n → Bool) → ℝ) where
  toFun v := fun x => ∑ i, sgn x i * v (flipAt x i)
  map_add' u v := by
    funext x
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext x
    simp [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

lemma hop_apply (v : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    hop n v x = ∑ i, sgn x i * v (flipAt x i) := rfl

/-- The fundamental identity `A² = n • I` for Huang's signed adjacency operator. -/
theorem hop_hop (v : (Fin n → Bool) → ℝ) (x : Fin n → Bool) :
    hop n (hop n v) x = (n : ℝ) * v x := by
  set G : Fin n × Fin n → ℝ :=
    fun p => sgn x p.1 * sgn (flipAt x p.1) p.2 * v (flipAt (flipAt x p.1) p.2) with hG
  have hdiag : ∀ i : Fin n, G (i, i) = v x := by
    intro i
    simp only [hG, sgn_flipAt_self, flipAt_flipAt_self]
    rw [sgn_mul_self, one_mul]
  have hanti : ∀ p : Fin n × Fin n, p.1 ≠ p.2 → G p + G (Prod.swap p) = 0 := by
    rintro ⟨i, j⟩ hij
    simp only [hG, Prod.swap_prod_mk] at *
    rcases lt_or_gt_of_ne hij with h | h
    · rw [sgn_flipAt_of_gt h, sgn_flipAt_of_lt h, flipAt_comm x hij]
      ring
    · rw [sgn_flipAt_of_lt h, sgn_flipAt_of_gt h, flipAt_comm x hij]
      ring
  have hexpand : hop n (hop n v) x = ∑ p : Fin n × Fin n, G p := by
    rw [hop_apply]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hop_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [hG, mul_assoc]
  have hswap : ∑ p : Fin n × Fin n, G p = ∑ p : Fin n × Fin n, G (Prod.swap p) :=
    (Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ (fun p => rfl)).symm
  have hdouble : (2 : ℝ) * ∑ p : Fin n × Fin n, G p
      = ∑ p : Fin n × Fin n, (G p + G (Prod.swap p)) := by
    rw [Finset.sum_add_distrib, ← hswap]
    ring
  have hpoint : ∀ p : Fin n × Fin n,
      G p + G (Prod.swap p) = if p.1 = p.2 then 2 * v x else 0 := by
    rintro ⟨i, j⟩
    by_cases h : i = j
    · subst h
      simp only [Prod.swap_prod_mk, hdiag i]
      rw [if_pos trivial]
      ring
    · rw [if_neg h]
      exact hanti (i, j) h
  have hsum : ∑ p : Fin n × Fin n, (G p + G (Prod.swap p)) = 2 * ((n : ℝ) * v x) := by
    rw [Finset.sum_congr rfl fun p _ => hpoint p]
    rw [Fintype.sum_prod_type]
    have : ∀ i : Fin n, (∑ j : Fin n, if i = j then 2 * v x else 0) = 2 * v x := by
      intro i
      simp
    rw [Finset.sum_congr rfl fun i _ => this i]
    simp [Finset.sum_const]
    ring
  have := hdouble.trans hsum
  rw [hexpand]
  linarith [this]

end Frontier

