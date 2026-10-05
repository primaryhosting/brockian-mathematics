/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

variable {V : Type*} [Fintype V]

/-- The bilinear form `xᵀ A y` associated to a "weight matrix" `A : V → V → ℝ`. -/
def bilForm (A : V → V → ℝ) (x y : V → ℝ) : ℝ := ∑ i, ∑ j, A i j * x i * y j

lemma bilForm_eq_sum_mul (A : V → V → ℝ) (x y : V → ℝ) :
    bilForm A x y = ∑ i, x i * ∑ j, A i j * y j := by
  simp only [bilForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bilForm_add_add (A : V → V → ℝ) (u v : V → ℝ) :
    bilForm A (fun i => u i + v i) (fun i => u i + v i)
      = bilForm A u u + bilForm A u v + bilForm A v u + bilForm A v v := by
  simp only [bilForm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bilForm_sub_sub (A : V → V → ℝ) (u v : V → ℝ) :
    bilForm A (fun i => u i - v i) (fun i => u i - v i)
      = bilForm A u u - bilForm A u v - bilForm A v u + bilForm A v v := by
  simp only [bilForm, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bilForm_symm (A : V → V → ℝ) (hsymm : ∀ i j, A i j = A j i) (x y : V → ℝ) :
    bilForm A x y = bilForm A y x := by
  simp only [bilForm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hsymm j i]; ring

lemma bilForm_smul_left (A : V → V → ℝ) (c : ℝ) (x y : V → ℝ) :
    bilForm A (fun i => c * x i) y = c * bilForm A x y := by
  simp only [bilForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma bilForm_smul_right (A : V → V → ℝ) (c : ℝ) (x y : V → ℝ) :
    bilForm A x (fun i => c * y i) = c * bilForm A x y := by
  simp only [bilForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Polarization: a bound on the quadratic form on the "balanced" subspace gives a bound on
the bilinear form, in the symmetric averaged form. -/
lemma bilForm_bound_avg (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ i j, A i j = A j i)
    (hlam : ∀ x : V → ℝ, (∑ i, x i = 0) → |bilForm A x x| ≤ lam * ∑ i, (x i) ^ 2)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bilForm A x y| ≤ lam / 2 * ((∑ i, (x i) ^ 2) + ∑ i, (y i) ^ 2) := by
  have hadd : ∑ i, (x i + y i) = 0 := by
    rw [Finset.sum_add_distrib, hx, hy]; ring
  have hsub : ∑ i, (x i - y i) = 0 := by
    rw [Finset.sum_sub_distrib, hx, hy]; ring
  have h1 := hlam (fun i => x i + y i) hadd
  have h2 := hlam (fun i => x i - y i) hsub
  rw [bilForm_add_add] at h1
  rw [bilForm_sub_sub] at h2
  rw [bilForm_symm A hsymm y x] at h1 h2
  have hsq : (∑ i, (x i + y i) ^ 2) + ∑ i, (x i - y i) ^ 2
      = 2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2 := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have key : |4 * bilForm A x y| ≤ lam * (2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2) := by
    have : (4 : ℝ) * bilForm A x y =
        (bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y)
          - (bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y) := by ring
    rw [this]
    calc |(bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y)
            - (bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y)|
          ≤ |bilForm A x x + bilForm A x y + bilForm A x y + bilForm A y y|
            + |bilForm A x x - bilForm A x y - bilForm A x y + bilForm A y y| := abs_sub _ _
      _ ≤ lam * (∑ i, (x i + y i) ^ 2) + lam * ∑ i, (x i - y i) ^ 2 := add_le_add h1 h2
      _ = lam * (2 * (∑ i, (x i) ^ 2) + 2 * ∑ i, (y i) ^ 2) := by rw [← mul_add, hsq]
  rw [abs_mul] at key
  simp only [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)] at key
  linarith [key]

/-- The bilinear form is bounded by `lam` times the product of the norms, on balanced vectors. -/
lemma bilForm_bound_norms (A : V → V → ℝ) (lam : ℝ) (hsymm : ∀ i j, A i j = A j i)
    (hlam : ∀ x : V → ℝ, (∑ i, x i = 0) → |bilForm A x x| ≤ lam * ∑ i, (x i) ^ 2)
    (x y : V → ℝ) (hx : ∑ i, x i = 0) (hy : ∑ i, y i = 0) :
    |bilForm A x y| ≤ lam * Real.sqrt (∑ i, (x i) ^ 2) * Real.sqrt (∑ i, (y i) ^ 2) := by
  set nx : ℝ := Real.sqrt (∑ i, (x i) ^ 2) with hnx
  set ny : ℝ := Real.sqrt (∑ i, (y i) ^ 2) with hny
  have hxnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hynn : (0 : ℝ) ≤ ∑ i, (y i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnx0 : 0 ≤ nx := Real.sqrt_nonneg _
  have hny0 : 0 ≤ ny := Real.sqrt_nonneg _
  have hnxsq : nx ^ 2 = ∑ i, (x i) ^ 2 := Real.sq_sqrt hxnn
  have hnysq : ny ^ 2 = ∑ i, (y i) ^ 2 := Real.sq_sqrt hynn
  rcases eq_or_lt_of_le hnx0 with hx0 | hxpos
  · have hzero : ∀ i, x i = 0 := by
      have hs : ∑ i, (x i) ^ 2 = 0 := by rw [← hnxsq, ← hx0]; ring
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).1 hs i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bilForm A x y = 0 := by
      simp only [bilForm]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [hzero i]; ring
    rw [this, ← hx0]
    simp
  rcases eq_or_lt_of_le hny0 with hy0 | hypos
  · have hzero : ∀ i, y i = 0 := by
      have hs : ∑ i, (y i) ^ 2 = 0 := by rw [← hnysq, ← hy0]; ring
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (y i))).1 hs i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    have : bilForm A x y = 0 := by
      simp only [bilForm]
      exact Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => by
        rw [hzero j]; ring
    rw [this, ← hy0]
    simp
  · have hu : ∑ i, (ny * x i) = 0 := by
      rw [← Finset.mul_sum, hx, mul_zero]
    have hv : ∑ i, (nx * y i) = 0 := by
      rw [← Finset.mul_sum, hy, mul_zero]
    have h := bilForm_bound_avg A lam hsymm hlam (fun i => ny * x i) (fun i => nx * y i) hu hv
    rw [bilForm_smul_left, bilForm_smul_right] at h
    have e1 : ∑ i, (ny * x i) ^ 2 = ny ^ 2 * nx ^ 2 := by
      rw [hnxsq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, (nx * y i) ^ 2 = nx ^ 2 * ny ^ 2 := by
      rw [hnysq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2] at h
    rw [abs_mul, abs_mul, abs_of_nonneg hnx0, abs_of_nonneg hny0] at h
    have hprod : 0 < nx * ny := mul_pos hxpos hypos
    have h' : ny * nx * |bilForm A x y| ≤ (ny * nx) * (lam * nx * ny) := by
      calc ny * nx * |bilForm A x y| = ny * (nx * |bilForm A x y|) := by ring
        _ ≤ lam / 2 * (ny ^ 2 * nx ^ 2 + nx ^ 2 * ny ^ 2) := h
        _ = (ny * nx) * (lam * nx * ny) := by ring
    have := le_of_mul_le_mul_left (by linarith [h'] : (ny * nx) * |bilForm A x y|
      ≤ (ny * nx) * (lam * nx * ny)) (by nlinarith : (0:ℝ) < ny * nx)
    linarith [this]

/-- **Expander mixing lemma** (Alon–Chung, as presented by Wigderson).

Let `A` be a symmetric weight matrix on a finite nonempty vertex set `V` which is `d`-regular
(all row sums equal `d`), and suppose the quadratic form of `A` is bounded in absolute value by
`lam` times the squared norm on vectors orthogonal to the all-ones vector (i.e. `lam` bounds the
second eigenvalue in absolute value).  Then for all sets of vertices `S` and `T`, the
number of edges `e(S,T) = ∑_{i ∈ S} ∑_{j ∈ T} A i j` differs from its "expected" value
`d |S| |T| / n` by at most `lam * √(|S| |T|)`. -/
theorem wigderson_expander_mixing
    {V : Type*} [Fintype V] [Nonempty V]
    (A : V → V → ℝ) (d lam : ℝ)
    (hsymm : ∀ i j, A i j = A j i)
    (hreg : ∀ i, ∑ j, A i j = d)
    (hlam0 : 0 ≤ lam)
    (hlam : ∀ x : V → ℝ, (∑ i, x i = 0) → |bilForm A x x| ≤ lam * ∑ i, (x i) ^ 2)
    (S T : Finset V) :
    |(∑ i ∈ S, ∑ j ∈ T, A i j) - d * S.card * T.card / (Fintype.card V)|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  have hcol : ∀ j, ∑ i, A i j = d := fun j => by
    rw [← hreg j]
    exact Finset.sum_congr rfl fun i _ => hsymm i j
  set s : ℝ := (S.card : ℝ) / n with hs
  set t : ℝ := (T.card : ℝ) / n with ht
  set x : V → ℝ := fun i => (if i ∈ S then (1 : ℝ) else 0) - s with hxdef
  set y : V → ℝ := fun j => (if j ∈ T then (1 : ℝ) else 0) - t with hydef
  -- the two vectors are balanced
  have hsum_ind : ∀ (U : Finset V), ∑ i, (if i ∈ U then (1 : ℝ) else 0) = (U.card : ℝ) := by
    intro U; simp
  have hconst : ∀ c : ℝ, ∑ _i : V, c = n * c := by
    intro c
    simp [Finset.sum_const, Finset.card_univ, hn]
  have hxbal : ∑ i, x i = 0 := by
    simp only [hxdef, Finset.sum_sub_distrib, hsum_ind, hconst, hs]
    field_simp
    ring
  have hybal : ∑ i, y i = 0 := by
    simp only [hydef, Finset.sum_sub_distrib, hsum_ind, hconst, ht]
    field_simp
    ring
  -- the value of the bilinear form
  have hinner : ∀ i, ∑ j, A i j * y j = (∑ j ∈ T, A i j) - t * d := by
    intro i
    have : ∀ j, A i j * y j = A i j * (if j ∈ T then (1 : ℝ) else 0) - t * A i j := by
      intro j; simp only [hydef]; ring
    rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_sub_distrib, ← Finset.mul_sum,
      hreg i]
    congr 1
    simp [mul_ite]
  have hsumT : ∑ i, ∑ j ∈ T, A i j = d * (T.card : ℝ) := by
    rw [Finset.sum_comm]
    simp [hcol, mul_comm]
  have hbil : bilForm A x y
      = (∑ i ∈ S, ∑ j ∈ T, A i j) - d * (S.card : ℝ) * (T.card : ℝ) / n := by
    rw [bilForm_eq_sum_mul]
    have hstep : ∀ i, x i * ∑ j, A i j * y j
        = (if i ∈ S then (1 : ℝ) else 0) * (∑ j ∈ T, A i j)
          - (if i ∈ S then (1 : ℝ) else 0) * (t * d)
          - s * (∑ j ∈ T, A i j) + s * (t * d) := by
      intro i; rw [hinner i]; simp only [hxdef]; ring
    rw [Finset.sum_congr rfl (fun i _ => hstep i)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ i, (if i ∈ S then (1 : ℝ) else 0) * (∑ j ∈ T, A i j)
        = ∑ i ∈ S, ∑ j ∈ T, A i j := by
      simp
    have e2 : ∑ i, (if i ∈ S then (1 : ℝ) else 0) * (t * d) = (S.card : ℝ) * (t * d) := by
      rw [← Finset.sum_mul, hsum_ind]
    have e3 : ∑ i, s * (∑ j ∈ T, A i j) = s * (d * (T.card : ℝ)) := by
      rw [← Finset.mul_sum, hsumT]
    rw [e1, e2, e3, hconst, hs, ht]
    field_simp
    ring
  -- norm bounds
  have hnormS : ∑ i, (x i) ^ 2 ≤ (S.card : ℝ) := by
    have hexp : ∀ i, (x i) ^ 2
        = (1 - 2 * s) * (if i ∈ S then (1 : ℝ) else 0) + s ^ 2 := by
      intro i
      simp only [hxdef]
      by_cases hi : i ∈ S
      · rw [if_pos hi]; ring
      · rw [if_neg hi]; ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum_ind, hconst, hs]
    have hval : (1 - 2 * ((S.card : ℝ) / n)) * (S.card : ℝ) + n * ((S.card : ℝ) / n) ^ 2
        = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
      field_simp
      ring
    rw [hval]
    have : (0 : ℝ) ≤ (S.card : ℝ) ^ 2 / n := by positivity
    linarith
  have hnormT : ∑ i, (y i) ^ 2 ≤ (T.card : ℝ) := by
    have hexp : ∀ i, (y i) ^ 2
        = (1 - 2 * t) * (if i ∈ T then (1 : ℝ) else 0) + t ^ 2 := by
      intro i
      simp only [hydef]
      by_cases hi : i ∈ T
      · rw [if_pos hi]; ring
      · rw [if_neg hi]; ring
    rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib, ← Finset.mul_sum,
      hsum_ind, hconst, ht]
    have hval : (1 - 2 * ((T.card : ℝ) / n)) * (T.card : ℝ) + n * ((T.card : ℝ) / n) ^ 2
        = (T.card : ℝ) - (T.card : ℝ) ^ 2 / n := by
      field_simp
      ring
    rw [hval]
    have : (0 : ℝ) ≤ (T.card : ℝ) ^ 2 / n := by positivity
    linarith
  -- combine
  have key := bilForm_bound_norms A lam hsymm hlam x y hxbal hybal
  rw [hbil] at key
  refine key.trans ?_
  have hsS : Real.sqrt (∑ i, (x i) ^ 2) ≤ Real.sqrt (S.card : ℝ) :=
    Real.sqrt_le_sqrt hnormS
  have hsT : Real.sqrt (∑ i, (y i) ^ 2) ≤ Real.sqrt (T.card : ℝ) :=
    Real.sqrt_le_sqrt hnormT
  have hprod : Real.sqrt (∑ i, (x i) ^ 2) * Real.sqrt (∑ i, (y i) ^ 2)
      ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    mul_le_mul hsS hsT (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt ((S.card : ℝ) * (T.card : ℝ))
      = Real.sqrt (S.card : ℝ) * Real.sqrt (T.card : ℝ) :=
    Real.sqrt_mul (by positivity) _
  rw [hsqrt, mul_assoc]
  exact mul_le_mul_of_nonneg_left hprod hlam0

/-- Sanity check: the hypotheses of `wigderson_expander_mixing` are satisfiable.  For the
complete graph with loops on `Fin 3` (all weights `1`, degree `3`) the quadratic form is
`(∑ i, x i) ^ 2`, so it vanishes on balanced vectors and one may take `lam = 0`; the lemma then
says that the edge count between any two sets is exactly `3 |S| |T| / 3 = |S| |T|`. -/
example (S T : Finset (Fin 3)) :
    |(∑ _i ∈ S, ∑ _j ∈ T, (1 : ℝ)) - 3 * S.card * T.card / (Fintype.card (Fin 3))|
      ≤ 0 * Real.sqrt (S.card * T.card) := by
  refine wigderson_expander_mixing (fun _ _ => (1 : ℝ)) 3 0 (fun _ _ => rfl) (by simp) le_rfl
    ?_ S T
  intro x hx
  rw [bilForm_eq_sum_mul]
  simp [hx]

end Frontier

