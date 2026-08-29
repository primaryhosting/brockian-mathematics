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

/-- The bilinear form `u ↦ v ↦ ∑ᵢ ∑ⱼ uᵢ Mᵢⱼ vⱼ` attached to a matrix `M`. -/
noncomputable def bil {V : Type*} [Fintype V] (M : Matrix V V ℝ) (u v : V → ℝ) : ℝ :=
  ∑ i, ∑ j, u i * M i j * v j

section

variable {V : Type*} [Fintype V] (M : Matrix V V ℝ)

lemma bil_add_left (u u' v : V → ℝ) :
    bil M (fun i => u i + u' i) v = bil M u v + bil M u' v := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma bil_add_right (u v v' : V → ℝ) :
    bil M u (fun j => v j + v' j) = bil M u v + bil M u v' := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- If all row sums of `M` equal `d`, then `bil M u 1 = d * ∑ u`. -/
lemma bil_const_right {d : ℝ} (hrow : ∀ i, ∑ j, M i j = d) (u : V → ℝ) (c : ℝ) :
    bil M u (fun _ => c) = c * d * ∑ i, u i := by
  unfold bil
  have h : ∀ i : V, ∑ j, u i * M i j * c = c * d * u i := by
    intro i
    have : ∑ j, u i * M i j * c = (∑ j, M i j) * (u i * c) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hrow i]; ring
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => h i), ← Finset.mul_sum]

/-- If all column sums of `M` equal `d`, then `bil M 1 v = d * ∑ v`. -/
lemma bil_const_left {d : ℝ} (hcol : ∀ j, ∑ i, M i j = d) (v : V → ℝ) (c : ℝ) :
    bil M (fun _ => c) v = c * d * ∑ j, v j := by
  unfold bil
  rw [Finset.sum_comm]
  have h : ∀ j : V, ∑ i, c * M i j * v j = c * d * v j := by
    intro j
    have : ∑ i, c * M i j * v j = (∑ i, M i j) * (c * v j) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [this, hcol j]; ring
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => h j), ← Finset.mul_sum]

end

/-- Indicator sums: `∑ᵢ 1_S(i) f i = ∑_{i ∈ S} f i`. -/
lemma sum_indicator_mul {V : Type*} [Fintype V] (S : Finset V) (f : V → ℝ) :
    ∑ i, (if i ∈ S then (1 : ℝ) else 0) * f i = ∑ i ∈ S, f i := by
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
    show (if i ∈ S then (1 : ℝ) else 0) * f i = if i ∈ S then f i else 0 by
      by_cases h : i ∈ S <;> simp [h])]
  rw [Finset.sum_ite_mem]
  simp

/-- **Expander mixing lemma** (Alon–Chung; see Hoory–Linial–Wigderson).

Let `M` be a real symmetric matrix indexed by a finite vertex set `V` all of whose row sums
equal `d` (e.g. the adjacency matrix of a `d`-regular graph), and suppose `M` contracts the
space of mean-zero vectors by a factor `lam` (i.e. `lam` dominates the absolute values of all
eigenvalues other than the trivial one `d`).  Then for any two vertex subsets `S`, `T` the
number of edges between `S` and `T` deviates from its "random graph" expectation
`d |S| |T| / n` by at most `lam * sqrt (|S| |T|)`. -/
theorem wigderson_expander_mixing
    {V : Type*} [Fintype V] (M : Matrix V V ℝ) (d lam : ℝ) (S T : Finset V)
    (hn : 0 < Fintype.card V)
    (hsymm : ∀ i j : V, M i j = M j i)
    (hrow : ∀ i : V, ∑ j, M i j = d)
    (hlam : 0 ≤ lam)
    (hspec : ∀ v : V → ℝ, (∑ i, v i = 0) →
      ∑ i, (∑ j, M i j * v j) ^ 2 ≤ lam ^ 2 * ∑ i, (v i) ^ 2) :
    |(∑ i ∈ S, ∑ j ∈ T, M i j) - d * S.card * T.card / Fintype.card V|
      ≤ lam * Real.sqrt (S.card * T.card) := by
  have hcol : ∀ j : V, ∑ i, M i j = d := by
    intro j
    rw [← hrow j]
    exact Finset.sum_congr rfl (fun i _ => hsymm i j)
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hn0 : 0 < n := by
    rw [hn_def]; exact_mod_cast hn
  set s : ℝ := (S.card : ℝ) / n with hs_def
  set t : ℝ := (T.card : ℝ) / n with ht_def
  set x : V → ℝ := fun i => (if i ∈ S then (1 : ℝ) else 0) - s with hx_def
  set y : V → ℝ := fun j => (if j ∈ T then (1 : ℝ) else 0) - t with hy_def
  -- basic indicator sums
  have hsumS : ∑ i, (if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by
    rw [Finset.sum_ite_mem]; simp
  have hsumT : ∑ j, (if j ∈ T then (1 : ℝ) else 0) = (T.card : ℝ) := by
    rw [Finset.sum_ite_mem]; simp
  have hx0 : ∑ i, x i = 0 := by
    rw [hx_def]
    rw [Finset.sum_sub_distrib, hsumS]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs_def, ← hn_def]
    field_simp
    ring
  have hy0 : ∑ j, y j = 0 := by
    rw [hy_def]
    rw [Finset.sum_sub_distrib, hsumT]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ht_def, ← hn_def]
    field_simp
    ring
  -- decomposition of the edge count
  have hdecomp : (∑ i ∈ S, ∑ j ∈ T, M i j)
      = bil M x y + d * S.card * T.card / n := by
    have hSx : (fun i => if i ∈ S then (1 : ℝ) else 0) = fun i => x i + s := by
      funext i; rw [hx_def]; ring
    have hTy : (fun j => if j ∈ T then (1 : ℝ) else 0) = fun j => y j + t := by
      funext j; rw [hy_def]; ring
    have hA : bil M (fun i => if i ∈ S then (1 : ℝ) else 0)
        (fun j => if j ∈ T then (1 : ℝ) else 0) = ∑ i ∈ S, ∑ j ∈ T, M i j := by
      have step : ∀ i : V,
          ∑ j, (if i ∈ S then (1 : ℝ) else 0) * M i j * (if j ∈ T then (1 : ℝ) else 0)
            = (if i ∈ S then (1 : ℝ) else 0) * ∑ j ∈ T, M i j := by
        intro i
        rw [Finset.mul_sum,
          ← sum_indicator_mul T (fun j => (if i ∈ S then (1 : ℝ) else 0) * M i j)]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      calc bil M (fun i => if i ∈ S then (1 : ℝ) else 0)
            (fun j => if j ∈ T then (1 : ℝ) else 0)
          = ∑ i, (if i ∈ S then (1 : ℝ) else 0) * ∑ j ∈ T, M i j :=
            Finset.sum_congr rfl (fun i _ => step i)
        _ = ∑ i ∈ S, ∑ j ∈ T, M i j := sum_indicator_mul S _
    rw [← hA, hSx, hTy]
    rw [bil_add_left, bil_add_right, bil_add_right]
    rw [bil_const_right M hrow x t, hx0]
    rw [bil_const_left M hcol y s, hy0]
    have hcc : bil M (fun _ : V => s) (fun _ : V => t) = s * d * (n * t) := by
      rw [bil_const_left M hcol (fun _ : V => t) s]
      congr 1
      simp [Finset.sum_const, Finset.card_univ, hn_def]
    rw [hcc, hs_def, ht_def]
    field_simp
    ring
  -- Cauchy-Schwarz bound on the "error" term
  have hxsq : ∑ i, (x i) ^ 2 ≤ (S.card : ℝ) := by
    have hexp : ∑ i, (x i) ^ 2 = (S.card : ℝ) - (S.card : ℝ) ^ 2 / n := by
      have hpt : ∀ i : V, (x i) ^ 2
          = (if i ∈ S then (1 : ℝ) else 0) - 2 * s * (if i ∈ S then (1 : ℝ) else 0) + s ^ 2 := by
        intro i
        rw [hx_def]
        by_cases h : i ∈ S <;> (simp [h]; ring)
      rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hpt i)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumS]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, hs_def]
      field_simp
      ring
    rw [hexp]
    have : 0 ≤ (S.card : ℝ) ^ 2 / n := by positivity
    linarith
  have hysq : ∑ j, (y j) ^ 2 ≤ (T.card : ℝ) := by
    have hexp : ∑ j, (y j) ^ 2 = (T.card : ℝ) - (T.card : ℝ) ^ 2 / n := by
      have hpt : ∀ j : V, (y j) ^ 2
          = (if j ∈ T then (1 : ℝ) else 0) - 2 * t * (if j ∈ T then (1 : ℝ) else 0) + t ^ 2 := by
        intro j
        rw [hy_def]
        by_cases h : j ∈ T <;> (simp [h]; ring)
      rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hpt j)]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumT]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, ht_def]
      field_simp
      ring
    rw [hexp]
    have : 0 ≤ (T.card : ℝ) ^ 2 / n := by positivity
    linarith
  have hbil_eq : bil M x y = ∑ i, x i * (∑ j, M i j * y j) := by
    unfold bil
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hcs : (bil M x y) ^ 2 ≤ (∑ i, (x i) ^ 2) * (∑ i, (∑ j, M i j * y j) ^ 2) := by
    rw [hbil_eq]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun i => ∑ j, M i j * y j)
  have hMy : ∑ i, (∑ j, M i j * y j) ^ 2 ≤ lam ^ 2 * (T.card : ℝ) := by
    refine le_trans (hspec y hy0) ?_
    have : (0 : ℝ) ≤ lam ^ 2 := sq_nonneg lam
    nlinarith [hysq]
  have hxnn : (0 : ℝ) ≤ ∑ i, (x i) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hbnd : (bil M x y) ^ 2 ≤ (lam * Real.sqrt (S.card * T.card)) ^ 2 := by
    have h1 : (bil M x y) ^ 2 ≤ (S.card : ℝ) * (lam ^ 2 * (T.card : ℝ)) := by
      refine le_trans hcs ?_
      have hMynn : (0 : ℝ) ≤ ∑ i, (∑ j, M i j * y j) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have h2 : (∑ i, (x i) ^ 2) * (∑ i, (∑ j, M i j * y j) ^ 2)
          ≤ (S.card : ℝ) * (∑ i, (∑ j, M i j * y j) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hxsq hMynn
      refine le_trans h2 ?_
      exact mul_le_mul_of_nonneg_left hMy (by positivity)
    have hsq : (lam * Real.sqrt ((S.card : ℝ) * (T.card : ℝ))) ^ 2
        = lam ^ 2 * ((S.card : ℝ) * (T.card : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [hsq]
    nlinarith [h1]
  have hnn : (0 : ℝ) ≤ lam * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) := by positivity
  have : |bil M x y| ≤ lam * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)) :=
    abs_le_of_sq_le_sq' (by simpa using hbnd) hnn |>.2
  rw [hdecomp]
  simpa using this

end Frontier

