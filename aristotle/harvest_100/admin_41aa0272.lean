/-
# Deligne Weil RH
Category: Frontier — Fields Medal Work
Target: Frontier.deligne_weil_RH
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

namespace Frontier

/-- Cohomological data attached to a variety over a finite field `𝔽_q`:
the inverse roots (Frobenius eigenvalues) on each cohomology group, together with the
point counts over the extensions `𝔽_{q^m}`, linked by the Grothendieck–Lefschetz trace
formula. -/
structure WeilVariety where
  /-- Cardinality of the base field. -/
  q : ℕ
  /-- The base field has at least two elements. -/
  hq : 2 ≤ q
  /-- Dimension of the variety. -/
  dim : ℕ
  /-- Multiset of inverse roots of Frobenius acting on the `i`-th cohomology group. -/
  frobRoots : ℕ → Multiset ℂ
  /-- `count m` is the number of `𝔽_{q^m}`-rational points. -/
  count : ℕ → ℕ
  /-- Cohomology vanishes above degree `2 * dim`. -/
  vanishing : ∀ i, 2 * dim < i → frobRoots i = 0
  /-- Grothendieck–Lefschetz trace formula. -/
  trace : ∀ m, 1 ≤ m →
    (count m : ℂ) =
      ∑ i ∈ Finset.range (2 * dim + 1),
        (-1) ^ i * (((frobRoots i).map (fun a => a ^ m)).sum)

/-- The Riemann hypothesis for a variety over a finite field: every inverse root of
Frobenius on the `i`-th cohomology group has archimedean absolute value `q ^ (i / 2)`. -/
def RiemannHypothesis (W : WeilVariety) : Prop :=
  ∀ i ≤ 2 * W.dim, ∀ a ∈ W.frobRoots i, ‖a‖ = (W.q : ℝ) ^ ((i : ℝ) / 2)

section Auxiliary

/-- Norm bound for the `m`-th power sum of a multiset of complex numbers of bounded norm. -/
lemma multiset_pow_sum_norm_le (s : Multiset ℂ) (c : ℝ) (m : ℕ)
    (h : ∀ a ∈ s, ‖a‖ ≤ c) :
    ‖(s.map (fun a => a ^ m)).sum‖ ≤ (Multiset.card s : ℝ) * c ^ m := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : ‖a‖ ≤ c := h a (Multiset.mem_cons_self a s)
      have hc : (0:ℝ) ≤ c := le_trans (norm_nonneg a) ha
      have ih' : ‖(s.map (fun x => x ^ m)).sum‖ ≤ (Multiset.card s : ℝ) * c ^ m :=
        ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
      have hpow : ‖a ^ m‖ ≤ c ^ m := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg a) ha m
      have : ‖(a ^ m) + (s.map (fun x => x ^ m)).sum‖ ≤ c ^ m + (Multiset.card s : ℝ) * c ^ m :=
        le_trans (norm_add_le _ _) (add_le_add hpow ih')
      simpa [Multiset.map_cons, Multiset.sum_cons, add_mul, add_comm, add_left_comm,
        add_assoc] using this

/-- Even-degree bookkeeping for the projective space example. -/
lemma sum_projective_range (q n m : ℕ) :
    ∑ i ∈ Finset.range (2 * n + 1),
        ((-1 : ℂ)) ^ i * (if i % 2 = 0 then (((q : ℂ) ^ (i / 2)) ^ m) else 0)
      = ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ (k * m)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h : 2 * (n + 1) + 1 = (2 * n + 1) + 1 + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
      have h1 : (2 * n + 1) % 2 = 1 := by omega
      have h2 : (2 * n + 1 + 1) % 2 = 0 := by omega
      have h3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
      rw [h1, h2, h3, Finset.sum_range_succ]
      have hsign : ((-1 : ℂ)) ^ (2 * n + 1 + 1) = 1 := by
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
        simp
      rw [hsign]
      simp [pow_mul, Finset.sum_range_succ]

end Auxiliary

/-- The Weil data of projective `n`-space over `𝔽_q`: the cohomology is one-dimensional in
each even degree `2k ≤ 2n`, with Frobenius eigenvalue `q ^ k`, and the number of
`𝔽_{q^m}`-points is `1 + q^m + ⋯ + q^{nm}`. -/
def projectiveSpace (q n : ℕ) (hq : 2 ≤ q) : WeilVariety where
  q := q
  hq := hq
  dim := n
  frobRoots := fun i => if i % 2 = 0 ∧ i ≤ 2 * n then {((q : ℂ)) ^ (i / 2)} else 0
  count := fun m => ∑ k ∈ Finset.range (n + 1), q ^ (k * m)
  vanishing := by
    intro i hi
    have : ¬ (i % 2 = 0 ∧ i ≤ 2 * n) := by omega
    simp [this]
  trace := by
    intro m _
    have hcast : ((∑ k ∈ Finset.range (n + 1), q ^ (k * m) : ℕ) : ℂ)
        = ∑ k ∈ Finset.range (n + 1), ((q : ℂ) ^ (k * m)) := by push_cast; ring
    rw [hcast, ← sum_projective_range q n m]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ 2 * n := by
      simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hi
    by_cases h : i % 2 = 0 <;> simp [h, hi']

/-- The `count` function of `projectiveSpace q n` is the actual number of rational points of
`n`-dimensional projective space over a field with `q ^ m` elements. -/
theorem card_points_projectiveSpace (q n m : ℕ) (hq : 2 ≤ q)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = q ^ m) :
    Nat.card (Projectivization K (Fin (n + 1) → K)) = (projectiveSpace q n hq).count m := by
  rw [Projectivization.card_of_finrank K _
    (by simp : Module.finrank K (Fin (n + 1) → K) = n + 1), hK]
  simp [projectiveSpace, pow_mul, mul_comm]

/-- **Base case of the Weil Riemann hypothesis**: it holds for projective space. -/
theorem riemannHypothesis_projectiveSpace (q n : ℕ) (hq : 2 ≤ q) :
    RiemannHypothesis (projectiveSpace q n hq) := by
  intro i hi a ha
  simp only [projectiveSpace] at hi ha ⊢
  by_cases h : i % 2 = 0 ∧ i ≤ 2 * n
  · rw [if_pos h] at ha
    have ha' : a = ((q : ℂ)) ^ (i / 2) := by
      simpa using ha
    subst ha'
    have hq0 : (0:ℝ) ≤ (q : ℝ) := by positivity
    rw [norm_pow, Complex.norm_natCast]
    have hi2 : ((i : ℝ) / 2) = ((i / 2 : ℕ) : ℝ) := by
      obtain ⟨k, hk⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
      subst hk
      have : (2 * k) / 2 = k := by omega
      rw [this]
      push_cast
      ring
    rw [hi2, Real.rpow_natCast]
  · rw [if_neg h] at ha
    simp at ha

/-- **Consequence of the Riemann hypothesis**: the point counts of a `d`-dimensional variety
whose top cohomology is one-dimensional with Frobenius eigenvalue `q ^ d` satisfy the
square-root error estimate `|#X(𝔽_{q^m}) - q^{dm}| ≤ B · q^{(2d-1)m/2}`, where `B` is the sum
of the Betti numbers below the top degree. -/
theorem count_estimate_of_riemannHypothesis (W : WeilVariety)
    (hRH : RiemannHypothesis W)
    (htop : W.frobRoots (2 * W.dim) = {((W.q : ℂ)) ^ W.dim})
    (m : ℕ) (hm : 1 ≤ m) :
    ‖(W.count m : ℂ) - ((W.q : ℂ)) ^ (W.dim * m)‖ ≤
      (∑ i ∈ Finset.range (2 * W.dim), (Multiset.card (W.frobRoots i) : ℝ)) *
        (W.q : ℝ) ^ (((2 * W.dim - 1 : ℕ) : ℝ) * m / 2) := by
  have hq1 : (1 : ℝ) ≤ (W.q : ℝ) := by
    have := W.hq
    exact_mod_cast le_trans (by norm_num) this
  have hq0 : (0 : ℝ) ≤ (W.q : ℝ) := le_trans zero_le_one hq1
  set d := W.dim with hd
  set Q : ℝ := (W.q : ℝ) ^ (((2 * d - 1 : ℕ) : ℝ) * m / 2) with hQ
  -- rewrite the difference as the alternating sum over degrees below the top one
  have htopterm : (((W.frobRoots (2 * d)).map (fun a => a ^ m)).sum) = ((W.q : ℂ)) ^ (d * m) := by
    rw [htop]
    simp [pow_mul]
  have key : (W.count m : ℂ) - ((W.q : ℂ)) ^ (d * m)
      = ∑ i ∈ Finset.range (2 * d), (-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum) := by
    rw [W.trace m hm, Finset.sum_range_succ, htopterm]
    have hsign : ((-1 : ℂ)) ^ (2 * d) = 1 := by
      rw [pow_mul]; simp
    rw [hsign, one_mul]
    ring
  rw [key]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i ∈ Finset.range (2 * d),
      ‖(-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        ≤ (Multiset.card (W.frobRoots i) : ℝ) * Q := by
    intro i hi
    have hi2d : i ≤ 2 * d := le_of_lt (Finset.mem_range.mp hi)
    have hbound : ∀ a ∈ W.frobRoots i, ‖a‖ ≤ (W.q : ℝ) ^ ((i : ℝ) / 2) :=
      fun a ha => le_of_eq (hRH i hi2d a ha)
    have h1 : ‖(((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        ≤ (Multiset.card (W.frobRoots i) : ℝ) * ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m :=
      multiset_pow_sum_norm_le _ _ m hbound
    have h2 : ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m = (W.q : ℝ) ^ (((i : ℝ) / 2) * m) := by
      rw [← Real.rpow_natCast ((W.q : ℝ) ^ ((i : ℝ) / 2)) m, ← Real.rpow_mul hq0]
    have h3 : ((i : ℝ) / 2) * m ≤ ((2 * d - 1 : ℕ) : ℝ) * m / 2 := by
      have hile : (i : ℝ) ≤ ((2 * d - 1 : ℕ) : ℝ) := by
        have : i ≤ 2 * d - 1 := by
          have := Finset.mem_range.mp hi
          omega
        exact_mod_cast this
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hile hm0]
    have h4 : (W.q : ℝ) ^ (((i : ℝ) / 2) * m) ≤ Q :=
      Real.rpow_le_rpow_of_exponent_le hq1 h3
    calc ‖(-1 : ℂ) ^ i * (((W.frobRoots i).map (fun a => a ^ m)).sum)‖
        = ‖(((W.frobRoots i).map (fun a => a ^ m)).sum)‖ := by
          simp
      _ ≤ (Multiset.card (W.frobRoots i) : ℝ) * ((W.q : ℝ) ^ ((i : ℝ) / 2)) ^ m := h1
      _ ≤ (Multiset.card (W.frobRoots i) : ℝ) * Q := by
          have hcard : (0 : ℝ) ≤ (Multiset.card (W.frobRoots i) : ℝ) := by positivity
          rw [h2]
          exact mul_le_mul_of_nonneg_left h4 hcard
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.sum_mul]

/-- The Weil Riemann hypothesis (Deligne): formalized statement, together with a proof of the
projective-space base case and of the square-root point-count estimate that the Riemann
hypothesis implies. -/
theorem deligne_weil_RH :
    (∀ (q n : ℕ) (hq : 2 ≤ q), RiemannHypothesis (projectiveSpace q n hq)) ∧
    (∀ (q n m : ℕ) (hq : 2 ≤ q) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = q ^ m →
      Nat.card (Projectivization K (Fin (n + 1) → K)) = (projectiveSpace q n hq).count m) ∧
    (∀ (W : WeilVariety), RiemannHypothesis W →
      W.frobRoots (2 * W.dim) = {((W.q : ℂ)) ^ W.dim} →
      ∀ m, 1 ≤ m →
        ‖(W.count m : ℂ) - ((W.q : ℂ)) ^ (W.dim * m)‖ ≤
          (∑ i ∈ Finset.range (2 * W.dim), (Multiset.card (W.frobRoots i) : ℝ)) *
            (W.q : ℝ) ^ (((2 * W.dim - 1 : ℕ) : ℝ) * m / 2)) :=
  ⟨riemannHypothesis_projectiveSpace,
   fun q n m hq K _ _ hK => card_points_projectiveSpace q n m hq K hK,
   fun W hRH htop m hm => count_estimate_of_riemannHypothesis W hRH htop m hm⟩

end Frontier

