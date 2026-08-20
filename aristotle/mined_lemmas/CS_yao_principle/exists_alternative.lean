/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-- The standard simplex over a nonempty finite type is nonempty (it contains point masses). -/
instance nonempty_stdSimplex {X : Type*} [Fintype X] [Nonempty X] :
    Nonempty (stdSimplex ℝ X) :=
  ⟨⟨fun x => if Classical.arbitrary X = x then 1 else 0,
    ite_eq_mem_stdSimplex ℝ (Classical.arbitrary X)⟩⟩

/-- The expectation of `f` under a probability distribution is at least its minimum. -/

lemma exists_alternative {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (M : A → I → ℝ) :
    (∃ q ∈ stdSimplex ℝ I, ∀ a, 0 < ∑ i, q i * M a i) ∨
      (∃ p ∈ stdSimplex ℝ A, ∀ i, ∑ a, p a * M a i ≤ 0) := by
  classical
  by_cases hcase : ∃ q ∈ stdSimplex ℝ I, ∀ a, 0 < ∑ i, q i * M a i
  · exact Or.inl hcase
  right
  push_neg at hcase
  set L : (I → ℝ) → (A → ℝ) := fun q a => ∑ i, q i * M a i with hLdef
  have hLlin : IsLinearMap ℝ L := by
    constructor
    · intro x y; funext a; simp only [hLdef, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c x; funext a; simp only [hLdef, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  set P : Set (A → ℝ) := {x : A → ℝ | ∀ a, 0 < x a} with hPdef
  have hPopen : IsOpen P := by
    have h : P = ⋂ a, (fun x : A → ℝ => x a) ⁻¹' (Set.Ioi 0) := by ext x; simp [hPdef]
    rw [h]
    exact isOpen_iInter_of_finite fun a => (continuous_apply a).isOpen_preimage _ isOpen_Ioi
  have hPconv : Convex ℝ P := by
    intro x hx y hy s t hs ht hst a
    have hx' := hx a
    have hy' := hy a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases lt_or_eq_of_le hs with h | h
    · nlinarith
    · nlinarith [ht]
  have hKconv : Convex ℝ (L '' stdSimplex ℝ I) :=
    (convex_stdSimplex ℝ I).is_linear_image hLlin
  have hdisj : Disjoint P (L '' stdSimplex ℝ I) := by
    rw [Set.disjoint_left]
    rintro x hxP ⟨q, hq, rfl⟩
    obtain ⟨a, ha⟩ := hcase q hq
    exact absurd (hxP a) (by simpa [hLdef] using not_lt.2 ha)
  obtain ⟨f, u, hfP, hfK⟩ := geometric_hahn_banach_open hPconv hPopen hKconv hdisj
  set c : A → ℝ := fun a => f (Pi.single a 1) with hcdef
  have hfeq : ∀ x : A → ℝ, f x = ∑ a, x a * c a := fun x => clm_apply_eq_sum f x
  set T : ℝ := ∑ a, c a with hTdef
  -- the separating functional has nonpositive coordinates
  have hcnonpos : ∀ a, c a ≤ 0 := by
    intro a
    by_contra hpos
    push_neg at hpos
    set s : ℝ := max 1 ((u - T + 1) / c a) with hsdef
    have hs1 : (1:ℝ) ≤ s := le_max_left _ _
    have hs0 : 0 < s := lt_of_lt_of_le one_pos hs1
    have hx : (fun b => if b = a then 1 + s else (1:ℝ)) ∈ P := by
      intro b
      by_cases hb : b = a
      · simp only [hb, if_pos]; linarith
      · simp [hb]
    have hval : f (fun b => if b = a then 1 + s else (1:ℝ)) = T + s * c a := by
      rw [hfeq]
      have h2 : ∀ b : A, (if b = a then 1 + s else (1:ℝ)) * c b
          = c b + (if b = a then s * c b else 0) := by
        intro b
        by_cases hb : b = a
        · simp only [hb, if_pos]; ring
        · simp [hb]
      simp_rw [h2]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ a (fun b => s * c b)]
      simp [hTdef]
    have hlt := hfP _ hx
    rw [hval] at hlt
    have hge : (u - T + 1) / c a * c a ≤ s * c a :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hge
    linarith
  have hTnonpos : T ≤ 0 := Finset.sum_nonpos fun a _ => hcnonpos a
  -- the separating value is nonnegative
  have hu0 : 0 ≤ u := by
    by_contra hu
    push_neg at hu
    rcases lt_or_eq_of_le hTnonpos with hT | hT
    · have hpos : 0 < u / (2 * T) := div_pos_of_neg_of_neg hu (by linarith)
      have hx : (fun _ : A => u / (2 * T)) ∈ P := fun _ => hpos
      have hval : f (fun _ : A => u / (2 * T)) = u / 2 := by
        rw [hfeq, ← Finset.mul_sum, ← hTdef]
        field_simp
        rw [mul_div_assoc, div_self hT.ne, mul_one]
      have hlt := hfP _ hx
      rw [hval] at hlt
      linarith
    · have hx : (fun _ : A => (1:ℝ)) ∈ P := fun _ => one_pos
      have hval : f (fun _ : A => (1:ℝ)) = 0 := by
        rw [hfeq]; simp [← hTdef, ← hT]
      have hlt := hfP _ hx
      rw [hval] at hlt
      linarith
  -- the separating functional is nonzero
  have hcne : ∃ a, c a ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hf0 : ∀ x : A → ℝ, f x = 0 := by
      intro x; rw [hfeq]; simp [hall]
    have h1 : (0:ℝ) < u := by
      have h := hfP (fun _ => (1:ℝ)) (fun _ => one_pos); rwa [hf0] at h
    have hq0 : (fun j => if Classical.arbitrary I = j then (1:ℝ) else 0) ∈ stdSimplex ℝ I :=
      ite_eq_mem_stdSimplex ℝ (Classical.arbitrary I)
    have h2 : u ≤ 0 := by
      have h := hfK (L _) ⟨_, hq0, rfl⟩; rwa [hf0] at h
    linarith
  obtain ⟨a₀, ha₀⟩ := hcne
  set S : ℝ := ∑ a, -c a with hSdef
  have hS : 0 < S :=
    Finset.sum_pos' (fun a _ => by linarith [hcnonpos a])
      ⟨a₀, Finset.mem_univ _, neg_pos.2 (lt_of_le_of_ne (hcnonpos a₀) ha₀)⟩
  refine ⟨fun a => (-c a)/S, ⟨fun a => div_nonneg (by linarith [hcnonpos a]) hS.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hSdef, div_self hS.ne']
  · intro i
    have hq : (fun j => if i = j then (1:ℝ) else 0) ∈ stdSimplex ℝ I :=
      ite_eq_mem_stdSimplex ℝ i
    have hLq : L (fun j => if i = j then (1:ℝ) else 0) = fun a => M a i := by
      funext a; simp [hLdef]
    have h1 : u ≤ ∑ a, M a i * c a := by
      have h := hfK _ ⟨_, hq, rfl⟩
      rw [hLq, hfeq] at h
      exact h
    have hsum : 0 ≤ ∑ a, M a i * c a := le_trans hu0 h1
    calc ∑ a, (-c a/S) * M a i = (∑ a, -(M a i * c a))/S := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun a _ => by ring
      _ = -((∑ a, M a i * c a)/S) := by rw [Finset.sum_neg_distrib]; ring
      _ ≤ 0 := by have := div_nonneg hsum hS.le; linarith

/-- **Yao's minimax principle.**  For a finite set `A` of deterministic algorithms, a finite
set `I` of inputs and a cost function `cost`, the best worst-case expected cost of a
randomized algorithm (i.e. of a probability distribution `p` over `A`) equals the best,
over input distributions `q`, of the expected cost of the best deterministic algorithm
for `q`. -/
