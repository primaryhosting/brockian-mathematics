/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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
lemma ciInf_le_expectation {X : Type*} [Fintype X] [Nonempty X] {p : X → ℝ}
    (hp : p ∈ stdSimplex ℝ X) (f : X → ℝ) : (⨅ x, f x) ≤ ∑ x, p x * f x := by
  have hb : BddBelow (Set.range f) := Finite.bddBelow_range f
  calc (⨅ x, f x) = ∑ x, p x * (⨅ x, f x) := by rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ ∑ x, p x * f x :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ciInf_le hb x) (hp.1 x)

/-- The expectation of `f` under a probability distribution is at most its maximum. -/
lemma expectation_le_ciSup {X : Type*} [Fintype X] [Nonempty X] {p : X → ℝ}
    (hp : p ∈ stdSimplex ℝ X) (f : X → ℝ) : (∑ x, p x * f x) ≤ ⨆ x, f x := by
  have hb : BddAbove (Set.range f) := Finite.bddAbove_range f
  calc (∑ x, p x * f x) ≤ ∑ x, p x * (⨆ x, f x) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (le_ciSup hb x) (hp.1 x)
    _ = ⨆ x, f x := by rw [← Finset.sum_mul, hp.2, one_mul]

/-- Weak duality (the "easy" direction of Yao's principle): for any randomized algorithm
`p` and any input distribution `q`, the expected cost of the best deterministic algorithm
against `q` is at most the worst-case expected cost of `p`. -/
lemma yao_weak_duality {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (cost : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ}
    (hq : q ∈ stdSimplex ℝ I) :
    (⨅ a : A, ∑ i, q i * cost a i) ≤ ⨆ i : I, ∑ a, p a * cost a i := by
  have key : ∑ a, p a * (∑ i, q i * cost a i) = ∑ i, q i * (∑ a, p a * cost a i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  calc (⨅ a : A, ∑ i, q i * cost a i)
      ≤ ∑ a, p a * (∑ i, q i * cost a i) := ciInf_le_expectation hp _
    _ = ∑ i, q i * (∑ a, p a * cost a i) := key
    _ ≤ ⨆ i : I, ∑ a, p a * cost a i := expectation_le_ciSup hq _

/-- A continuous linear functional on `A → ℝ` (with `A` finite) is given by a vector. -/
lemma clm_apply_eq_sum {A : Type*} [Fintype A] [DecidableEq A] (f : (A → ℝ) →L[ℝ] ℝ)
    (x : A → ℝ) : f x = ∑ a, x a * f (Pi.single a 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : Pi.single a (x a) = x a • (Pi.single a (1:ℝ) : A → ℝ) := by
    ext b; by_cases hb : a = b <;> simp [Pi.single_apply, hb]
  rw [h, map_smul]
  simp

/-- **Key lemma** (a theorem of the alternative, the combinatorial core of the minimax
theorem): for any real payoff matrix `M`, either the column player has a distribution `q`
making every row expectation strictly positive, or the row player has a distribution `p`
making every column expectation nonpositive.

The proof separates the compact convex set of achievable payoff vectors from the open
positive orthant by a hyperplane (geometric Hahn–Banach). -/
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
theorem yao_principle {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]
    (cost : A → I → ℝ) :
    (⨅ p : stdSimplex ℝ A, ⨆ i : I, ∑ a, (p : A → ℝ) a * cost a i) =
      ⨆ q : stdSimplex ℝ I, ⨅ a : A, ∑ i, (q : I → ℝ) i * cost a i := by
  classical
  have hweak : ∀ (p : stdSimplex ℝ A) (q : stdSimplex ℝ I),
      (⨅ a : A, ∑ i, (q : I → ℝ) i * cost a i) ≤ ⨆ i : I, ∑ a, (p : A → ℝ) a * cost a i :=
    fun p q => yao_weak_duality cost p.2 q.2
  have hbddF : BddBelow (Set.range fun p : stdSimplex ℝ A =>
      ⨆ i : I, ∑ a, (p : A → ℝ) a * cost a i) := by
    refine ⟨⨅ a : A, ∑ i, ((Classical.arbitrary (stdSimplex ℝ I) : stdSimplex ℝ I) : I → ℝ) i
      * cost a i, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hweak p _
  have hbddG : BddAbove (Set.range fun q : stdSimplex ℝ I =>
      ⨅ a : A, ∑ i, (q : I → ℝ) i * cost a i) := by
    refine ⟨⨆ i : I, ∑ a, ((Classical.arbitrary (stdSimplex ℝ A) : stdSimplex ℝ A) : A → ℝ) a
      * cost a i, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hweak _ q
  refine le_antisymm ?_ (ciSup_le fun q => le_ciInf fun p => hweak p q)
  by_contra hlt
  push_neg at hlt
  set c : ℝ := ((⨆ q : stdSimplex ℝ I, ⨅ a : A, ∑ i, (q : I → ℝ) i * cost a i) +
      (⨅ p : stdSimplex ℝ A, ⨆ i : I, ∑ a, (p : A → ℝ) a * cost a i)) / 2 with hcdef
  have hcR : (⨆ q : stdSimplex ℝ I, ⨅ a : A, ∑ i, (q : I → ℝ) i * cost a i) < c := by
    rw [hcdef]; linarith
  have hcL : c < ⨅ p : stdSimplex ℝ A, ⨆ i : I, ∑ a, (p : A → ℝ) a * cost a i := by
    rw [hcdef]; linarith
  rcases exists_alternative (fun a i => cost a i - c) with ⟨q, hq, hqpos⟩ | ⟨p, hp, hple⟩
  · have hexp : ∀ a : A, ∑ i, q i * (cost a i - c) = (∑ i, q i * cost a i) - c := by
      intro a
      have h2 : ∀ i, q i * (cost a i - c) = q i * cost a i - c * q i := fun i => by ring
      simp_rw [h2]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq.2, mul_one]
    have hlow : c ≤ ⨅ a : A, ∑ i, q i * cost a i :=
      le_ciInf fun a => by have := hqpos a; rw [hexp a] at this; linarith
    have hle : (⨅ a : A, ∑ i, q i * cost a i)
        ≤ ⨆ q' : stdSimplex ℝ I, ⨅ a : A, ∑ i, (q' : I → ℝ) i * cost a i :=
      le_ciSup hbddG ⟨q, hq⟩
    linarith
  · have hexp : ∀ i : I, ∑ a, p a * (cost a i - c) = (∑ a, p a * cost a i) - c := by
      intro i
      have h2 : ∀ a, p a * (cost a i - c) = p a * cost a i - c * p a := fun a => by ring
      simp_rw [h2]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hp.2, mul_one]
    have hhigh : (⨆ i : I, ∑ a, p a * cost a i) ≤ c :=
      ciSup_le fun i => by have := hple i; rw [hexp i] at this; linarith
    have hge : (⨅ p' : stdSimplex ℝ A, ⨆ i : I, ∑ a, (p' : A → ℝ) a * cost a i)
        ≤ ⨆ i : I, ∑ a, p a * cost a i :=
      ciInf_le hbddF ⟨p, hp⟩
    linarith

end CS

