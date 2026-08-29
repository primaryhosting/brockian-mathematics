/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated as a module docstring below; Lean requires `import`
-- to precede any module docstring.)

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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

variable {A I : Type*}

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
(deterministic) algorithms `A`, run on the input `i`. -/
noncomputable def randCost [Fintype A] (cost : A → I → ℝ) (p : A → ℝ) (i : I) : ℝ :=
  ∑ a, p a * cost a i

/-- The expected cost of the deterministic algorithm `a` on a random input drawn from the
distribution `q` over inputs. -/
noncomputable def distCost [Fintype I] (cost : A → I → ℝ) (a : A) (q : I → ℝ) : ℝ :=
  ∑ i, q i * cost a i

section Aux

/-- A convex combination is at least any lower bound of the combined values. -/
lemma le_convex_comb {α : Type*} [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α)
    {f : α → ℝ} {m : ℝ} (h : ∀ a, m ≤ f a) : m ≤ ∑ a, w a * f a := by
  obtain ⟨h0, h1⟩ := hw
  calc m = ∑ a, w a * m := by rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ a, w a * f a := Finset.sum_le_sum fun a _ => by
        exact mul_le_mul_of_nonneg_left (h a) (h0 a)

/-- A convex combination is at most any upper bound of the combined values. -/
lemma convex_comb_le {α : Type*} [Fintype α] {w : α → ℝ} (hw : w ∈ stdSimplex ℝ α)
    {f : α → ℝ} {m : ℝ} (h : ∀ a, f a ≤ m) : ∑ a, w a * f a ≤ m := by
  obtain ⟨h0, h1⟩ := hw
  calc ∑ a, w a * f a ≤ ∑ a, w a * m :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (h0 a)
    _ = m := by rw [← Finset.sum_mul, h1, one_mul]

/-- Exchanging the order of averaging: averaging the randomized cost over inputs is the same as
averaging the distributional cost over algorithms. -/
lemma exchange [Fintype A] [Fintype I] (cost : A → I → ℝ) (p : A → ℝ) (q : I → ℝ) :
    ∑ i, q i * randCost cost p i = ∑ a, p a * distCost cost a q := by
  simp only [randCost, distCost, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

end Aux

section Alternative

variable [Fintype A] [Fintype I]

/-- The theorem of the alternative underlying the minimax theorem (a form of Ville's theorem):
for any real matrix `M`, either there is a distribution `q` over the columns making all row
averages nonnegative, or there is a distribution `p` over the rows making all column averages
strictly negative. -/
theorem exists_dist_nonneg_or_dist_neg [Nonempty A] [Nonempty I] (M : A → I → ℝ) :
    (∃ q ∈ stdSimplex ℝ I, ∀ a, 0 ≤ ∑ i, q i * M a i) ∨
    (∃ p ∈ stdSimplex ℝ A, ∀ i, ∑ a, p a * M a i < 0) := by
  classical
  by_cases hcase : ∃ q ∈ stdSimplex ℝ I, ∀ a, 0 ≤ ∑ i, q i * M a i
  · exact Or.inl hcase
  refine Or.inr ?_
  push_neg at hcase
  -- The linear map sending an input distribution `q` to the vector of expected costs.
  set L : (I → ℝ) →ₗ[ℝ] (A → ℝ) :=
    { toFun := fun q a => ∑ i, q i * M a i
      map_add' := by intro x y; funext a; simp [← Finset.sum_add_distrib, add_mul]
      map_smul' := by intro c x; funext a; simp [Finset.mul_sum, mul_assoc] } with hL
  have hLdef : ∀ (q : I → ℝ) (a : A), L q a = ∑ i, q i * M a i := fun q a => rfl
  set K : Set (A → ℝ) := L '' (stdSimplex ℝ I) with hK
  set P : Set (A → ℝ) := {y : A → ℝ | ∀ a, 0 ≤ y a} with hP
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ I).linear_image L
  have hKcomp : IsCompact K := (isCompact_stdSimplex I).image L.continuous_of_finiteDimensional
  have hPconv : Convex ℝ P := by
    intro x hx y hy s t hs ht _ a
    have h1 := hx a
    have h2 := hy a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h3 := mul_nonneg hs h1
    have h4 := mul_nonneg ht h2
    linarith
  have hPclosed : IsClosed P := by
    have hPeq : P = ⋂ a, {y : A → ℝ | 0 ≤ y a} := by ext y; simp [hP]
    rw [hPeq]
    exact isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)
  have hdisj : Disjoint K P := by
    rw [Set.disjoint_left]
    rintro _ ⟨q, hq, rfl⟩ hmem
    obtain ⟨a, ha⟩ := hcase q hq
    have h := hmem a
    rw [hLdef] at h
    linarith
  obtain ⟨f, u, v, hfK, huv, hfP⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hPconv hPclosed hdisj
  -- The separating functional has nonnegative coefficients, giving the desired distribution.
  set p : A → ℝ := fun a => f (Pi.single a 1) with hp
  have hv0 : v < 0 := by
    have := hfP 0 (fun a => le_refl 0)
    simpa using this
  have hpnonneg : ∀ a, 0 ≤ p a := by
    intro a
    by_contra hlt
    push_neg at hlt
    have hne : p a ≠ 0 := ne_of_lt hlt
    set t : ℝ := v / p a + 1 with ht
    have ht0 : 0 ≤ t := by
      have : 0 < v / p a := div_pos_of_neg_of_neg hv0 hlt
      linarith
    have hmem : (t • (Pi.single a (1:ℝ) : A → ℝ)) ∈ P := by
      intro b
      rcases eq_or_ne b a with rfl | hb
      · simpa using ht0
      · simp [hb]
    have h1 := hfP _ hmem
    rw [map_smul] at h1
    have h2 : t * p a = v + p a := by
      rw [ht, add_mul, one_mul, div_mul_cancel₀ _ hne]
    simp only [smul_eq_mul] at h1
    rw [h2] at h1
    linarith
  have hfx : ∀ x : A → ℝ, f x = ∑ a, x a * p a := by
    intro x
    have hx : x = ∑ a, x a • (Pi.single a (1:ℝ) : A → ℝ) := by
      funext b
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hx]
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul]; simp [hp]
  have key : ∀ i, ∑ a, p a * M a i < 0 := by
    intro i
    have hδ : (Pi.single i (1:ℝ) : I → ℝ) ∈ stdSimplex ℝ I := by
      refine ⟨fun j => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · simp
        · simp [hj]
      · simp
    have h1 := hfK _ ⟨_, hδ, rfl⟩
    have h2 : f (L (Pi.single i (1:ℝ) : I → ℝ)) = ∑ a, p a * M a i := by
      rw [hfx]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hLdef]
      simp [Pi.single_apply, mul_comm]
    rw [h2] at h1
    linarith
  have hSnonneg : 0 ≤ ∑ a, p a := Finset.sum_nonneg fun a _ => hpnonneg a
  have hS : 0 < ∑ a, p a := by
    rcases hSnonneg.lt_or_eq with h | h
    · exact h
    · exfalso
      obtain ⟨i⟩ := ‹Nonempty I›
      have hall : ∀ a ∈ Finset.univ, p a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hpnonneg a).1 h.symm
      have hk := key i
      rw [Finset.sum_congr rfl fun a ha => by rw [hall a ha, zero_mul]] at hk
      simp at hk
  refine ⟨fun a => p a / (∑ a, p a), ⟨fun a => div_nonneg (hpnonneg a) hS.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, div_self (ne_of_gt hS)]
  · intro i
    have h3 : ∑ a, p a / (∑ a, p a) * M a i = (∑ a, p a * M a i) / (∑ a, p a) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [h3]
    exact div_neg_of_neg_of_pos (key i) hS

end Alternative

section Main

variable [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- Uniform bounds on all the entries of the cost matrix. -/
lemma exists_cost_bounds (cost : A → I → ℝ) :
    ∃ m M : ℝ, ∀ a i, m ≤ cost a i ∧ cost a i ≤ M := by
  obtain ⟨x, hx⟩ := Finite.exists_min (fun x : A × I => cost x.1 x.2)
  obtain ⟨y, hy⟩ := Finite.exists_max (fun x : A × I => cost x.1 x.2)
  exact ⟨cost x.1 x.2, cost y.1 y.2, fun a i => ⟨hx (a, i), hy (a, i)⟩⟩

omit [Nonempty A] [Nonempty I] in
lemma bddAbove_randCost (cost : A → I → ℝ) (p : A → ℝ) :
    BddAbove (Set.range fun i => randCost cost p i) := Finite.bddAbove_range _

omit [Nonempty A] [Nonempty I] in
lemma bddBelow_distCost (cost : A → I → ℝ) (q : I → ℝ) :
    BddBelow (Set.range fun a => distCost cost a q) := Finite.bddBelow_range _

lemma bddBelow_maxRand (cost : A → I → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => ⨆ i, randCost cost (p : A → ℝ) i) := by
  obtain ⟨m, M, hm⟩ := exists_cost_bounds cost
  refine ⟨m, ?_⟩
  rintro _ ⟨p, rfl⟩
  obtain ⟨i⟩ := ‹Nonempty I›
  refine le_trans ?_ (le_ciSup (bddAbove_randCost cost (p : A → ℝ)) i)
  exact le_convex_comb p.2 fun a => (hm a i).1

lemma bddAbove_minDist (cost : A → I → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ I => ⨅ a, distCost cost a (q : I → ℝ)) := by
  obtain ⟨m, M, hm⟩ := exists_cost_bounds cost
  refine ⟨M, ?_⟩
  rintro _ ⟨q, rfl⟩
  obtain ⟨a⟩ := ‹Nonempty A›
  refine le_trans (ciInf_le (bddBelow_distCost cost (q : I → ℝ)) a) ?_
  exact convex_comb_le q.2 fun i => (hm a i).2

/-- Weak duality: the distributional complexity is at most the randomized complexity. -/
lemma sup_inf_le_inf_sup (cost : A → I → ℝ) :
    ⨆ q : stdSimplex ℝ I, ⨅ a, distCost cost a (q : I → ℝ) ≤
      ⨅ p : stdSimplex ℝ A, ⨆ i, randCost cost (p : A → ℝ) i := by
  refine ciSup_le fun q => le_ciInf fun p => ?_
  have h1 : (⨅ a, distCost cost a (q : I → ℝ)) ≤ ∑ a, (p : A → ℝ) a * distCost cost a q :=
    le_convex_comb p.2 fun a => ciInf_le (bddBelow_distCost cost (q : I → ℝ)) a
  have h2 : ∑ i, (q : I → ℝ) i * randCost cost (p : A → ℝ) i ≤ ⨆ i, randCost cost (p : A → ℝ) i :=
    convex_comb_le q.2 fun i => le_ciSup (bddAbove_randCost cost (p : A → ℝ)) i
  rw [exchange] at h2
  exact h1.trans h2

/-- **Yao's minimax principle**: for a finite set `A` of deterministic algorithms and a finite set
`I` of inputs with cost matrix `cost`, the randomized complexity (the least, over distributions `p`
over algorithms, of the worst-case expected cost) equals the distributional complexity (the
greatest, over distributions `q` over inputs, of the best expected cost of a deterministic
algorithm). -/
theorem yao_principle (cost : A → I → ℝ) :
    ⨅ p : stdSimplex ℝ A, ⨆ i, randCost cost (p : A → ℝ) i =
      ⨆ q : stdSimplex ℝ I, ⨅ a, distCost cost a (q : I → ℝ) := by
  refine le_antisymm ?_ (sup_inf_le_inf_sup cost)
  by_contra hlt
  push_neg at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  rcases exists_dist_nonneg_or_dist_neg (fun a i => cost a i - c) with ⟨q, hq, h⟩ | ⟨p, hp, h⟩
  · -- the input distribution `q` forces every algorithm to pay at least `c`
    have hq' : ∀ a, c ≤ distCost cost a q := by
      intro a
      have := h a
      have hsum : ∑ i, q i * (cost a i - c) = distCost cost a q - c := by
        simp only [distCost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq.2, one_mul]
      linarith [hsum ▸ this]
    have : c ≤ ⨅ a, distCost cost a q := le_ciInf hq'
    have h2 : (⨅ a, distCost cost a (⟨q, hq⟩ : stdSimplex ℝ I).1) ≤
        ⨆ q : stdSimplex ℝ I, ⨅ a, distCost cost a (q : I → ℝ) :=
      le_ciSup (bddAbove_minDist cost) (⟨q, hq⟩ : stdSimplex ℝ I)
    linarith
  · -- the algorithm distribution `p` pays strictly less than `c` on every input
    have hp' : ∀ i, randCost cost p i < c := by
      intro i
      have := h i
      have hsum : ∑ a, p a * (cost a i - c) = randCost cost p i - c := by
        simp only [randCost, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul]
      linarith [hsum ▸ this]
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => randCost cost p i)
    have hsup : (⨆ i, randCost cost p i) < c :=
      lt_of_le_of_lt (ciSup_le hi₀) (hp' i₀)
    have h2 : (⨅ p : stdSimplex ℝ A, ⨆ i, randCost cost (p : A → ℝ) i) ≤
        ⨆ i, randCost cost (⟨p, hp⟩ : stdSimplex ℝ A).1 i :=
      ciInf_le (bddBelow_maxRand cost) (⟨p, hp⟩ : stdSimplex ℝ A)
    simp only at h2
    linarith

/-- Sanity check: for a constant cost matrix, the randomized complexity is that constant
(in particular the infimum/supremum above are not junk values). -/
example (c : ℝ) :
    ⨅ p : stdSimplex ℝ A, ⨆ _i : I, randCost (fun (_ : A) (_ : I) => c) (p : A → ℝ) _i = c := by
  have h : ∀ p : stdSimplex ℝ A,
      (⨆ _i : I, randCost (fun (_ : A) (_ : I) => c) (p : A → ℝ) _i) = c := by
    intro p
    have hc : ∀ i : I, randCost (fun (_ : A) (_ : I) => c) (p : A → ℝ) i = c := fun i => by
      simp [randCost, ← Finset.sum_mul]
    simp [hc]
  simp [h]

/-- Sanity check: for a constant cost matrix, the distributional complexity is that constant. -/
example (c : ℝ) :
    ⨆ q : stdSimplex ℝ I, ⨅ _a : A, distCost (fun (_ : A) (_ : I) => c) _a (q : I → ℝ) = c := by
  have h : ∀ q : stdSimplex ℝ I,
      (⨅ _a : A, distCost (fun (_ : A) (_ : I) => c) _a (q : I → ℝ)) = c := by
    intro q
    have hc : ∀ a : A, distCost (fun (_ : A) (_ : I) => c) a (q : I → ℝ) = c := fun a => by
      simp [distCost, ← Finset.sum_mul]
    simp [hc]
  simp [h]

end Main

end CS

