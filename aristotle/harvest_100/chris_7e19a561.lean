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

open Set

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over the
deterministic algorithms `A`, run on the input `i`. -/
def expCostAlg (c : A → I → ℝ) (p : A → ℝ) (i : I) : ℝ := ∑ a, p a * c a i

/-- The expected cost of the deterministic algorithm `a` on an input drawn from the
distribution `q` over the inputs `I`. -/
def expCostInp (c : A → I → ℝ) (q : I → ℝ) (a : A) : ℝ := ∑ i, q i * c a i

/-- The randomized complexity of the cost matrix `c`: the best (over randomized algorithms,
i.e. distributions over deterministic algorithms) worst-case (over inputs) expected cost. -/
noncomputable def randComplexity (c : A → I → ℝ) : ℝ :=
  ⨅ p : stdSimplex ℝ A, ⨆ i, expCostAlg c (p : A → ℝ) i

/-- The distributional complexity of the cost matrix `c`: the worst (over input distributions)
best-case (over deterministic algorithms) expected cost. -/
noncomputable def distComplexity (c : A → I → ℝ) : ℝ :=
  ⨆ q : stdSimplex ℝ I, ⨅ a, expCostInp c (q : I → ℝ) a

instance instNonemptyStdSimplex [Nonempty A] : Nonempty (stdSimplex ℝ A) :=
  ⟨⟨Pi.single (Classical.arbitrary A) 1, single_mem_stdSimplex ℝ _⟩⟩

section Weighted

variable {X : Type*} [Fintype X] {w f : X → ℝ}

lemma le_wsum (hw : w ∈ stdSimplex ℝ X) {m : ℝ} (hm : ∀ x, m ≤ f x) :
    m ≤ ∑ x, w x * f x := by
  have h1 : ∑ x, w x * m ≤ ∑ x, w x * f x :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hm x) (hw.1 x)
  have h2 : ∑ x, w x * m = m := by rw [← Finset.sum_mul, hw.2, one_mul]
  linarith

lemma wsum_le (hw : w ∈ stdSimplex ℝ X) {M : ℝ} (hM : ∀ x, f x ≤ M) :
    ∑ x, w x * f x ≤ M := by
  have h1 : ∑ x, w x * f x ≤ ∑ x, w x * M :=
    Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hM x) (hw.1 x)
  have h2 : ∑ x, w x * M = M := by rw [← Finset.sum_mul, hw.2, one_mul]
  linarith

end Weighted

section Basic

variable {c : A → I → ℝ}

omit [Fintype I] in
lemma expCostAlg_single (a : A) (i : I) : expCostAlg c (Pi.single a 1) i = c a i := by
  simp [expCostAlg, Pi.single_apply, Finset.sum_ite_eq']

omit [Fintype A] in
lemma expCostInp_single (a : A) (i : I) : expCostInp c (Pi.single i 1) a = c a i := by
  simp [expCostInp, Pi.single_apply, Finset.sum_ite_eq']

/-- Fubini: averaging the algorithm-side expected cost over `q` is the same as averaging the
input-side expected cost over `p`. -/
lemma exchange (p : A → ℝ) (q : I → ℝ) :
    ∑ i, q i * expCostAlg c p i = ∑ a, p a * expCostInp c q a := by
  simp only [expCostAlg, expCostInp, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring

lemma bddBelow_expCostAlg_sup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => ⨆ i, expCostAlg c (p : A → ℝ) i) := by
  refine ⟨⨅ x : A × I, c x.1 x.2, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hm : ∀ x : A × I, (⨅ x : A × I, c x.1 x.2) ≤ c x.1 x.2 := fun x =>
    ciInf_le (Finite.bddBelow_range fun x : A × I => c x.1 x.2) x
  have h1 : (⨅ x : A × I, c x.1 x.2) ≤ expCostAlg c (p : A → ℝ) (Classical.arbitrary I) :=
    le_wsum p.2 fun a => hm (a, Classical.arbitrary I)
  exact h1.trans (le_ciSup (Finite.bddAbove_range _) (Classical.arbitrary I))

lemma bddAbove_expCostInp_inf [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ I => ⨅ a, expCostInp c (q : I → ℝ) a) := by
  refine ⟨⨆ x : A × I, c x.1 x.2, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hM : ∀ x : A × I, c x.1 x.2 ≤ ⨆ x : A × I, c x.1 x.2 := fun x =>
    le_ciSup (Finite.bddAbove_range fun x : A × I => c x.1 x.2) x
  have h1 : expCostInp c (q : I → ℝ) (Classical.arbitrary A) ≤ ⨆ x : A × I, c x.1 x.2 :=
    wsum_le q.2 fun i => hM (Classical.arbitrary A, i)
  exact le_trans (ciInf_le (Finite.bddBelow_range _) (Classical.arbitrary A)) h1

/-- Weak duality: for any randomized algorithm `p` and any input distribution `q`, the best
deterministic algorithm against `q` does no worse than `p` does in the worst case. -/
lemma inf_expCostInp_le_sup_expCostAlg [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    (⨅ a, expCostInp c q a) ≤ ⨆ i, expCostAlg c p i := by
  have h1 : (⨅ a, expCostInp c q a) ≤ ∑ a, p a * expCostInp c q a :=
    le_wsum hp fun a => ciInf_le (Finite.bddBelow_range _) a
  have h2 : ∑ i, q i * expCostAlg c p i ≤ ⨆ i, expCostAlg c p i :=
    wsum_le hq fun i => le_ciSup (Finite.bddAbove_range _) i
  rw [exchange p q] at h2
  linarith

end Basic

/-- **Key separation lemma.** If every randomized algorithm has expected cost more than `v`
on some input, then there is a single input distribution `q` against which *every* deterministic
algorithm has expected cost more than `v`. -/
lemma exists_input_dist_of_forall_alg [Nonempty A] [Nonempty I] (c : A → I → ℝ) (v : ℝ)
    (h : ∀ p ∈ stdSimplex ℝ A, ∃ i, v < expCostAlg c p i) :
    ∃ q ∈ stdSimplex ℝ I, ∀ a, v < expCostInp c q a := by
  classical
  set g : (A → ℝ) → (I → ℝ) := fun p i => expCostAlg c p i with hgdef
  set K : Set (I → ℝ) := g '' stdSimplex ℝ A with hKdef
  set Q : Set (I → ℝ) := {y : I → ℝ | ∀ i, 0 ≤ y i} with hQdef
  set C : Set (I → ℝ) := K + Q with hCdef
  -- `C` is the set of cost vectors dominating some randomized algorithm's cost vector
  have hmemC : ∀ y : I → ℝ, y ∈ C ↔ ∃ p ∈ stdSimplex ℝ A, ∀ i, expCostAlg c p i ≤ y i := by
    intro y
    rw [hCdef, Set.mem_add]
    constructor
    · rintro ⟨k, ⟨p, hp, rfl⟩, z, hz, rfl⟩
      refine ⟨p, hp, fun i => ?_⟩
      have hzi : (0 : ℝ) ≤ z i := hz i
      show expCostAlg c p i ≤ g p i + z i
      have : g p i = expCostAlg c p i := rfl
      linarith
    · rintro ⟨p, hp, hle⟩
      refine ⟨g p, ⟨p, hp, rfl⟩, y - g p, fun i => ?_, by funext i; simp⟩
      have := hle i
      simpa [hgdef] using sub_nonneg.2 this
  -- closedness
  have hgcont : Continuous g := by
    apply continuous_pi
    intro i
    exact continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const
  have hKcompact : IsCompact K := (isCompact_stdSimplex A).image hgcont
  have hQclosed : IsClosed Q := by
    have hQeq : Q = ⋂ i : I, (fun y : I → ℝ => y i) ⁻¹' (Set.Ici (0 : ℝ)) := by
      ext y; simp [hQdef]
    rw [hQeq]
    exact isClosed_iInter fun i => isClosed_Ici.preimage (continuous_apply i)
  have hCclosed : IsClosed C := hQclosed.add_left_of_isCompact hKcompact
  -- convexity
  have hCconv : Convex ℝ C := by
    intro y₁ hy₁ y₂ hy₂ s t hs ht hst
    rw [hmemC] at hy₁ hy₂
    rw [hmemC]
    obtain ⟨p₁, hp₁, k₁⟩ := hy₁
    obtain ⟨p₂, hp₂, k₂⟩ := hy₂
    refine ⟨s • p₁ + t • p₂, convex_stdSimplex ℝ A hp₁ hp₂ hs ht hst, fun i => ?_⟩
    have hlin : expCostAlg c (s • p₁ + t • p₂) i
        = s * expCostAlg c p₁ i + t * expCostAlg c p₂ i := by
      simp only [expCostAlg, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by simp [Pi.add_apply, Pi.smul_apply]; ring
    have h1 := mul_le_mul_of_nonneg_left (k₁ i) hs
    have h2 := mul_le_mul_of_nonneg_left (k₂ i) ht
    have : (s • y₁ + t • y₂) i = s * y₁ i + t * y₂ i := by simp
    rw [hlin, this]
    linarith
  -- the constant vector `v` is not in `C`
  have hx₀ : (fun _ : I => v) ∉ C := by
    rw [hmemC]
    rintro ⟨p, hp, hle⟩
    obtain ⟨i, hi⟩ := h p hp
    exact absurd (hle i) (not_le.2 hi)
  -- upward closure of `C`
  have hup : ∀ y ∈ C, ∀ z : I → ℝ, (∀ i, y i ≤ z i) → z ∈ C := by
    intro y hy z hz
    rw [hmemC] at hy ⊢
    obtain ⟨p, hp, hle⟩ := hy
    exact ⟨p, hp, fun i => (hle i).trans (hz i)⟩
  have hcC : ∀ a : A, (fun i => c a i) ∈ C := by
    intro a
    rw [hmemC]
    exact ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, fun i => by rw [expCostAlg_single]⟩
  -- separate
  obtain ⟨f, u, hfx, hfC⟩ := geometric_hahn_banach_point_closed hCconv hCclosed hx₀
  set lam : I → ℝ := fun i => f (Pi.single i (1 : ℝ) : I → ℝ) with hlamdef
  have hf_apply : ∀ y : I → ℝ, f y = ∑ i, y i * lam i := by
    intro y
    have hy : y = ∑ i, y i • (Pi.single i (1 : ℝ) : I → ℝ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
    conv_lhs => rw [hy]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; simp [hlamdef, smul_eq_mul]
  -- the separating functional has nonnegative coefficients
  have hlamnn : ∀ i, 0 ≤ lam i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set a₀ := Classical.arbitrary A with ha₀
    set y : I → ℝ := fun j => c a₀ j with hy
    have hyC : y ∈ C := hcC a₀
    have hfy : u < f y := hfC y hyC
    set s : ℝ := (f y - u) / (-lam i) with hs
    have hs0 : 0 ≤ s := div_nonneg (by linarith) (by linarith)
    have hzC : (y + s • (Pi.single i (1 : ℝ) : I → ℝ)) ∈ C := by
      refine hup y hyC _ fun j => ?_
      have hnn : (0 : ℝ) ≤ s * (Pi.single i (1 : ℝ) : I → ℝ) j := by
        refine mul_nonneg hs0 ?_
        rcases eq_or_ne i j with rfl | hij
        · simp
        · simp [hij]
      simpa using hnn
    have hgt := hfC _ hzC
    rw [map_add, map_smul] at hgt
    have hne : lam i ≠ 0 := ne_of_lt hneg
    have hsl : s * lam i = -(f y - u) := by
      rw [hs]
      field_simp
    simp only [smul_eq_mul] at hgt
    linarith
  set S : ℝ := ∑ i, lam i with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hlamnn i
  have hSpos : 0 < S := by
    rcases lt_or_eq_of_le hS0 with hlt | heq
    · exact hlt
    · exfalso
      have hall : ∀ i ∈ (Finset.univ : Finset I), lam i = 0 := by
        refine (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hlamnn i).1 ?_
        rw [← hSdef, ← heq]
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y
        rw [hf_apply y]
        exact Finset.sum_eq_zero fun i _ => by rw [hall i (Finset.mem_univ i), mul_zero]
      have h1 : (0 : ℝ) < u := by
        have := hfx
        rw [hf0] at this
        exact this
      have h2 : u < 0 := by
        have := hfC _ (hcC (Classical.arbitrary A))
        rw [hf0] at this
        exact this
      linarith
  refine ⟨fun i => lam i / S, ⟨fun i => div_nonneg (hlamnn i) hSpos.le, ?_⟩, fun a => ?_⟩
  · rw [← Finset.sum_div, ← hSdef]
    field_simp
  · have h1 : u < ∑ i, c a i * lam i := by
      have := hfC _ (hcC a)
      rwa [hf_apply] at this
    have h2 : v * S < u := by
      have := hfx
      rw [hf_apply] at this
      simpa [hSdef, Finset.mul_sum] using this
    have h3 : v * S < ∑ i, c a i * lam i := lt_trans h2 h1
    have h4 : expCostInp c (fun i => lam i / S) a = (∑ i, c a i * lam i) / S := by
      rw [expCostInp, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h4, lt_div_iff₀ hSpos]
    exact h3

/-- **Yao's minimax principle.** For a finite cost matrix `c : A → I → ℝ`, the randomized
complexity (the minimum over distributions on deterministic algorithms of the worst-case
expected cost) equals the distributional complexity (the maximum over input distributions of
the best deterministic algorithm's expected cost). -/
theorem yao_principle [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    randComplexity c = distComplexity c := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_lt fun v hv => ?_
    have hkey : ∀ p ∈ stdSimplex ℝ A, ∃ i, v < expCostAlg c p i := by
      intro p hp
      have hle : randComplexity c ≤ ⨆ i, expCostAlg c p i :=
        ciInf_le (bddBelow_expCostAlg_sup c) (⟨p, hp⟩ : stdSimplex ℝ A)
      obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => expCostAlg c p i)
      exact ⟨i, by rw [hi]; linarith⟩
    obtain ⟨q, hq, hqa⟩ := exists_input_dist_of_forall_alg c v hkey
    obtain ⟨a, ha⟩ := exists_eq_ciInf_of_finite (f := fun a => expCostInp c q a)
    have hlt : v < ⨅ a, expCostInp c q a := by rw [← ha]; exact hqa a
    exact lt_of_lt_of_le hlt (le_ciSup (bddAbove_expCostInp_inf c) (⟨q, hq⟩ : stdSimplex ℝ I))
  · exact ciSup_le fun q => le_ciInf fun p =>
      inf_expCostInp_le_sup_expCostAlg c p.2 q.2

end CS

