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

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import RequestProject.Math2.Defs

/-!
Elementary finite-probability toolkit for `p`-random subsets: the expectation `Ex p f`,
the fact that the weights sum to one, and the "union of independent random sets" identity.
-/

namespace Math2

open Finset

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The expectation of `f` at a `p`-random subset of the ground set `s`. -/
noncomputable def ExS (s : Finset X) (p : ℝ) (f : Finset X → ℝ) : ℝ :=
  ∑ W ∈ s.powerset, p ^ W.card * (1 - p) ^ (s.card - W.card) * f W

lemma ExS_empty (p : ℝ) (f : Finset X → ℝ) : ExS ∅ p f = f ∅ := by
  simp [ExS]

lemma ExS_insert {a : X} {s : Finset X} (ha : a ∉ s) (p : ℝ) (f : Finset X → ℝ) :
    ExS (insert a s) p f = p * ExS s p (fun W => f (insert a W)) + (1 - p) * ExS s p f := by
  classical
  have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
    refine Finset.disjoint_left.2 ?_
    rintro W hW hW'
    rw [Finset.mem_image] at hW'
    obtain ⟨V, hV, hVW⟩ := hW'
    rw [Finset.mem_powerset] at hW
    exact ha (hW (hVW ▸ Finset.mem_insert_self a V))
  have hinj : ∀ W ∈ s.powerset, ∀ V ∈ s.powerset, insert a W = insert a V → W = V := by
    intro W hW V hV h
    rw [Finset.mem_powerset] at hW hV
    have haW : a ∉ W := fun hh => ha (hW hh)
    have haV : a ∉ V := fun hh => ha (hV hh)
    rw [← Finset.erase_insert haW, ← Finset.erase_insert haV, h]
  rw [ExS, Finset.powerset_insert, Finset.sum_union hdisj,
    Finset.sum_image hinj]
  have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
  have h1 : ∀ W ∈ s.powerset,
      p ^ W.card * (1 - p) ^ ((insert a s).card - W.card) * f W
        = (1 - p) * (p ^ W.card * (1 - p) ^ (s.card - W.card) * f W) := by
    intro W hW
    rw [Finset.mem_powerset] at hW
    have hle : W.card ≤ s.card := Finset.card_le_card hW
    rw [hcard]
    have : s.card + 1 - W.card = (s.card - W.card) + 1 := by omega
    rw [this, pow_succ]
    ring
  have h2 : ∀ W ∈ s.powerset,
      p ^ (insert a W).card * (1 - p) ^ ((insert a s).card - (insert a W).card) * f (insert a W)
        = p * (p ^ W.card * (1 - p) ^ (s.card - W.card) * f (insert a W)) := by
    intro W hW
    rw [Finset.mem_powerset] at hW
    have haW : a ∉ W := fun hh => ha (hW hh)
    rw [Finset.card_insert_of_notMem haW, hcard]
    have : s.card + 1 - (W.card + 1) = s.card - W.card := by omega
    rw [this, pow_succ]
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [ExS, ExS]
  ring

lemma ExS_add (s : Finset X) (p : ℝ) (f g : Finset X → ℝ) :
    ExS s p (fun W => f W + g W) = ExS s p f + ExS s p g := by
  simp only [ExS, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun W _ => by ring

lemma ExS_const_mul (s : Finset X) (p c : ℝ) (f : Finset X → ℝ) :
    ExS s p (fun W => c * f W) = c * ExS s p f := by
  simp only [ExS, Finset.mul_sum]
  exact Finset.sum_congr rfl fun W _ => by ring

lemma ExS_one (s : Finset X) (p : ℝ) : ExS s p (fun _ => (1:ℝ)) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ExS]
  | insert a s ha ih =>
      rw [ExS_insert ha]
      simp only [ih]
      ring

lemma ExS_zero_param (s : Finset X) (f : Finset X → ℝ) : ExS s 0 f = f ∅ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ExS]
  | insert a s ha ih =>
      rw [ExS_insert ha]
      simp only [ih]
      ring

/-- The union of an independent `p`-random set and `q`-random set is `(p+q-pq)`-random. -/
lemma ExS_union (s : Finset X) (p q : ℝ) :
    ∀ f : Finset X → ℝ,
      ExS s p (fun W => ExS s q (fun V => f (W ∪ V))) = ExS s (p + q - p * q) f := by
  classical
  induction s using Finset.induction_on with
  | empty => intro f; simp [ExS_empty]
  | insert a s ha ih =>
      intro f
      have key : ∀ W : Finset X,
          ExS (insert a s) q (fun V => f (insert a W ∪ V))
            = ExS s q (fun V => f (insert a (W ∪ V))) := by
        intro W
        rw [ExS_insert ha]
        have e1 : (fun V => f (insert a W ∪ insert a V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.insert_union, Finset.union_insert, Finset.insert_idem]
        have e2 : (fun V => f (insert a W ∪ V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.insert_union]
        rw [e1, e2]
        ring
      have key2 : ∀ W : Finset X,
          ExS (insert a s) q (fun V => f (W ∪ V))
            = q * ExS s q (fun V => f (insert a (W ∪ V)))
              + (1 - q) * ExS s q (fun V => f (W ∪ V)) := by
        intro W
        rw [ExS_insert ha]
        have e1 : (fun V => f (W ∪ insert a V)) = fun V => f (insert a (W ∪ V)) := by
          funext V
          congr 1
          rw [Finset.union_insert]
        rw [e1]
      rw [ExS_insert ha]
      simp only [key, key2]
      rw [ExS_add s p (fun W => q * ExS s q fun V => f (insert a (W ∪ V)))
        (fun W => (1 - q) * ExS s q fun V => f (W ∪ V))]
      rw [ExS_const_mul s p q (fun W => ExS s q fun V => f (insert a (W ∪ V))),
        ExS_const_mul s p (1 - q) (fun W => ExS s q fun V => f (W ∪ V))]
      rw [ih (fun U => f (insert a U)), ih f]
      rw [ExS_insert ha (p + q - p * q) f]
      ring

/-- `Ex` is `ExS` over the whole ground set. -/
lemma Ex_eq_ExS (p : ℝ) (f : Finset X → ℝ) : Ex p f = ExS univ p f := by
  simp only [Ex, ExS, wt, Finset.powerset_univ, Finset.card_univ]

lemma Ex_one (p : ℝ) : Ex (X := X) p (fun _ => (1:ℝ)) = (1:ℝ) := by
  rw [Ex_eq_ExS]; exact ExS_one _ _

lemma sum_wt (p : ℝ) : ∑ W : Finset X, wt p W = 1 := by
  have h := Ex_one (X := X) p
  simpa [Ex] using h

lemma Ex_const (p c : ℝ) : Ex (X := X) p (fun _ => c) = c := by
  have : Ex (X := X) p (fun _ => c) = ∑ W : Finset X, c * wt p W := by
    simp only [Ex]; exact Finset.sum_congr rfl fun W _ => by ring
  rw [this, ← Finset.mul_sum, sum_wt]
  ring

lemma Ex_add (p : ℝ) (f g : Finset X → ℝ) :
    Ex p (fun W => f W + g W) = Ex p f + Ex p g := by
  rw [Ex_eq_ExS, Ex_eq_ExS, Ex_eq_ExS]; exact ExS_add _ _ _ _

lemma Ex_const_mul (p c : ℝ) (f : Finset X → ℝ) :
    Ex p (fun W => c * f W) = c * Ex p f := by
  rw [Ex_eq_ExS, Ex_eq_ExS]; exact ExS_const_mul _ _ _ _

lemma wt_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (W : Finset X) : 0 ≤ wt p W :=
  mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)

lemma Ex_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {f g : Finset X → ℝ}
    (h : ∀ W, f W ≤ g W) : Ex p f ≤ Ex p g := by
  refine Finset.sum_le_sum fun W _ => ?_
  exact mul_le_mul_of_nonneg_left (h W) (wt_nonneg hp0 hp1 W)

lemma Ex_union (p q : ℝ) (f : Finset X → ℝ) :
    Ex p (fun W => Ex q (fun V => f (W ∪ V))) = Ex (p + q - p * q) f := by
  rw [Ex_eq_ExS]
  have : (fun W => Ex q (fun V => f (W ∪ V))) = fun W => ExS univ q (fun V => f (W ∪ V)) := by
    funext W; rw [Ex_eq_ExS]
  rw [this, ExS_union univ p q f, ← Ex_eq_ExS]

lemma Ex_zero_param (f : Finset X → ℝ) : Ex 0 f = f ∅ := by
  rw [Ex_eq_ExS]; exact ExS_zero_param _ _

/-- The expectation of `f` at the union of `k` independent `p`-random subsets. -/
noncomputable def ExIter (p : ℝ) : ℕ → (Finset X → ℝ) → ℝ
  | 0, f => f ∅
  | (k+1), f => Ex p (fun W => ExIter p k (fun V => f (W ∪ V)))

/-- The union of `k` independent `p`-random sets is `(1-(1-p)^k)`-random. -/
lemma ExIter_eq (p : ℝ) : ∀ (k : ℕ) (f : Finset X → ℝ),
    ExIter p k f = Ex (1 - (1 - p) ^ k) f := by
  intro k
  induction k with
  | zero => intro f; simp [ExIter, Ex_zero_param]
  | succ k ih =>
      intro f
      rw [ExIter]
      have : (fun W => ExIter p k (fun V => f (W ∪ V)))
          = fun W => Ex (1 - (1 - p) ^ k) (fun V => f (W ∪ V)) := by
        funext W; rw [ih]
      rw [this, Ex_union]
      congr 1
      ring

end Math2

/-
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
Basic definitions for the Kahn–Kalai theorem (Park–Pham).

Throughout, `X` is a finite ground set, subsets of `X` are elements of `Finset X`, and a
*hypergraph* (or family) on `X` is an element of `Finset (Finset X)`.
-/

namespace Math2

open Finset

open scoped Classical

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The weight of `W` under the product measure `μ_p` on subsets of `X`:
`μ_p({W}) = p ^ |W| * (1-p) ^ |X \ W|`. -/
noncomputable def wt (p : ℝ) (W : Finset X) : ℝ :=
  p ^ W.card * (1 - p) ^ (Fintype.card X - W.card)

/-- The expectation of `f` evaluated at a `p`-random subset of `X`. -/
noncomputable def Ex (p : ℝ) (f : Finset X → ℝ) : ℝ := ∑ W : Finset X, wt p W * f W

/-- `mu p A` is the probability that a `p`-random subset of `X` lies in the family `A`. -/
noncomputable def mu (p : ℝ) (A : Finset (Finset X)) : ℝ := ∑ W ∈ A, wt p W

/-- The up-closure `⟨H⟩ = ⋃_{S ∈ H} {T : T ⊇ S}` of a family `H`. -/
noncomputable def upSet (H : Finset (Finset X)) : Finset (Finset X) :=
  univ.filter (fun W => ∃ S ∈ H, S ⊆ W)

/-- `G` is a cover of `H`: every edge of `H` contains an edge of `G`. -/
def Covers (G H : Finset (Finset X)) : Prop := ∀ S ∈ H, ∃ T ∈ G, T ⊆ S

/-- The cost `∑_{S ∈ G} p ^ |S|` of a family `G`. -/
noncomputable def cost (p : ℝ) (G : Finset (Finset X)) : ℝ := ∑ S ∈ G, p ^ S.card

/-- `H` is `p`-small if it admits a cover of cost at most `1/2`. -/
def IsSmall (p : ℝ) (H : Finset (Finset X)) : Prop :=
  ∃ G : Finset (Finset X), Covers G H ∧ cost p G ≤ 1 / 2

/-- The (finite, nonempty) family of all covers of `H`. -/
noncomputable def coverFams (H : Finset (Finset X)) : Finset (Finset (Finset X)) :=
  univ.filter (fun G => Covers G H)

lemma coverFams_nonempty (H : Finset (Finset X)) :
    ((coverFams H).image (cost p)).Nonempty := by
  refine Finset.Nonempty.image ⟨H, ?_⟩ _
  simp only [coverFams, mem_filter, mem_univ, true_and]
  intro S hS
  exact ⟨S, hS, subset_rfl⟩

/-- The minimal cost of a cover of `H`. -/
noncomputable def mcost (p : ℝ) (H : Finset (Finset X)) : ℝ :=
  ((coverFams H).image (cost p)).min' (coverFams_nonempty H)

section basic

variable {p : ℝ} {G H : Finset (Finset X)}

lemma mem_upSet {W : Finset X} : W ∈ upSet H ↔ ∃ S ∈ H, S ⊆ W := by
  simp [upSet]

lemma cost_nonneg (hp : 0 ≤ p) (G : Finset (Finset X)) : 0 ≤ cost p G :=
  Finset.sum_nonneg fun _ _ => pow_nonneg hp _

lemma cost_union_le (hp : 0 ≤ p) (G₁ G₂ : Finset (Finset X)) :
    cost p (G₁ ∪ G₂) ≤ cost p G₁ + cost p G₂ := by
  classical
  have h := Finset.sum_union_inter (s₁ := G₁) (s₂ := G₂) (f := fun S : Finset X => p ^ S.card)
  have h2 : (0:ℝ) ≤ ∑ S ∈ G₁ ∩ G₂, p ^ S.card :=
    Finset.sum_nonneg fun _ _ => pow_nonneg hp _
  simp only [cost]
  linarith [h, h2]

lemma mcost_le_cost (hcov : Covers G H) : mcost p H ≤ cost p G := by
  refine Finset.min'_le _ _ ?_
  refine Finset.mem_image.2 ⟨G, ?_, rfl⟩
  simp only [coverFams, mem_filter, mem_univ, true_and]
  exact hcov

lemma exists_cover_eq_mcost (p : ℝ) (H : Finset (Finset X)) :
    ∃ G, Covers G H ∧ cost p G = mcost p H := by
  have h := Finset.min'_mem ((coverFams H).image (cost p)) (coverFams_nonempty H)
  rw [Finset.mem_image] at h
  obtain ⟨G, hG, hGc⟩ := h
  simp only [coverFams, mem_filter, mem_univ, true_and] at hG
  exact ⟨G, hG, hGc⟩

lemma mcost_nonneg (hp : 0 ≤ p) (H : Finset (Finset X)) : 0 ≤ mcost p H := by
  obtain ⟨G, _, hG⟩ := exists_cover_eq_mcost p H
  rw [← hG]
  exact cost_nonneg hp G

lemma mcost_empty (hp : 0 ≤ p) : mcost p (∅ : Finset (Finset X)) = 0 := by
  refine le_antisymm ?_ (mcost_nonneg hp _)
  have h : Covers (∅ : Finset (Finset X)) (∅ : Finset (Finset X)) := by
    intro S hS; simp at hS
  simpa [cost] using mcost_le_cost (p := p) h

lemma half_lt_mcost (hns : ¬ IsSmall p H) : 1 / 2 < mcost p H := by
  by_contra h
  push_neg at h
  obtain ⟨G, hcov, hGc⟩ := exists_cover_eq_mcost p H
  exact hns ⟨G, hcov, by rw [hGc]; exact h⟩

end basic

end Math2

