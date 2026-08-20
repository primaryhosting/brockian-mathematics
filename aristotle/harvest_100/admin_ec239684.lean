import Mathlib

/-!
# Aumann Agreement
Category: Frontier Mind
Target: Frontier.aumann_agreement
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

section Aumann

variable {Ω : Type*} [DecidableEq Ω]

/-- If `I` assigns to each state its information cell (so that the cells form a partition of the
state space), `M` is a union of cells, and `g` sums to zero over every cell meeting `M`, then `g`
sums to zero over `M`. -/
theorem sum_eq_zero_of_cells (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (hcell : ∀ x y, y ∈ I x → I y = I x) (g : Ω → ℝ) :
    ∀ M : Finset Ω, (∀ x ∈ M, I x ⊆ M) → (∀ x ∈ M, ∑ y ∈ I x, g y = 0) →
      ∑ y ∈ M, g y = 0 := by
  intro M
  induction M using Finset.strongInduction with
  | _ M ih =>
    intro hclosed hzero
    rcases M.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hIx : I x ⊆ M := hclosed x hx
      -- the rest `M \ I x` is again a union of cells
      have hsub : M \ I x ⊂ M := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨x, hx, ?_⟩
        simp [hself x]
      have hclosed' : ∀ y ∈ M \ I x, I y ⊆ M \ I x := by
        intro y hy
        have hyM : y ∈ M := (Finset.mem_sdiff.1 hy).1
        have hyn : y ∉ I x := (Finset.mem_sdiff.1 hy).2
        intro z hz
        refine Finset.mem_sdiff.2 ⟨hclosed y hyM hz, ?_⟩
        intro hzIx
        -- if `z` lies in both cells, the cells coincide, contradicting `y ∉ I x`
        have h1 : I z = I y := hcell y z hz
        have h2 : I z = I x := hcell x z hzIx
        exact hyn (by rw [← h2, h1]; exact hself y)
      have hrest : ∑ y ∈ M \ I x, g y = 0 :=
        ih _ hsub hclosed' (fun y hy => hzero y (Finset.mem_sdiff.1 hy).1)
      have := Finset.sum_sdiff (f := g) hIx
      rw [← this, hrest, hzero x hx, add_zero]

/-- Conditional probabilities aggregate: if the posterior probability of `E` equals `q` on every
information cell contained in `M`, then it equals `q` on `M` itself. -/
theorem sum_inter_eq_of_cells (μ : Ω → ℝ) (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (hcell : ∀ x y, y ∈ I x → I y = I x)
    (E M : Finset Ω) (hclosed : ∀ x ∈ M, I x ⊆ M) (q : ℝ)
    (hq : ∀ x ∈ M, ∑ y ∈ I x ∩ E, μ y = q * ∑ y ∈ I x, μ y) :
    ∑ y ∈ M ∩ E, μ y = q * ∑ y ∈ M, μ y := by
  have key : ∀ S : Finset Ω,
      ∑ y ∈ S, ((if y ∈ E then μ y else 0) - q * μ y)
        = (∑ y ∈ S ∩ E, μ y) - q * ∑ y ∈ S, μ y := by
    intro S
    rw [Finset.sum_sub_distrib, Finset.sum_ite_mem, ← Finset.mul_sum]
  have h := sum_eq_zero_of_cells I hself hcell
    (fun y => (if y ∈ E then μ y else 0) - q * μ y) M hclosed
    (fun x hx => by rw [key]; rw [hq x hx]; ring)
  rw [key] at h
  linarith

/-- **Aumann's agreement theorem** (finite, base case).

Two agents share a common prior `μ` on a finite state space `Ω`.  Agent `i`'s information is
described by the partition `I i` (`I i ω` is the cell of agent `i` containing `ω`).  The event `M`
is *common knowledge* at the true state `ω₀`: it contains `ω₀` and is a union of cells of both
agents.  If, throughout `M`, agent `1`'s posterior probability of the event `E` is `q₁` and agent
`2`'s posterior probability of `E` is `q₂` (this is the content of "the posteriors are common
knowledge"), then `q₁ = q₂`: the agents cannot agree to disagree.

Posteriors are expressed in the multiplicative form `μ (C ∩ E) = q * μ C`, which is equivalent to
`μ (C ∩ E) / μ C = q` on cells of positive probability and avoids division by zero elsewhere. -/
theorem aumann_agreement
    (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (I₁ I₂ : Ω → Finset Ω)
    (hself₁ : ∀ x, x ∈ I₁ x) (hcell₁ : ∀ x y, y ∈ I₁ x → I₁ y = I₁ x)
    (hself₂ : ∀ x, x ∈ I₂ x) (hcell₂ : ∀ x y, y ∈ I₂ x → I₂ y = I₂ x)
    (E M : Finset Ω) (ω₀ : Ω) (hω₀ : ω₀ ∈ M) (hpos : 0 < μ ω₀)
    (hM₁ : ∀ x ∈ M, I₁ x ⊆ M) (hM₂ : ∀ x ∈ M, I₂ x ⊆ M)
    (q₁ q₂ : ℝ)
    (hq₁ : ∀ x ∈ M, ∑ y ∈ I₁ x ∩ E, μ y = q₁ * ∑ y ∈ I₁ x, μ y)
    (hq₂ : ∀ x ∈ M, ∑ y ∈ I₂ x ∩ E, μ y = q₂ * ∑ y ∈ I₂ x, μ y) :
    q₁ = q₂ := by
  -- The prior probability of the common-knowledge event `M` is positive.
  have hMpos : 0 < ∑ y ∈ M, μ y :=
    Finset.sum_pos' (fun i _ => hμ i) ⟨ω₀, hω₀, hpos⟩
  have h1 : ∑ y ∈ M ∩ E, μ y = q₁ * ∑ y ∈ M, μ y :=
    sum_inter_eq_of_cells μ I₁ hself₁ hcell₁ E M hM₁ q₁ hq₁
  have h2 : ∑ y ∈ M ∩ E, μ y = q₂ * ∑ y ∈ M, μ y :=
    sum_inter_eq_of_cells μ I₂ hself₂ hcell₂ E M hM₂ q₂ hq₂
  have : q₁ * ∑ y ∈ M, μ y = q₂ * ∑ y ∈ M, μ y := by rw [← h1, h2]
  exact mul_right_cancel₀ (ne_of_gt hMpos) this

/-- Sanity check: the hypotheses of `Frontier.aumann_agreement` are satisfiable non-vacuously.
Four equally likely states; agent 1 learns whether the state is in `{0,1}` or `{2,3}`, agent 2
learns whether it is in `{0,2}` or `{1,3}`; the event is `E = {0,3}`.  Both posteriors are `1/2`
everywhere, and everything is common knowledge. -/
example : (1 : ℝ) / 2 = 1 / 2 :=
    Frontier.aumann_agreement (Ω := Fin 4) (fun _ => (1 : ℝ) / 4) (by norm_num)
      (fun x => ![({0, 1} : Finset (Fin 4)), {0, 1}, {2, 3}, {2, 3}] x)
      (fun x => ![({0, 2} : Finset (Fin 4)), {1, 3}, {0, 2}, {1, 3}] x)
      (by decide) (by decide) (by decide) (by decide)
      {0, 3} Finset.univ 0 (by decide) (by norm_num) (by decide) (by decide)
      (1 / 2) (1 / 2)
      (by
        intro x _
        fin_cases x <;>
          norm_num [show (({0, 1} : Finset (Fin 4)) ∩ {0, 3}) = {0} from by decide,
            show (({2, 3} : Finset (Fin 4)) ∩ {0, 3}) = {3} from by decide,
            show (({2, 3} : Finset (Fin 4)).card) = 2 from by decide])
      (by
        intro x _
        fin_cases x <;>
          norm_num [show (({0, 2} : Finset (Fin 4)) ∩ {0, 3}) = {0} from by decide,
            show (({1, 3} : Finset (Fin 4)) ∩ {0, 3}) = {3} from by decide,
            show (({0, 2} : Finset (Fin 4)).card) = 2 from by decide,
            show (({1, 3} : Finset (Fin 4)).card) = 2 from by decide])

end Aumann

end Frontier

