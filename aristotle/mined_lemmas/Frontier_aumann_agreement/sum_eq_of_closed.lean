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

/-- The conditional probability of the event `E` given the (information) cell `C`,
computed from the weight function `p`. -/

theorem sum_eq_of_closed {Ω : Type*} [DecidableEq Ω] (p : Ω → ℝ) (I : Ω → Finset Ω)
    (hself : ∀ x, x ∈ I x) (heq : ∀ x y, y ∈ I x → I y = I x)
    (E : Finset Ω) (q : ℝ) :
    ∀ M : Finset Ω, (∀ x ∈ M, I x ⊆ M) →
      (∀ x ∈ M, (∑ y ∈ I x ∩ E, p y) = q * ∑ y ∈ I x, p y) →
      (∑ y ∈ M ∩ E, p y) = q * ∑ y ∈ M, p y := by
  intro M
  induction M using Finset.strongInduction with
  | _ M ih =>
    intro hclosed hq
    rcases M.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hCM : I x ⊆ M := hclosed x hx
      have hxC : x ∈ I x := hself x
      have hsub : M \ I x ⊂ M := by
        refine Finset.ssubset_iff_of_subset (Finset.sdiff_subset) |>.2 ⟨x, hx, ?_⟩
        simp [hxC]
      have hclosed' : ∀ y ∈ M \ I x, I y ⊆ M \ I x := by
        intro y hy z hz
        obtain ⟨hyM, hyC⟩ := Finset.mem_sdiff.mp hy
        refine Finset.mem_sdiff.mpr ⟨hclosed y hyM hz, ?_⟩
        intro hzC
        have h1 : I z = I y := heq y z hz
        have h2 : I z = I x := heq x z hzC
        have h3 : I y = I x := h1.symm.trans h2
        exact hyC (h3 ▸ hself y)
      have hq' : ∀ y ∈ M \ I x, (∑ z ∈ I y ∩ E, p z) = q * ∑ z ∈ I y, p z :=
        fun y hy => hq y (Finset.mem_sdiff.mp hy).1
      have IH := ih (M \ I x) hsub hclosed' hq'
      have hsplitE : M ∩ E = (I x ∩ E) ∪ ((M \ I x) ∩ E) := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro ⟨hzM, hzE⟩
          by_cases hzC : z ∈ I x
          · exact Or.inl ⟨hzC, hzE⟩
          · exact Or.inr ⟨⟨hzM, hzC⟩, hzE⟩
        · rintro (⟨hzC, hzE⟩ | ⟨⟨hzM, _⟩, hzE⟩)
          · exact ⟨hCM hzC, hzE⟩
          · exact ⟨hzM, hzE⟩
      have hdisjE : Disjoint (I x ∩ E) ((M \ I x) ∩ E) := by
        refine Finset.disjoint_left.2 ?_
        intro z hz hz'
        exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hz').1).2 (Finset.mem_inter.mp hz).1
      have hsplit : M = I x ∪ (M \ I x) := (Finset.union_sdiff_of_subset hCM).symm
      have hdisj : Disjoint (I x) (M \ I x) := Finset.disjoint_sdiff
      rw [hsplitE, Finset.sum_union hdisjE, IH, hq x hx]
      conv_rhs => rw [hsplit]
      rw [Finset.sum_union hdisj]
      ring

/-- **Aumann's agreement theorem** (finite, base case).

Two agents share a common prior `p` (a nonnegative weight function on a state space `Ω`)
and have information partitions given by the cell maps `I₁`, `I₂` (each point lies in its own
cell, and cells of points in a common cell coincide).  `M` is a common-knowledge component at the
actual state `w`: it contains `w` and is closed under both information maps.  If, throughout `M`,
agent 1's posterior for the event `E` is `q₁` and agent 2's posterior is `q₂` — i.e. the posteriors
are common knowledge at `w` — then `q₁ = q₂`: the agents cannot agree to disagree.

(Normalization `∑ x, p x = 1` of the prior is not needed for the argument, so it is not assumed.) -/
