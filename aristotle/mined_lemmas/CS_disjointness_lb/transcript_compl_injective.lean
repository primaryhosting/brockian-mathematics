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
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Communication complexity of set disjointness

We set up the standard two-party communication model (protocol trees), prove the
rectangle property of transcripts, and deduce the fooling-set lower bound
`n ≤ depth` for any deterministic protocol computing set disjointness on subsets
of `Fin n`.  We then lift this to public-coin randomized protocols.

Scope of the randomized statement: `CS.disjointness_lb` shows that every
public-coin randomized protocol for set disjointness on `Fin n` whose per-input
error probability `ε` satisfies `ε * 4 ^ n < 1` needs at least `n` bits of
communication.  This covers in particular zero-error (Las Vegas) randomized
protocols.  The constant-error version of the bound (Kalyanasundaram–Schnitger,
Razborov), which needs the corruption/information-complexity machinery, is *not*
formalized here.
-/

namespace CS

universe u v

variable {X : Type u} {Y : Type v}

/-- A deterministic two-party communication protocol with Boolean output:
a binary tree whose internal nodes are labelled by the party that speaks
(`alice` sends a bit depending on her input `x`, `bob` on his input `y`). -/
inductive Protocol (X : Type u) (Y : Type v) where
  | leaf (o : Bool) : Protocol X Y
  | alice (f : X → Bool) (a b : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (a b : Protocol X Y) : Protocol X Y

namespace Protocol

/-- The communication cost (worst-case number of exchanged bits) of a protocol. -/

theorem transcript_compl_injective {n : ℕ} {p : Protocol (Finset (Fin n)) (Finset (Fin n))}
    (hp : ComputesDisj n p) :
    Function.Injective (fun x : Finset (Fin n) => p.transcript x xᶜ) := by
  intro x x' h
  by_contra hne
  -- some element separates `x` from `x'`
  have hsep : (∃ i, i ∈ x ∧ i ∉ x') ∨ (∃ i, i ∈ x' ∧ i ∉ x) := by
    by_contra hc
    push_neg at hc
    obtain ⟨h1, h2⟩ := hc
    exact hne (Finset.Subset.antisymm (fun i hi => h1 i hi) (fun i hi => h2 i hi))
  simp only at h
  have key : ∀ (u v : Finset (Fin n)), p.transcript u uᶜ = p.transcript v vᶜ →
      ∀ i, i ∈ u → i ∉ v → False := by
    intro u v huv i hiu hiv
    have hr : p.transcript u vᶜ = p.transcript u uᶜ := p.transcript_rectangle huv
    have hrun : p.run u vᶜ = p.run u uᶜ := p.run_eq_of_transcript_eq hr
    have h1 : p.run u uᶜ = true := by
      rw [hp u uᶜ]; exact decide_eq_true disjoint_compl_right
    have h2 : ¬ Disjoint u vᶜ := by
      intro hd
      have : i ∈ (∅ : Finset (Fin n)) := by
        have := Finset.disjoint_left.mp hd hiu
        exact absurd (Finset.mem_compl.mpr hiv) this
      simp at this
    have h3 : p.run u vᶜ = false := by
      rw [hp u vᶜ]; simpa using h2
    rw [h3, h1] at hrun
    exact Bool.false_ne_true hrun
  rcases hsep with ⟨i, hi1, hi2⟩ | ⟨i, hi1, hi2⟩
  · exact key x x' h i hi1 hi2
  · exact key x' x h.symm i hi1 hi2

/-- **Deterministic lower bound.** Every deterministic protocol computing set
disjointness on subsets of an `n`-element universe must communicate at least `n`
bits (fooling-set / rectangle argument). -/
