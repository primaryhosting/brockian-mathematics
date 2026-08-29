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

import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

universe u v

/-- A deterministic two-party communication protocol: a binary tree whose internal nodes
are labelled either by a bit that Alice sends (a function of her input `x : X`) or by a bit
that Bob sends (a function of his input `y : Y`), and whose leaves carry the output bit. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → Protocol X Y → Protocol X Y → Protocol X Y
  | bob : (Y → Bool) → Protocol X Y → Protocol X Y → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The communication cost of a protocol: the depth of the tree, i.e. the worst-case number
of bits exchanged. -/

theorem card_accepted_le {n : ℕ} (p : Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hsound : ∀ S T : Finset (Fin n), ¬ Disjoint S T → p.run S T = false) :
    (Finset.univ.filter fun S : Finset (Fin n) => p.run S Sᶜ = true).card ≤ 2 ^ p.cost := by
  classical
  set A : Finset (Finset (Fin n)) :=
    Finset.univ.filter fun S : Finset (Fin n) => p.run S Sᶜ = true with hA
  set B : Finset (Finset (Fin n) × Finset (Fin n)) := A.image (fun S => (S, Sᶜ)) with hB
  have hcardB : B.card = A.card := by
    rw [hB]
    exact Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.fst hab)
  have hinj : Set.InjOn (fun z : Finset (Fin n) × Finset (Fin n) => p.transcript z.1 z.2)
      (B : Set (Finset (Fin n) × Finset (Fin n))) := by
    intro z₁ hz₁ z₂ hz₂ hteq
    simp only [hB, Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz₁ hz₂
    obtain ⟨S, hS, rfl⟩ := hz₁
    obtain ⟨T, hT, rfl⟩ := hz₂
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hS hT
    simp only at hteq
    by_cases hST : S = T
    · subst hST; rfl
    · exfalso
      have h1 : p.run S Tᶜ = true := by
        have hr := (Protocol.rectangle p S T Sᶜ Tᶜ hteq).2
        rw [hr]; exact hS
      have h2 : p.run T Sᶜ = true := by
        have hr := (Protocol.rectangle p T S Tᶜ Sᶜ hteq.symm).2
        rw [hr]; exact hT
      rcases fooling_cross hST with hc | hc
      · rw [hsound S Tᶜ hc] at h1; exact Bool.noConfusion h1
      · rw [hsound T Sᶜ hc] at h2; exact Bool.noConfusion h2
  calc A.card = B.card := hcardB.symm
    _ = (B.image fun z => p.transcript z.1 z.2).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ 2 ^ p.cost := Protocol.card_image_transcript_le p B

/-- **Set disjointness has Ω(n) randomized communication complexity.**

A public-coin randomized protocol is a family `P : Fin m → Protocol _ _` of deterministic
protocols, run after drawing the public random string `r` uniformly from `Fin m`; its cost is
the worst-case cost `sup r, (P r).cost`.

If such a protocol computes set-disjointness on subsets of an `n`-element ground set with
one-sided error smaller than `1/2` — it never claims that two intersecting sets are disjoint
(`hsound`), and on disjoint inputs it answers correctly with probability strictly greater than
`1/2` (`hcomplete`) — then its cost is at least `n`.

Scope of the statement: the error is one-sided, i.e. the protocol has perfect soundness
(`hsound`) and is only allowed to err, with probability `< 1/2`, on disjoint pairs.  The
two-sided bounded-error version of this lower bound (Kalyanasundaram–Schnitger, Razborov) is a
strictly stronger statement and is not established here. -/
