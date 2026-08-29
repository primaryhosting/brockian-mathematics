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

