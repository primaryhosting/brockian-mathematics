/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

set_option grind.warning false

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

theorem classical_query_bound {n : ℕ} (A : ClassicalAlg n) (m : ℕ) (hA : A.Solves m) :
    2 ^ n ≤ m * m + 2 := by
  classical
  by_contra hlt
  push_neg at hlt
  set X : Finset (BV n) := queried A id m with hXdef
  have hXcard : X.card ≤ m := queried_card_le A id m
  -- the excluded periods
  set D : Finset (BV n) := insert 0 ((X ×ˢ X).image (fun p => p.1 + p.2)) with hDdef
  have hDcard : D.card ≤ m * m + 1 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h1 : ((X ×ˢ X).image (fun p => p.1 + p.2)).card ≤ (X ×ˢ X).card :=
      Finset.card_image_le
    have h2 : (X ×ˢ X).card = X.card * X.card := Finset.card_product X X
    have h3 : X.card * X.card ≤ m * m := Nat.mul_le_mul hXcard hXcard
    omega
  have hcard_univ : (Finset.univ : Finset (BV n)).card = 2 ^ n := by
    simp [Finset.card_univ]
  -- at least two admissible periods remain
  have hcompl : 2 ≤ (Finset.univ \ D).card := by
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ D)
    rw [hcard_univ] at hsum
    have hDc : D.card ≤ m * m + 1 := hDcard
    have : m * m + 2 < 2 ^ n := hlt
    omega
  obtain ⟨s₁, hs₁, s₂, hs₂, hne⟩ := Finset.one_lt_card.mp hcompl
  -- for any admissible period there is an instance the algorithm cannot distinguish
  have key : ∀ s ∈ Finset.univ \ D, A.output (transcript A id m) = s := by
    intro s hsmem
    have hsD : s ∉ D := (Finset.mem_sdiff.mp hsmem).2
    have hs0 : s ≠ 0 := by
      intro h; exact hsD (by rw [h]; exact Finset.mem_insert_self _ _)
    have hXs : ∀ x ∈ X, ∀ y ∈ X, x + y ≠ s := by
      intro x hx y hy hxy
      refine hsD (Finset.mem_insert_of_mem ?_)
      refine Finset.mem_image.mpr ⟨(x, y), ?_, hxy⟩
      exact Finset.mem_product.mpr ⟨hx, hy⟩
    obtain ⟨f, hf, hfid⟩ := exists_promise_agreeing X s hs0 hXs
    have hT : transcript A f m = transcript A id m :=
      transcript_eq_of_agree A f m (fun x hx => hfid x hx) m le_rfl
    have := hA f s hf
    rw [hT] at this
    exact this
  exact hne ((key s₁ hs₁).symm.trans (key s₂ hs₂))

/-- **Ω(2^{n/2}) classical queries are necessary.** -/
