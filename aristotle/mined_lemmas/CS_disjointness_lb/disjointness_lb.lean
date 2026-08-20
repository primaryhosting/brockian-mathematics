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

theorem disjointness_lb (n c : ℕ) {R : Type} [Fintype R] [DecidableEq R]
    (w : R → ℝ) (hw0 : ∀ r, 0 ≤ w r) (hw1 : ∑ r, w r = 1)
    (p : R → Protocol (Finset (Fin n)) (Finset (Fin n)))
    (hdepth : ∀ r, (p r).depth ≤ c)
    (ε : ℝ)
    (herr : ∀ x y : Finset (Fin n),
      ∑ r ∈ Finset.univ.filter (fun r => (p r).run x y ≠ decide (Disjoint x y)), w r ≤ ε)
    (hsmall : ε * 4 ^ n < 1) : n ≤ c := by
  classical
  -- Some coin value gives a protocol correct on *all* inputs.
  have hex : ∃ r : R, ComputesDisj n (p r) := by
    by_contra hc
    push_neg at hc
    -- pick, for each `r`, a bad input pair
    have hbad : ∀ r : R, ∃ q : Finset (Fin n) × Finset (Fin n),
        (p r).run q.1 q.2 ≠ decide (Disjoint q.1 q.2) := by
      intro r
      obtain ⟨x, hx⟩ := not_forall.mp (hc r)
      obtain ⟨y, hy⟩ := not_forall.mp hx
      exact ⟨(x, y), hy⟩
    choose φ hφ using hbad
    set S : Finset (Finset (Fin n) × Finset (Fin n)) := Finset.univ with hS
    have hmaps : ∀ r ∈ (Finset.univ : Finset R), φ r ∈ S := by intro r _; simp [hS]
    have hsplit : ∑ r, w r
        = ∑ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r :=
      (Finset.sum_fiberwise_of_maps_to hmaps w).symm
    have hle : ∀ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r ≤ ε := by
      intro q _
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => hw0 i)) (herr q.1 q.2)
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      subst hr
      exact hφ r
    have hsum : (1 : ℝ) ≤ (S.card : ℝ) * ε := by
      calc (1 : ℝ) = ∑ r, w r := hw1.symm
        _ = ∑ q ∈ S, ∑ r ∈ Finset.univ.filter (fun r => φ r = q), w r := hsplit
        _ ≤ ∑ _q ∈ S, ε := Finset.sum_le_sum hle
        _ = (S.card : ℝ) * ε := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.card : ℝ) = 4 ^ n := by
      have : S.card = 2 ^ n * 2 ^ n := by
        simp [hS, Finset.card_univ, Fintype.card_prod, Fintype.card_finset]
      rw [this]
      push_cast
      rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
    rw [hcard] at hsum
    nlinarith [hsum, hsmall]
  obtain ⟨r, hr⟩ := hex
  exact (deterministic_disjointness_lb n (p r) hr).trans (hdepth r)

end CS

