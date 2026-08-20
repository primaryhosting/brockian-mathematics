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
Statement: Set-disjointness has Ω(n) randomized communication complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace CS

universe u v

/-- A deterministic two-party communication protocol tree over inputs `X` (Alice) and `Y` (Bob).
`alice m k` means Alice sends the bit `m x` and the protocol continues with `k (m x)`;
`bob m k` means Bob sends the bit `m y`. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf : Bool → Protocol X Y
  | alice : (X → Bool) → (Bool → Protocol X Y) → Protocol X Y
  | bob : (Y → Bool) → (Bool → Protocol X Y) → Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on a given pair of inputs. -/

theorem disjointness_lb_randomized {n : ℕ} {RA RB : Type}
    [Fintype RA] [Fintype RB] [Nonempty RA] [Nonempty RB] [DecidableEq RA] [DecidableEq RB]
    (P : Protocol (Finset (Fin n) × RA) (Finset (Fin n) × RB)) (ε : ℝ) (hε : ε < 1)
    (hsound : ∀ (a b : Finset (Fin n)) (ra : RA) (rb : RB),
      ¬ Disjoint a b → run P (a, ra) (b, rb) = false)
    (hcorrect : ∀ (a b : Finset (Fin n)), Disjoint a b →
      1 - ε ≤ ((Finset.univ.filter
          (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
        / ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ))) :
    n ≤ depth P := by
  refine disjointness_lb P hsound ?_
  intro a b hab
  have hA : (0 : ℝ) < (Fintype.card RA : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := RA)
  have hB : (0 : ℝ) < (Fintype.card RB : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := RB)
  have h := hcorrect a b hab
  have hpos : (0 : ℝ) < ((Finset.univ.filter
      (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ) := by
    have h0 : (0:ℝ) < 1 - ε := by linarith
    have hd : (0:ℝ) < (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := mul_pos hA hB
    have hq := lt_of_lt_of_le h0 h
    have hrw : ((Finset.univ.filter
        (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
        = (((Finset.univ.filter
          (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).card : ℝ)
          / ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)))
          * ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) := by
      field_simp
    rw [hrw]
    exact mul_pos hq hd
  have : (Finset.univ.filter (fun p : RA × RB => run P (a, p.1) (b, p.2) = true)).Nonempty := by
    rw [← Finset.card_pos]
    exact_mod_cast hpos
  obtain ⟨p, hp⟩ := this
  exact ⟨p.1, p.2, (Finset.mem_filter.mp hp).2⟩

/-- Two-sided error corollary.  If, on every input pair, the protocol errs (in either
direction) for fewer than a `4 ^ (-n)` fraction of the private random strings, then it must
exchange at least `n` bits.  (The error probability required here is exponentially small; the
two-sided bound for constant error is Razborov's theorem and is not proved here.) -/
