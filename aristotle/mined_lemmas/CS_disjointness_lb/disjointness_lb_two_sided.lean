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

theorem disjointness_lb_two_sided {n : ℕ} {RA RB : Type}
    [Fintype RA] [Fintype RB] [DecidableEq RA] [DecidableEq RB]
    (P : Protocol (Finset (Fin n) × RA) (Finset (Fin n) × RB))
    (herr : ∀ a b : Finset (Fin n),
      (((Finset.univ : Finset (RA × RB)).filter
          (fun p => run P (a, p.1) (b, p.2) ≠ decide (Disjoint a b))).card : ℝ)
        < ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n) :
    n ≤ depth P := by
  classical
  set Bad : Finset (Fin n) × Finset (Fin n) → Finset (RA × RB) := fun q =>
    (Finset.univ : Finset (RA × RB)).filter
      (fun p => run P (q.1, p.1) (q.2, p.2) ≠ decide (Disjoint q.1 q.2))
  -- a union bound produces a single pair of random strings that is correct on all inputs
  have hne : ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card
      < Fintype.card (RA × RB) := by
    have h1 : (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
        ≤ ∑ q : Finset (Fin n) × Finset (Fin n), ((Bad q).card : ℝ) := by
      have := Finset.card_biUnion_le (s := (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))))
        (t := Bad)
      exact_mod_cast this
    have h2 : (∑ q : Finset (Fin n) × Finset (Fin n), ((Bad q).card : ℝ))
        < ∑ _q : Finset (Fin n) × Finset (Fin n),
            ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun q _ => herr q.1 q.2)
    have hpow : ((4 : ℝ)) ^ n = (2:ℝ) ^ n * (2:ℝ) ^ n := by
      rw [show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
    have h3 : (∑ _q : Finset (Fin n) × Finset (Fin n),
        ((Fintype.card RA : ℝ) * (Fintype.card RB : ℝ)) / 4 ^ n)
        = (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset,
        Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [hpow]
      field_simp
    have h4 : (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
        < (Fintype.card (RA × RB) : ℝ) := by
      have : (Fintype.card (RA × RB) : ℝ)
          = (Fintype.card RA : ℝ) * (Fintype.card RB : ℝ) := by
        rw [Fintype.card_prod]; push_cast; ring
      rw [this]
      calc (((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card : ℝ)
          ≤ _ := h1
        _ < _ := h2
        _ = _ := h3
    exact_mod_cast h4
  obtain ⟨p, hp⟩ : ∃ p : RA × RB,
      p ∉ (Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (RA × RB)).card
        ≤ ((Finset.univ : Finset (Finset (Fin n) × Finset (Fin n))).biUnion Bad).card :=
      Finset.card_le_card (fun p _ => hcon p)
    rw [Finset.card_univ] at this
    omega
  have hgood : ∀ a b : Finset (Fin n), run P (a, p.1) (b, p.2) = decide (Disjoint a b) := by
    intro a b
    by_contra hbad
    exact hp (Finset.mem_biUnion.mpr ⟨(a, b), Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad⟩⟩)
  refine fooling_bound P (fun S => (S, p.1)) (fun U => (U, p.2)) ?_ ?_
  · intro S T hST
    rw [hgood S T]
    simp [hST]
  · intro S
    rw [hgood S Sᶜ]
    simp [disjoint_compl_right]

/-! ### Sanity check: the hypotheses above are satisfiable -/

/-- A concrete (correct, deterministic) two-bit protocol for disjointness on `Fin 1`. -/
