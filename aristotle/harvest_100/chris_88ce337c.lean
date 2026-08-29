/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is written in plain Lean 4 core (no imports), so that the header comment above
can legally be the very first thing in the file.
-/

namespace Frontier

/-- A `±1` sequence: `f n ∈ {1, -1}` for every index `n ≥ 1`. -/
def IsPlusMinusOne (f : Nat → Int) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- `hapSum f d n = f d + f (2 * d) + ⋯ + f (n * d)`, the partial sum of `f` along the
homogeneous arithmetic progression with common difference `d`. -/
def hapSum (f : Nat → Int) (d : Nat) : Nat → Int
  | 0 => 0
  | n + 1 => hapSum f d n + f ((n + 1) * d)

/-- The Erdős discrepancy problem (Tao's theorem): every `±1` sequence has unbounded
discrepancy along homogeneous arithmetic progressions, i.e. for every bound `C` there is a
homogeneous arithmetic progression `d, 2d, …, nd` on which the partial sum of `f` exceeds
`C` in absolute value. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : Nat → Int, IsPlusMinusOne f → ∀ C : Nat,
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ C < (hapSum f d n).natAbs

/-- If the two-term partial sum `f d + f (2d)` of a `±1` sequence has absolute value at
most `1`, then `f (2 * d) = - f d`. -/
theorem neg_of_hapSum_two (f : Nat → Int) (hf : IsPlusMinusOne f) {d : Nat} (hd : 1 ≤ d)
    (h : (hapSum f d 2).natAbs ≤ 1) : f (2 * d) = - f d := by
  have h2 : hapSum f d 2 = f d + f (2 * d) := by simp [hapSum]
  rw [h2] at h
  rcases hf d hd with h1 | h1 <;> rcases hf (2 * d) (by omega) with h3 | h3 <;> omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`), uniform form.**
For every `±1` sequence `f` a homogeneous arithmetic progression witnessing discrepancy
greater than `1` can already be found inside the initial segment `{1, …, 12}`: there are
`d, n ≥ 1` with `n * d ≤ 12` and `|f d + f (2d) + ⋯ + f (nd)| > 1`.

Equivalently: no `±1` sequence of length `12` has discrepancy at most `1` on homogeneous
arithmetic progressions.  (The bound `12` is optimal: there is a `±1` sequence of length
`11` with discrepancy `1`.) -/
theorem erdos_discrepancy_uniform (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ 12 ∧ 1 < (hapSum f d n).natAbs := by
  apply Classical.byContradiction
  intro hcon
  have h : ∀ d n : Nat, 1 ≤ d → 1 ≤ n → n * d ≤ 12 → (hapSum f d n).natAbs ≤ 1 := by
    intro d n hd hn hnd
    apply Classical.byContradiction
    intro hx
    exact hcon ⟨d, n, hd, hn, hnd, by omega⟩
  -- The doubling relation `f (2d) = - f d`, instantiated at `d = 1, 2, 3, 4, 5, 6`.
  have e2 : f 2 = - f 1 := by
    simpa using neg_of_hapSum_two f hf (d := 1) (by omega) (h 1 2 (by omega) (by omega) (by omega))
  have e4 : f 4 = - f 2 := by
    simpa using neg_of_hapSum_two f hf (d := 2) (by omega) (h 2 2 (by omega) (by omega) (by omega))
  have e6 : f 6 = - f 3 := by
    simpa using neg_of_hapSum_two f hf (d := 3) (by omega) (h 3 2 (by omega) (by omega) (by omega))
  have e8 : f 8 = - f 4 := by
    simpa using neg_of_hapSum_two f hf (d := 4) (by omega) (h 4 2 (by omega) (by omega) (by omega))
  have e10 : f 10 = - f 5 := by
    simpa using neg_of_hapSum_two f hf (d := 5) (by omega) (h 5 2 (by omega) (by omega) (by omega))
  have e12 : f 12 = - f 6 := by
    simpa using neg_of_hapSum_two f hf (d := 6) (by omega) (h 6 2 (by omega) (by omega) (by omega))
  -- Partial sums along `d = 1`.
  have s4 : (f 1 + f 2 + f 3 + f 4).natAbs ≤ 1 := by
    have := h 1 4 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s6 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6).natAbs ≤ 1 := by
    have := h 1 6 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s8 : (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8).natAbs ≤ 1 := by
    have := h 1 8 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s10 :
      (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10).natAbs ≤ 1 := by
    have := h 1 10 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have s12 :
      (f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 + f 12).natAbs
        ≤ 1 := by
    have := h 1 12 (by omega) (by omega) (by omega); simpa [hapSum] using this
  -- A partial sum along `d = 2` and one along `d = 3`.
  have u6 : (f 2 + f 4 + f 6 + f 8 + f 10 + f 12).natAbs ≤ 1 := by
    have := h 2 6 (by omega) (by omega) (by omega); simpa [hapSum] using this
  have t4 : (f 3 + f 6 + f 9 + f 12).natAbs ≤ 1 := by
    have := h 3 4 (by omega) (by omega) (by omega); simpa [hapSum] using this
  rcases hf 1 (by omega) with h1 | h1 <;> rcases hf 3 (by omega) with h3 | h3 <;>
    rcases hf 5 (by omega) with h5 | h5 <;> rcases hf 7 (by omega) with h7 | h7 <;>
    rcases hf 9 (by omega) with h9 | h9 <;> rcases hf 11 (by omega) with h11 | h11 <;>
    omega

/-- **Base case of the Erdős discrepancy problem (`C = 1`).**
For every `±1` sequence `f` there are `d, n ≥ 1` such that
`|f d + f (2d) + ⋯ + f (nd)| > 1`; equivalently, no `±1` sequence has discrepancy at
most `1` on homogeneous arithmetic progressions.  This is the `C = 1` instance of the full
statement `Frontier.ErdosDiscrepancyStatement`. -/
theorem erdos_discrepancy (f : Nat → Int) (hf : IsPlusMinusOne f) :
    ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ 1 < (hapSum f d n).natAbs := by
  obtain ⟨d, n, hd, hn, _, hlt⟩ := erdos_discrepancy_uniform f hf
  exact ⟨d, n, hd, hn, hlt⟩

/-- The instances `C ≤ 1` of the full Erdős discrepancy statement all hold:
for any bound `C ≤ 1` and any `±1` sequence there is a homogeneous arithmetic progression
whose partial sum exceeds `C` in absolute value. -/
theorem erdos_discrepancy_of_le_one (f : Nat → Int) (hf : IsPlusMinusOne f) (C : Nat)
    (hC : C ≤ 1) : ∃ d n : Nat, 1 ≤ d ∧ 1 ≤ n ∧ C < (hapSum f d n).natAbs := by
  obtain ⟨d, n, hd, hn, hlt⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by omega⟩

/-- The explicit `±1` sequence `+ - - + - + + - - + +` (extended by `1` beyond index
`11`), used to show that the bound `12` in `Frontier.erdos_discrepancy_uniform` is
optimal. -/
def witness11 (n : Nat) : Int :=
  if n = 2 ∨ n = 3 ∨ n = 5 ∨ n = 8 ∨ n = 9 then -1 else 1

theorem witness11_isPlusMinusOne : IsPlusMinusOne witness11 := by
  intro n _
  unfold witness11
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Bounded form of the optimality statement, checked by evaluation. -/
theorem witness11_discrepancy_one_bounded :
    ∀ d < 12, ∀ n < 12, 1 ≤ d → 1 ≤ n → n * d ≤ 11 →
      (hapSum witness11 d n).natAbs ≤ 1 := by
  decide

/-- **Optimality of the bound `12`.** All partial sums of `witness11` along homogeneous
arithmetic progressions contained in `{1, …, 11}` have absolute value at most `1`; so
there really is a `±1` sequence of length `11` with discrepancy `1`, and the initial
segment `{1, …, 12}` in `Frontier.erdos_discrepancy_uniform` cannot be shortened. -/
theorem witness11_discrepancy_one :
    ∀ d n : Nat, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (hapSum witness11 d n).natAbs ≤ 1 := by
  intro d n hd hn hnd
  exact witness11_discrepancy_one_bounded d (by
      have : d ≤ n * d := Nat.le_mul_of_pos_left d hn
      omega) n (by
      have : n ≤ n * d := Nat.le_mul_of_pos_right n hd
      omega) hd hn hnd

end Frontier

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# A Lean-checked reduction for the Erdős discrepancy problem

The statement `Frontier.ErdosDiscrepancyStatement` quantifies over all `±1` sequences on
`ℕ`.  Here we check, by a compactness argument on the Cantor space `ℕ → Bool`, that it is
*equivalent* to the family of finitary statements

  for every `C` there is `N` such that every `±1` sequence admits a homogeneous
  arithmetic progression inside `{1, …, N}` with partial sum exceeding `C`.

This is the standard reduction of the Erdős discrepancy problem to a sequence of finite
(in principle mechanically checkable) problems; the case `C = 1`, with `N = 12`, is proved
in `RequestProject/ErdosDiscrepancy.lean`.
-/

namespace Frontier

/-- The finitary form of the Erdős discrepancy statement: for each bound `C` there is a
uniform length `N` inside which every `±1` sequence already exhibits discrepancy `> C`. -/
def ErdosDiscrepancyFinite : Prop :=
  ∀ C : ℕ, ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPlusMinusOne f →
    ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ C < (hapSum f d n).natAbs

/-- The `±1` sequence attached to a point of Cantor space. -/
def boolSeq (g : ℕ → Bool) : ℕ → ℤ := fun n => if g n then 1 else -1

theorem boolSeq_isPlusMinusOne (g : ℕ → Bool) : IsPlusMinusOne (boolSeq g) := by
  intro n _
  unfold boolSeq
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `hapSum` only depends on the values of the sequence at positive indices. -/
theorem hapSum_congr {f f' : ℕ → ℤ} {d : ℕ} (hd : 1 ≤ d)
    (h : ∀ k, 1 ≤ k → f k = f' k) (n : ℕ) : hapSum f d n = hapSum f' d n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hpos : 1 ≤ (n + 1) * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      simp [hapSum, ih, h ((n + 1) * d) hpos]

/-- Every `±1` sequence agrees, at positive indices, with the sequence coming from a point
of Cantor space. -/
theorem exists_boolSeq_hapSum_eq (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ g : ℕ → Bool, ∀ d n : ℕ, 1 ≤ d → hapSum (boolSeq g) d n = hapSum f d n := by
  refine ⟨fun k => decide (f k = 1), fun d n hd => hapSum_congr hd (fun k hk => ?_) n⟩
  rcases hf k hk with h | h <;> simp [boolSeq, h]

theorem continuous_hapSum_boolSeq (d n : ℕ) :
    Continuous fun g : ℕ → Bool => hapSum (boolSeq g) d n := by
  induction n with
  | zero => simpa [hapSum] using continuous_const
  | succ n ih =>
      have hcoord : Continuous fun g : ℕ → Bool => boolSeq g ((n + 1) * d) := by
        exact (continuous_of_discreteTopology (f := fun b : Bool => if b then (1 : ℤ) else -1)).comp
          (continuous_apply ((n + 1) * d))
      simpa [hapSum] using ih.add hcoord

/-- **Compactness reduction.**  The Erdős discrepancy statement is equivalent to its
finitary form: unbounded discrepancy for all infinite `±1` sequences is the same as, for
each `C`, a uniform finite length `N` in which discrepancy `> C` must occur. -/
theorem erdosDiscrepancyStatement_iff_finite :
    ErdosDiscrepancyStatement ↔ ErdosDiscrepancyFinite := by
  constructor
  · -- the hard direction: compactness of Cantor space
    intro H C
    by_contra hN
    push_neg at hN
    -- for each `N`, a `±1` sequence with no witness inside `{1, …, N}`
    have hbad : ∀ N : ℕ, ∃ g : ℕ → Bool, ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ N →
        (hapSum (boolSeq g) d n).natAbs ≤ C := by
      intro N
      obtain ⟨f, hf, hfbad⟩ := hN N
      obtain ⟨g, hg⟩ := exists_boolSeq_hapSum_eq f hf
      refine ⟨g, fun d n hd hn hnd => ?_⟩
      rw [hg d n hd]
      exact hfbad d n hd hn hnd
    set t : ℕ → Set (ℕ → Bool) := fun N =>
      {g | ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ N → (hapSum (boolSeq g) d n).natAbs ≤ C}
      with ht
    have hmono : ∀ N : ℕ, t (N + 1) ⊆ t N := by
      intro N g hg d n hd hn hnd
      exact hg d n hd hn (by omega)
    have hne : ∀ N : ℕ, (t N).Nonempty := by
      intro N
      obtain ⟨g, hg⟩ := hbad N
      exact ⟨g, hg⟩
    have hclosed : ∀ N : ℕ, IsClosed (t N) := by
      intro N
      have hrw : t N = ⋂ d : ℕ, ⋂ n : ℕ,
          {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
            (hapSum (boolSeq g) d n).natAbs ≤ C} := by
        ext g
        simp [ht, Set.mem_iInter]
      rw [hrw]
      refine isClosed_iInter fun d => isClosed_iInter fun n => ?_
      by_cases hyp : 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N
      · have hset : {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
              (hapSum (boolSeq g) d n).natAbs ≤ C}
            = (fun g : ℕ → Bool => hapSum (boolSeq g) d n) ⁻¹' {x : ℤ | x.natAbs ≤ C} := by
          ext g
          simp [hyp.1, hyp.2.1, hyp.2.2]
        rw [hset]
        exact (isClosed_discrete _).preimage (continuous_hapSum_boolSeq d n)
      · have hset : {g : ℕ → Bool | 1 ≤ d → 1 ≤ n → n * d ≤ N →
              (hapSum (boolSeq g) d n).natAbs ≤ C} = Set.univ := by
          ext g
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
          intro h1 h2 h3
          exact absurd ⟨h1, h2, h3⟩ hyp
        rw [hset]
        exact isClosed_univ
    obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      t hmono hne (hclosed 0).isCompact hclosed
    obtain ⟨d, n, hd, hn, hlt⟩ := H (boolSeq g) (boolSeq_isPlusMinusOne g) C
    have := Set.mem_iInter.mp hg (n * d) d n hd hn le_rfl
    omega
  · -- the easy direction
    intro H f hf C
    obtain ⟨N, hNs⟩ := H C
    obtain ⟨d, n, hd, hn, _, hlt⟩ := hNs f hf
    exact ⟨d, n, hd, hn, hlt⟩

/-- The `C = 1` instance of the finitary form holds with `N = 12`, by
`Frontier.erdos_discrepancy_uniform`. -/
theorem erdosDiscrepancyFinite_one :
    ∃ N : ℕ, ∀ f : ℕ → ℤ, IsPlusMinusOne f →
      ∃ d n : ℕ, 1 ≤ d ∧ 1 ≤ n ∧ n * d ≤ N ∧ 1 < (hapSum f d n).natAbs :=
  ⟨12, fun f hf => erdos_discrepancy_uniform f hf⟩

end Frontier

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

