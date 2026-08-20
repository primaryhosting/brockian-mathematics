/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

theorem bpp_subset_p_of_prg (M : Model) (hPRG : DerandomizationHypothesis M)
    (L : List Bool → Bool) (hL : M.BPP L) : M.P L := by
  obtain ⟨A, m, hA, hm, hcorrect⟩ := hL
  obtain ⟨g⟩ := hPRG m hm
  -- the derandomized test
  have hf : M.PolyP2 (fun x y => A x (g.G x y)) := M.polyP2_subst A g.G hA g.polyG
  have hD := M.polyP_majority_log (fun x y => A x (g.G x y)) g.s hf g.polyS g.logSeed
  -- the majority vote computes `L`
  have hEq : (fun x : List Bool => decide (2 ^ (g.s x.length) <
      2 * (Finset.univ.filter
        (fun y : Fin (g.s x.length) → Bool => A x (g.G x (List.ofFn y)) = true)).card)) = L := by
    funext x
    have hfool := g.fools A hA x
    rcases hLx : L x with _ | _
    · have h13 := (hcorrect x).2 hLx
      have hhalf : avgTrue (g.s x.length) (fun y => A x (g.G x (List.ofFn y))) < (1 : ℚ) / 2 := by
        have := abs_le.mp hfool
        linarith [this.1, this.2]
      simpa using card_le_of_avgTrue_lt_half hhalf
    · have h23 := (hcorrect x).1 hLx
      have hhalf : (1 : ℚ) / 2 < avgTrue (g.s x.length) (fun y => A x (g.G x (List.ofFn y))) := by
        have := abs_le.mp hfool
        linarith [this.1, this.2]
      simpa using card_gt_of_avgTrue_gt_half hhalf
  rw [hEq] at hD
  exact hD

/-- Every language in `P` is in `BPP` (run the deterministic algorithm, ignoring randomness). -/
