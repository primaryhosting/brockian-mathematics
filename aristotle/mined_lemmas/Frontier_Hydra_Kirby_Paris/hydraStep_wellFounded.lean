/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem hydraStep_wellFounded :
    WellFounded (fun h' h : Hydra => ∃ n : ℕ, HydraStep n h h') := by
  refine Subrelation.wf ?_ (InvImage.wf ord Ordinal.lt_wf)
  rintro h' h ⟨n, hs⟩
  exact hs.ord_lt

/-- **Kirby–Paris hydra theorem.**  Every hydra game terminates, for every strategy of
Hercules and every regrowth behaviour of the hydra: there is no infinite sequence of hydras
`f 0, f 1, f 2, …` in which each `f (k+1)` arises from `f k` by a legal round of the game
(the hydra growing `c k` copies at round `k`). -/
