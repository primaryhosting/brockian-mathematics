/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

noncomputable def hadFst {n : ℕ} (psi : Amp n) : Amp n :=
  fun p => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * ∑ x, sgn x p.1 * psi (x, p.2)

/-- The standard quantum query (oracle) `|x, z⟩ ↦ |x, z + f x⟩`, acting on amplitudes. -/
