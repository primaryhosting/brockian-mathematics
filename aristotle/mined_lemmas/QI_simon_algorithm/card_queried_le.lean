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

lemma card_queried_le {n : ℕ} (A : ClassicalAlg n) (q : ℕ) : (queried A q).card ≤ q := by
  classical
  calc (queried A q).card ≤ (Finset.range q).card := Finset.card_image_le
    _ = q := Finset.card_range q

/-- If `g` fixes every point queried against the identity, the algorithm cannot tell `g`
from the identity. -/
