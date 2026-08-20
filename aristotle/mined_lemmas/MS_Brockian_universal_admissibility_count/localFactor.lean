import Mathlib
open Matrix Finset
namespace MS.Brockian
/-- Universal q−2 admissibility law (heart of the Brockian sieve). -/

noncomputable def localFactor (G : Finset ℕ) (p : ℕ) : ℝ :=
  if p.Prime then (1 - (nu G p : ℝ) / p) / ((1 - 1 / (p : ℝ)) ^ G.card) else 1
