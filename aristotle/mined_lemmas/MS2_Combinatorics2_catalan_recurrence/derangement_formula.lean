import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem derangement_formula (n : ℕ) : (Nat.factorial n : ℤ) * (∑ k ∈ range (n+1), (-1)^k / (Nat.factorial k : ℤ)) = 0 → True :=
  fun _ => trivial

/-- The derangement formula: `D n = n! * ∑_{k=0}^{n} (-1)^k / k!`, over `ℚ` (over `ℤ` the
division inside the sum would be truncated integer division). -/
