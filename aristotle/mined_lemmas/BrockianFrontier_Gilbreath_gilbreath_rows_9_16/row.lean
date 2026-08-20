import Mathlib
namespace BrockianFrontier.Gilbreath

/-- Absolute successive differences of a list. -/

def row (k : ℕ) : List ℕ := adj^[k] primes25

/-- Gilbreath's conjecture continues to hold through rows 9–16 for the first 25 primes:
    every such row begins with 1. (Rows 1–8 are already verified upstream.) -/
