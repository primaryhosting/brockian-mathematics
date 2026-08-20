import Mathlib
namespace BrockianFrontier.Gilbreath

/-- Absolute successive differences of a list. -/

def adj : List ℕ → List ℕ
  | a :: b :: t => Nat.dist a b :: adj (b :: t)
  | _ => []

/-- The first 25 primes. -/
