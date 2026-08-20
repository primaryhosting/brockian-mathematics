import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

def Node.depth {n k : ℕ} (g : Node n k) (dep : Fin k → ℕ) : ℕ :=
  match g with
  | .var _ => 0
  | .const _ => 0
  | .not j => dep j
  | .or L => 1 + (L.map dep).foldr max 0
  | .and L => 1 + (L.map dep).foldr max 0
  | .mod L => 1 + (L.map dep).foldr max 0

/-- A straight-line circuit with `k` gates on `n` inputs. -/
inductive Ckt (n : ℕ) : ℕ → Type
  | nil : Ckt n 0
  | cons : ∀ {k : ℕ}, Ckt n k → Node n k → Ckt n (k + 1)

/-- The values of all the gates of a circuit on a given input. -/
