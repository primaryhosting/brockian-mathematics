import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxHeartbeats 1000000

namespace QI

/-- Bit strings of length `n`, as vectors over the field `ZMod 2`.
Addition is bitwise XOR. -/
abbrev BV (n : ℕ) := Fin n → ZMod 2

/-- The `ZMod 2`-valued inner product `⟨x, y⟩ = ⨁ i, x i * y i`. -/

theorem fiber_eq_pair {n : ℕ} {s : BV n} {f : BV n → BV n} (hf : IsSimon s f) {x₀ z : BV n}
    (hx₀ : f x₀ = z) :
    Finset.univ.filter (fun x => f x = z) = ({x₀, x₀ + s} : Finset (BV n)) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hw
    have : f x₀ = f w := by rw [hx₀, hw]
    exact (hf x₀ w).1 this
  · intro hw
    have : f x₀ = f w := (hf x₀ w).2 hw
    rw [← this, hx₀]

/-- **Destructive interference.** Any outcome `y` that is *not* orthogonal to the hidden
shift `s` has zero amplitude: the quantum measurement always returns `y` with `⟨y,s⟩ = 0`. -/
