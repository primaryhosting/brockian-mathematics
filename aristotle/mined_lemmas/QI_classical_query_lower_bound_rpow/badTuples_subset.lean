import Mathlib
import RequestProject.Simon.Basic
import RequestProject.Simon.Classical
import RequestProject.Simon.Quantum
import RequestProject.Simon.Solve

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

/-!
# Simon's problem: `O(n)` quantum queries, `Ω(2 ^ (n / 2))` classical queries

`QI.simon_algorithm` collects the two halves of the classical/quantum
separation for Simon's problem.  An instance is a function
`f : BV n → BV n` on `n`-bit strings satisfying Simon's promise
`IsSimon f s`: `s ≠ 0` and `f x = f y ↔ y = x ∨ y = x + s`.  The task is to
output the hidden shift `s`.

*Quantum upper bound.*  Each round of Simon's algorithm uses exactly **one**
query: it prepares `2 ^ (-n/2) ∑ₓ |x⟩|f x⟩`, applies the Hadamard transform to
the first register and measures.  The resulting distribution `prob f` is
uniform on the hyperplane `{y | ⟪y, s⟫ = 0}` orthogonal to `s`.  After
`2 * n` such rounds — i.e. `2 * n = O(n)` queries — the outcomes fail to pin
down `s` (as the unique nonzero solution of the linear system `⟪yᵢ, t⟫ = 0`)
only with probability at most `2 ^ (-n)`.

*Classical lower bound.*  A deterministic classical query algorithm that always
outputs the hidden shift after `q` queries must satisfy `2 ^ n ≤ (q + 2) ^ 2`,
i.e. `q ≥ 2 ^ (n / 2) - 2 = Ω(2 ^ (n / 2))`.
-/

namespace QI

/-- The classical lower bound in the form `2 ^ (n / 2) ≤ q + 2`. -/

lemma badTuples_subset (s : BV n) (m : ℕ) :
    badTuples s m ⊆ (Finset.univ.filter (fun t : BV n => t ≠ 0 ∧ t ≠ s)).biUnion
      (fun t => Fintype.piFinset fun _ => (orth s).filter (fun y => ip y t = 0)) := by
  classical
  intro Y hY
  rw [badTuples, Finset.mem_filter, Fintype.mem_piFinset] at hY
  obtain ⟨hmem, hnd⟩ := hY
  rw [Determines] at hnd
  push_neg at hnd
  obtain ⟨t, ht0, hort, hts⟩ := hnd
  refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
  · simp [ht0, hts]
  · exact Fintype.mem_piFinset.2 fun i => Finset.mem_filter.2 ⟨hmem i, hort i⟩

/-- The number of bad tuples is at most `2 ^ n / 2 ^ m` times the total number
of sample tuples. -/
