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

def simonQuantumQueries (n : ℕ) : ℕ := n + 2

/-!
### Statement of the main theorem

The model, spelled out by the definitions in the imported files:

* `QI.Bits n = Fin n → ZMod 2` is the set of `n`-bit strings, an `F₂`-vector space, and
  `QI.bdot` is the `F₂`-valued inner product.
* `QI.SimonPromise f s` says that `s ≠ 0` and `f x = f y ↔ (y = x ∨ y = x + s)`, i.e. `f` is
  two-to-one with hidden shift `s`. Simon's problem is to find `s`.
* `QI.simonState f = hadFst (oracle f (hadFst (initState n)))` is the quantum state obtained
  from `|0, 0⟩` by a Hadamard transform on the first register, **one** standard quantum query
  `|x, z⟩ ↦ |x, z + f x⟩`, and a second Hadamard transform; `QI.measureFst` is the Born-rule
  probability of an outcome of measuring the first register.
* `QI.tupleState m f` is the product state of `m` independent copies of that circuit — a
  computation using exactly `m` quantum queries — and `QI.measureTuple m f` its outcome
  distribution; `QI.successProb m f s` is the probability that the outcome tuple `QI.determines`
  the hidden shift `s`, i.e. that `s` is the unique nonzero vector orthogonal to all `m`
  measured strings (and hence is recovered by classical linear algebra).
* `QI.ClassicalAlg n` is a deterministic adaptive classical query algorithm, `QI.Solves A q`
  says it outputs the hidden shift for every instance of Simon's problem using `q` queries.

The conjuncts below say:

1. the Hadamard layer and the quantum query are unitary (they preserve the total squared
   amplitude) and the initial state is normalized, so the circuit is a legitimate quantum
   computation;
2. the one-query circuit yields a genuine probability distribution;
3. it samples exactly uniformly from the hyperplane `s^⊥` orthogonal to the hidden shift;
4. `simonQuantumQueries n = n + 2` quantum queries — a number that is `O(n)`, with explicit
   constant `3` in the last line — determine `s` with probability at least `3/4`;
5. every deterministic classical algorithm solving Simon's problem needs `q ≥ 2^((n-1)/2)`
   queries, i.e. `Ω(2^(n/2))` many.
-/
/-- **Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2^(n/2))`
classical queries.** -/
