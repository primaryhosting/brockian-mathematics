import Mathlib

/-!
# Disjointness Lb
Category: Frontier Cs
Target: CS.disjointness_lb
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Contents

We formalize deterministic two-party communication protocols as protocol trees
(`CS.Protocol`), with `CS.Protocol.run` the output and `CS.Protocol.cost` the worst-case number
of exchanged bits, and prove the fooling-set bound `CS.Protocol.card_fooling_le`: a protocol of
cost `c` admits no fooling set of size larger than `2 ^ c`.

Applying it to the fooling set `{(x, xᶜ) : x ⊆ [n]}` for set disjointness gives

* `CS.disjointness_deterministic_lb`: every deterministic protocol computing set disjointness on
  subsets of an `n`-element universe costs at least `n` bits;
* `CS.disjointness_lb_of_success` and `CS.disjointness_lb`: every *public-coin randomized*
  protocol with perfect soundness (it never answers "disjoint" on an intersecting pair) that
  answers "disjoint" with probability at least `1/2` (more generally `δ`) on each disjoint pair
  costs at least `n - 1` bits (more generally `δ * 2 ^ n ≤ 2 ^ c`).  Hence set disjointness has
  `Ω(n)` randomized communication complexity in the one-sided-error model.
* `CS.disjointness_ub`: a matching deterministic protocol of cost `n + 1`, so the bounds are
  tight up to an additive constant and the hypotheses above are satisfiable.

The randomized lower bound proved here is for the one-sided-error (perfectly sound) model; the
two-sided bounded-error case (Kalyanasundaram–Schnitger, Razborov) is not formalized here.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace CS

universe u v

/-- A deterministic two-party communication protocol with Boolean output.
`alice f t e` means Alice sends the bit `f x` and the parties continue with `t` or `e`;
`bob g t e` is the same with Bob speaking. -/
inductive Protocol (X : Type u) (Y : Type v) : Type (max u v)
  | leaf (b : Bool) : Protocol X Y
  | alice (f : X → Bool) (t e : Protocol X Y) : Protocol X Y
  | bob (g : Y → Bool) (t e : Protocol X Y) : Protocol X Y

namespace Protocol

variable {X : Type u} {Y : Type v}

/-- The output of the protocol on the input pair `(x, y)`. -/

theorem cross_not_disjoint {n : ℕ} {x z : Finset (Fin n)} (h : x ≠ z) :
    ¬ Disjoint x zᶜ ∨ ¬ Disjoint z xᶜ := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  exact h (subset_antisymm (Finset.subset_iff.2 fun a ha => by
      by_contra hz
      exact (Finset.disjoint_left.1 h1 ha) (Finset.mem_compl.2 hz))
    (Finset.subset_iff.2 fun a ha => by
      by_contra hx
      exact (Finset.disjoint_left.1 h2 ha) (Finset.mem_compl.2 hx)))

/-- **Deterministic lower bound.** Any deterministic protocol computing set disjointness on
subsets of an `n`-element universe must communicate at least `n` bits. -/
