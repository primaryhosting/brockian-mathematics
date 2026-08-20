import Mathlib
import RequestProject.QI.Spanning
import RequestProject.QI.Classical

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/--
**Simon's problem is solved with `O(n)` quantum queries but needs `Ω(2 ^ (n / 2))`
classical queries.**

The four conjuncts are:

1. *One quantum query.*  For every Simon function `f` with secret `s`, one run of the
   circuit `H ∘ U_f ∘ H` applied to `|0,0⟩` — which uses exactly one oracle query — yields
   a measurement outcome that is uniformly distributed over the hyperplane
   `s^⊥ = {y | ⟪y, s⟫ = 0}` (probability `2 / 2 ^ n` on it, `0` off it).

2. *`m` quantum queries.*  With `m` runs of the circuit (`m` queries in total), the
   outcomes determine `s` uniquely — i.e. `s` is the only nonzero solution of the linear
   system they define, so Gaussian elimination recovers it — with probability at least
   `1 - 2 ^ n / 2 ^ m`.

3. *`O(n)` queries suffice.*  Taking `m = 2 n` queries, the algorithm succeeds with
   probability at least `1 - 2 ^ (-n)`.

4. *Classical lower bound.*  Any deterministic classical query algorithm (decision tree)
   that outputs the correct secret for every Simon function on `n ≥ 2` bits has depth at
   least `2 ^ (n / 2)`, i.e. makes `Ω(2 ^ (n / 2))` queries in the worst case.
-/

lemma orac_had_init {n : ℕ} (f : V n → V n) :
    orac f (had (initState (n := n)))
      = fun p : V n × V n => ((Real.sqrt (2 ^ n) : ℝ) : ℂ)⁻¹ * (if f p.1 = p.2 then 1 else 0) := by
  funext p
  rw [orac, had_init]
  congr 1
  simp [add_eq_zero_iff_V, eq_comm]

/-- The amplitudes of the final state are the real numbers `simonAmp f y b`. -/
