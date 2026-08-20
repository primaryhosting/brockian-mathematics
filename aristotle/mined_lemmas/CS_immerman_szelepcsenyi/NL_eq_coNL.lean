import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


theorem NL_eq_coNL : NL = coNL := by
  funext L
  rw [eq_iff_iff]
  constructor
  · intro h
    exact NL_compl h
  · intro h
    have h2 := NL_compl h
    have heq : (fun n x => ¬ ¬ L n x) = L := by
      funext n x
      simp
    rwa [heq] at h2

end CS

import Mathlib
import RequestProject.ISCore

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to precede every other command, including the module
-- documentation above.)

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## The statement

`NL` is formalised through configuration graphs (see `RequestProject/ISModel.lean`).
A machine on inputs of length `n` is a finite set of configurations together with an
initial and an accepting configuration and, for each ordered pair of configurations, a
guard which is either "absent", "present", or "present exactly when the `i`-th input bit
is `b`": this is precisely how a space bounded machine may depend on its input, namely
through the single input bit currently scanned.  A machine accepts an input when its
accepting configuration is reachable from its initial configuration along the guards that
hold.  A language belongs to `NL` when it is recognised by machines whose configuration
graphs have polynomially many vertices, i.e. logarithmic space; `coNL` is the class of
languages whose complement belongs to `NL`.

Since the machines are given for each input length separately, the class formalised here
is the nonuniform version of nondeterministic logarithmic space.  The proof is the
inductive counting argument of Immerman and Szelepcsényi: for every machine `M` we build
a machine `M'` with polynomially many configurations that accepts exactly the inputs
rejected by `M`.  The construction of `M'` is explicit (see
`RequestProject/ISMachine.lean`) and its correctness is proved in both directions in
`RequestProject/ISSound.lean` and `RequestProject/ISComplete.lean`.
-/

/-- **Immerman–Szelepcsényi theorem**: nondeterministic logarithmic space is closed
under complementation, `NL = coNL`. -/
