/-!
# Self Nonprediction
Category: Frontier Mind
Target: Frontier.self_nonprediction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u v

namespace Frontier

/-!
## Formalization

A *machine model* consists of

* a type `Machine` of machines, each of which produces one `Bool` output, recorded by
  `out : Machine → Bool`;
* a type `Predictor` of *predictor programs*, each of which, run on a machine, outputs a
  guess about that machine's output, recorded by `run : Predictor → Machine → Bool`;
* a *diagonalization* operation `diag : Predictor → Machine`: given a predictor program `q`,
  `diag q` is the machine that first runs `q` on itself (i.e. computes `q`'s prediction of
  `diag q`'s own output, *before* producing any output) and then outputs the negation of that
  prediction.  This behaviour is exactly the hypothesis `out (diag q) = !run q (diag q)`.

The theorem `Frontier.self_nonprediction` says that in any such model *no* predictor program is
always right: every `q` mispredicts some machine, namely the machine `diag q` that consults `q`
about itself before producing its own output.

Note that predictors form their own type: the semantic function `out` itself is not assumed to be
of the form `run q`.  That is what keeps the hypotheses consistent — see
`Frontier.machine_model_nonempty` below — and it reflects the intended reading, in which
predictors are programs that a machine may call as a subroutine.

This is the Cantor/Russell diagonal argument (compare `Function.cantor_surjective` in Mathlib,
which is proved by the same self-application-and-negate trick); since the statement here is
phrased directly in terms of machines and predictions, it is proved from scratch in two lines and
needs no library beyond core Lean.
-/

/-- **Self-nonprediction (diagonal form).** A machine that consults a predictor `q` about its own
next output and then does the opposite defeats `q`; hence no predictor program correctly predicts
the output of every machine. -/

theorem self_nonprediction_diag {Machine : Type u} {Predictor : Type v}
    (out : Machine → Bool) (run : Predictor → Machine → Bool) (diag : Predictor → Machine)
    (hdiag : ∀ q : Predictor, out (diag q) = !run q (diag q)) (q : Predictor) :
    run q (diag q) ≠ out (diag q) := by
  rw [hdiag q]; cases run q (diag q) <;> simp

/-- The hypotheses of `Frontier.self_nonprediction` are consistent: a machine model equipped with
a diagonalization operation and a nonempty supply of predictors exists.  (Machines are `Bool` and
each machine outputs its own name; the single predictor program always guesses `true`, and its
diagonal machine is the one outputting `false`.) -/
