# Game Theory Formalization Program

This program extends the existing finite Nash work without treating repeated
Aristotle runs as independent theorems or promoting a solver verdict by itself.
All entries begin in `CANDIDATE_ONLY`.

## Current foundation

The selected Nash candidate contains substantial finite-game infrastructure and
a reduction from a fixed point of the Nash map to equilibrium.  The general
existence theorem still exposes a Brouwer fixed-point premise, and the selected
file is not independently green in the current AXLE report.  Its honest target
name is therefore `Frontier.nash_equilibrium_exists_of_brouwer` until that
dependency is discharged.

## Staged expansion

| Phase | Area | First formal targets | Gate |
|---:|---|---|---|
| 0 | Nash foundation | Nash-map fixed point characterization; circulant skew zero-sum uniform equilibrium | Repair and verify the Brouwer reduction separately |
| 1 | Correlated equilibrium | Point-mass and product-distribution embeddings; convexity | No unconditional existence claim before the Nash dependency is green |
| 2 | Extensive/Bayesian games | Backward induction; finite Bayesian-to-normal-form reduction | Keep perfect recall and existence dependencies explicit |
| 3 | Refinements | Strict Nash implies trembling-hand perfect; Kuhn realization | Definitions and limit arguments first |
| 4 | Learning dynamics | External regret implies approximate coarse correlated equilibrium; Hedge later | Finite-time theorem before convergence language |
| 5 | Computation | Exact rational Nash verification; solver soundness; PPAD statement later | Soundness before completeness or complexity |
| 6 | Mechanism design | Second-price truthfulness; VCG later | Pin tie-breaking, utilities, and finite argmax |
| 7 | Continuous games | Continuous Nash as a Kakutani reduction; Glicksberg statement | `KAKUTANI_REDUCTION` firewall |

## Queue behavior

`game_theory_program.json` is the canonical roadmap. Run
`python aristotle/gen_game_theory_queue.py` to generate a queue containing only
targets marked `READY`. The generated queue is deliberately absent from the
default `night_submit.py` queue list: activation requires a separate human
approval, so adding the roadmap cannot silently spend solver budget.

## Promotion rule

A remote `PROVED` verdict remains a candidate. Promotion requires an exact
signature review, repository-pinned Lean and Mathlib compilation, AXLE at the
same pin, retained raw `#print axioms` output, hashes, correct firewall labels,
and human review. Conditional reductions retain their `_of_brouwer` or
`_of_kakutani` names until the dependency is actually discharged.
