# D5 validation record

Date: 22 October 2026. This record covers the focused `Brockian.D5Research`
import closure, including the five new proof modules described in
`D5_RESEARCH.md`.

## Environment and source

- Original repository baseline: `29426ff65b6f1fd68d594e529632eb79b5be3089`.
- Lean: `leanprover/lean4:v4.32.0`, compiler commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`, as pinned by the
  unchanged Lake manifest.
- Scope: 34 local modules: 28 original modules, five new proof modules, and
  one new aggregate import target.
- The original source files and dependency pins were unchanged. Hashes of
  the entire local source closure were compared before and after validation.

## Recorded results

| Check | Result |
|---|---|
| `lake build Brockian.D5Research` | Passed, exit 0; 8,688 Lake jobs in the resolved target, including cached dependencies. |
| `lake env lean -DautoImplicit=false scripts/d5_axiom_audit.lean` | Passed, exit 0; all theorem dependencies are within the stated whitelist. |
| Original source comparison | All 28 original local modules equal the pinned Git versions. |
| Source stability | All 34 local source hashes unchanged during the final checks. |

The audit visited 773 theorem declarations in 33
populated local modules and checked their transitive axiom dependencies.
The aggregate import file has no mathematical declarations of its own.
The only allowed axioms were `propext`, `Classical.choice`, and `Quot.sound`.
No project axiom, `sorryAx` dependency, or native decision oracle was
accepted. The count includes compiler-generated theorem declarations; it
does not count independent mathematical results.

Existing modules replay unused-simp warnings and tactic suggestions. These
are distinct from proof failures. The new rate and analytic modules passed
without error diagnostics. The commutant module also prints the axiom
dependencies of its two principal theorems.

## Checked statements

The final target includes the original automorphism, Fourier, eigenspace,
character/trace, golden-spectrum, cyclotomic, and divisibility chain. The
new modules prove:

1. The full complex-linear D5-equivariant operator classification and the
   unique nonnegative two-parameter real Markov cone.
2. Exact two-by-two phase commutation, actual paired-Fourier intertwining,
   and the necessary-and-sufficient whole-vertex commutation criterion.
3. Positivity and double stochasticity of heat matrices for arbitrary
   finite balanced real generators.
4. All finite real counting-norm contractions for `p ≥ 1` and the supremum
   contraction under a commuting nonnegative increment.
5. The explicit five-state matrix/action connection and the combined
   theorem `Brockian.D5RateComparison.markov_rate_comparison`.

The final comparison includes nonnegative base rates and increments,
both phase conditions, all real starting vectors, and nonnegative time.
It concludes that both heat matrices are doubly stochastic and that
distance to the uniform vector `1/5` does not increase in each stated norm.

## Reproduction and limits

Run the commands in `D5_RESEARCH.md` from this checkout with the pinned
toolchain. `scripts/d5_source_manifest.py` writes a fresh source inventory
with the current checkout revision and file hashes.

This is a local Lean validation of the selected D5 closure. It is not a
whole-repository build or a new AXLE/Aristotle service verdict. The original
historical attachments' Lean 4.24.0 environment was not rebuilt. Stored
historical failures retain their failed status.

The manuscript's explicit hyperbolic exponential, projector interpolation
formulas, quotient norm bound, and exact rational-series counterexample do
not inherit Lean proof status from this target. The new code does not
package the complete abstract irreducible-representation classification,
prove a ten-state regular-walk theorem, assert strict convergence, or give
a converse classifying every norm-monotone rate pair. Mathematical novelty
and first-formalization priority are separate questions from successful
proof checking.
