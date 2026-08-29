# MISSING-FORMAL-SOURCES.md

Formal (`.lean`) modules that the documentary corpus references but that are **absent** from the
submitted bundle. Per the bundle's controls, their prose descriptions **do not** authorize any
formal-verification verdict while the `.lean` sources are missing.

## A. Waves 1–15 — Books One & Two (prose only, no Lean)

The bundle ships these only as `Evidence/Provided/` documents (markdown / docx), never as compiled
Lean. A unified "Waves 1–50" corpus cannot be asserted until they are (re)formalized.

| Wave | Title (from documentary evidence) | Evidence present | Lean source |
|---|---|---|---|
| 1 | Phenomenological Dependence | `phenomenological-dependence-wave-1*.md` | ❌ missing |
| 2 | Foundation | `phenomenological-foundation-wave-2*.md` | ❌ missing |
| 3 | Intentional Constitution | `phenomenological-intentional-constitution-wave-3*.md` | ❌ missing |
| 4 | Temporal Constitution | `phenomenological-temporal-constitution-wave-4*.md` | ❌ missing |
| 5 | Branching Horizons | `phenomenological-branching-horizons-wave-5*.md` | ❌ missing |
| 6 | Passive Genesis | `phenomenological-passive-genesis-wave-6*.md` | ❌ missing |
| 7 | Intersubjectivity | `phenomenological-intersubjectivity-wave-7*.md` | ❌ missing |
| 8 | (Book One/Two, per 1–9 roadmap) | `…waves-1-9-roadmap*.md` (summary only) | ❌ missing |
| 9 | Genetic I-Model (per roadmap) | `…waves-1-9-roadmap*.md` (summary only) | ❌ missing |
| 10–15 | Book Two waves | `Phenomenological_Mathematics_Waves_10-15*.docx` | ❌ missing |

Required per-wave artifacts for reintegration (matching the Waves 16–29 pattern): `WaveNN.lean`
(definitions + generic invariants + positive finite witness + countermodel + governing
non-entailment theorem), `WaveNNAxiomAudit.lean`, a `WAVE NN-VERIFICATION.md`, and a ledger entry.
Expected aggregate roots: `BookOne.lean` (Waves 1–?) and `BookTwo.lean` (Waves ?–15).

## B. Wave 30 — chartered, not in this bundle

`Evidence/Provided/CORPUS-VERIFICATION-2026-08-29.md` references a Wave 30 ("Event-Sourced
Temporality and Genetic Identity") and a `BookFive.lean`, and a separate reconciliation names it as
the *next obligation*. **Neither `Wave30.lean` nor `BookFive.lean` is in this submission** (manifest
`coverage.wave_30 = "not_submitted_canonical_lean_module_absent"`). No Wave-30 verdict can be issued here.

> ⚠️ **Contradiction to resolve:** `CORPUS-VERIFICATION-2026-08-29.md` asserts "Isolated source
> builds: Waves 16–**30** passed" and "Aggregate roots … `BookFive.lean` passed." The submission
> manifest scopes the corpus to **Waves 16–29** and excludes Wave 30. Treat the doc's Wave-30 /
> BookFive build claim as **unsupported** until a `Wave30.lean` / `BookFive.lean` source is supplied
> and independently compiled.

## C. Reconstruction policy

If reconstructed Lean is ever generated for A or B, it must live in a separate `Reconstruction/`
tree, be labelled newly generated and **not identical** to any lost original, and must not be
described as verification of the original module.
