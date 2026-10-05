# ARISTOTLE-ATTESTATION.md

**Bundle:** `aristotle-full-available-corpus-2026-08-29`
**Program:** Phenomenological Mathematics — Waves 16–29 formal corpus
**Attesting verifier:** Claude Code, acting locally as the independent Lean verifier the bundle requests (in lieu of / ahead of a Harmonic Aristotle cloud run)
**Date:** 2026-08-29
**Pinned toolchain:** `leanprover/lean4:v4.32.0` — available locally via elan (exact match)

> **Status: PARTIAL — static verification COMPLETE, machine compilation DEFERRED.**
> The user elected "deliver static now, defer compile" because the host is memory-exhausted
> (~60 MB free RAM, heavy swap thrash; `lean` cannot load `Init`). Every claim below is
> labelled by evidence class. No prose or vendor artifact has been promoted to a checked-build verdict.

---

## 1. Verdict summary

| Check | Method | Result |
|---|---|---|
| Source identity (32 files) | SHA-256 recomputed vs `ARISTOTLE-SUBMISSION-MANIFEST.json` | ✅ **32/32 MATCH**, 0 mismatch, 0 missing |
| `sorry` | word-boundary scan, all 32 sources | ✅ **0** |
| `admit` | word-boundary scan, all 32 sources | ✅ **0** |
| `native_decide` | word-boundary scan, all 32 sources | ✅ **0** |
| user-added `axiom` decls | line scan `^\s*axiom\s`, all 32 sources | ✅ **0** |
| Statement preservation | byte-identity to submission | ✅ **UNCHANGED** (nothing weakened/renamed/removed) |
| **Lean compilation (32 files)** | `lean -o … .lean` under pin | ⏸️ **DEFERRED — memory-constrained** |
| **`#print axioms` reproduction** | 14 audit + 2 final-audit roots | ⏸️ **DEFERRED — memory-constrained** |

**Independently established now:** the submitted corpus is exactly the corpus the manifest
names (cryptographic identity), and it contains no proof-hole or trust-escape construct.

**Not yet independently established:** that the 32 files *compile* under Lean 4.32.0 and that
the reproduced axiom footprints equal the vendor-claimed footprints. This requires the deferred build.

## 2. Scope (exactly 32 `.lean` files, per manifest)

- **14 wave modules:** `Wave16.lean` … `Wave29.lean`
- **14 axiom audits:** `Wave16AxiomAudit.lean` … `Wave29AxiomAudit.lean`
- **4 aggregate / final-audit roots:** `BookThree.lean`, `BookFour.lean`, `BookThreeFinalAudit.lean`, `BookFourFinalAudit.lean`

Dependency shape: linear `Init`-rooted chain `Wave16 ← Wave17 ← … ← Wave29`; `BookThree`
imports Waves 16–25; `BookFour` imports `BookThree` + `Wave29`. **No Mathlib, no external
package** — the whole corpus is pure core Lean 4. (Verified by import scan; confirmed at build time.)

## 3. Source identity (SHA-256)

All 32 recomputed digests equal the manifest values. Full per-file table is in
`ARISTOTLE-ATTESTATION.json → files[]` (`sha256_submitted`, `sha256_recomputed`, `identity`).
Spot values:

| file | sha256 (verified) |
|---|---|
| `Wave16.lean` | `8920fe9f…006497465` |
| `Wave29.lean` | (see JSON) |
| `BookThree.lean` | `45175280…203cc4c2` |
| `BookFour.lean` | `163e9e65…5b331023` |

## 4. Forbidden-construct scan

Zero occurrences of `sorry`, `admit`, `native_decide`, or user-declared `axiom` in any of the
32 sources. The proofs are explicit term/tactic constructions (`True.intro`, `rfl`,
`False.elim`, `And.intro`, `Exists.intro`, `cases`), which is consistent with a corpus whose
theorems depend on at most `propext`.

## 5. Axiom footprint — VENDOR-CLAIMED (pending independent reproduction)

Reproduced verbatim from the shipped `*AxiomAudit.out` files. **This is documentary evidence,
not a machine result of this attestation** — it will be regenerated locally during the deferred build.

- Audited declarations across the 14 wave audit files: **181**
- Depend on **no axioms**: **111**
- Depend on **`propext` only**: **70**
- Depend on any **non-standard / user-added** axiom: **0**
- Book Three / Book Four final-audit roots (34 firewall non-entailment theorems): all **`propext`**

If the local build reproduces these exactly, the corpus is axiom-honest (only the standard,
universally-trusted `propext`, and mostly nothing at all). Any divergence will be reported as a finding.

## 6. Constitutive firewall (carried, not weakened)

A passing Lean build establishes **consequences of the submitted formal models only**. Book Four's
theorems are explicitly *non-entailments* (e.g. `vocabulary_schema_does_not_entail_conformance`,
`no_hit_search_does_not_entail_novelty`). Their finite witnesses prove a specified model is inhabited;
they do **not** establish historical fidelity, empirical adequacy, standards conformance,
interoperability, production safety, governance legitimacy, novelty, or priority. Those remain open
external obligations, exactly as the corpus's own README states.

## 7. Deferred step — how the compile will be completed

Off-peak (or after freeing ~1 GB RAM), run under the pinned toolchain with `LEAN_PATH` set to the
source dir, in dependency order:

```
Wave16 … Wave29 → BookThree → BookFour → BookThreeFinalAudit → BookFourFinalAudit
then: lean WaveNNAxiomAudit.lean   (N=16..29)   # reproduces #print axioms
```

On completion, `compile_result` for each file and the reproduced per-declaration axiom footprints
replace the `DEFERRED` markers in both this file and the JSON, yielding a full independent verdict.
