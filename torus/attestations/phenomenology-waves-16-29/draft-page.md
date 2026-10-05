# DRAFT — Riemann Lab page: "Phenomenological Mathematics · Book Three & Four"

> ⚠️ DRAFT / NOT PUBLISHED. Intended for torus.riemannlab.com once the compile gate in
> `STATUS.md` is cleared. Copy is written for the CURRENT partial state; the bracketed
> [[UPGRADE-ON-GREEN]] spans flip when verification completes.

## Hero

**Phenomenological Mathematics — Waves 16–29**
A 14-module Lean 4 corpus formalizing constitution, institutions, evidence, ontology, and
external-validation review contracts. Pure core Lean (`Init`-rooted, no Mathlib).

**Status chip:** 🟡 *Static-verified — machine compile pending* &nbsp;[[UPGRADE-ON-GREEN → ✅ Independently verified (Lean 4.32.0)]]

## What is verified right now

- **Source identity:** all 32 submitted `.lean` files match their manifest SHA-256 (32/32).
- **No proof holes:** 0 `sorry`, 0 `admit`, 0 `native_decide`, 0 user-added axioms.
- **Scope:** 234 theorems; 181 audited by `#print axioms`; 34 governing "firewall" non-entailment theorems.

[[UPGRADE-ON-GREEN: add — **Machine-checked:** all 32 files compile under Lean 4.32.0;
reproduced axiom footprints = 111 axiom-free + 70 `propext`-only, 0 non-standard.]]

## The honesty firewall (the point of the corpus)

Book Four does not claim the program is historically faithful, empirically adequate, standards-
conformant, novel, or has priority. It **proves the opposite of the shortcut**: e.g.
*standard vocabulary + a schema-valid artifact does **not** entail conformance*; *a prior-art
search returning no hits does **not** entail novelty*. A passing Lean build establishes
consequences of the formal models only — never an external review verdict.

## Still open (shown honestly)

- **Waves 1–15** exist as prose only — not yet formalized (see crosswalk).
- **Wave 30 / BookFive** referenced in a corpus doc but absent from the submission.
- External reviews (archival, empirical, standards, prior-art) remain open obligations.

## Artifacts (link when published)

- `ARISTOTLE-ATTESTATION.md` / `.json` — file-by-file verdicts + verified hashes
- `MISSING-FORMAL-SOURCES.md` · `DOCUMENT-TO-THEOREM-CROSSWALK.md`

---
*Rendering note:* until green, the status chip MUST use the neutral/pending style, never the
green verified badge — consistent with `torus/README.md` §4 ("a conjecture is not" a proof).
