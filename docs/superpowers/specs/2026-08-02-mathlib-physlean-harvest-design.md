# Mathlib + PhysLean Harvest — Design Spec

**Date:** 2026-08-02 · **Status:** design · **Owner:** Riemann Lab / Verified Core

## Goal

Scale the verified substrate from ~1,449 hand-built Brockian theorems to **all of formally-verified
mathematics and physics** — by indexing Mathlib (all of math) and PhysLean (physics) into the
registry as first-class, provenance-tagged verified declarations. This is the substrate under the
"verified visualization + calculation" calling card: a picture or a computation can bind to *any*
theorem in Mathlib/PhysLean, not just the Brockian core.

**Non-goal:** re-proving Mathlib. We *index* an already-verified library; we do not claim we proved
it. That distinction is the load-bearing honesty decision of this spec (§2).

## 1. Why this is different from the existing pipeline

The certificate factory (`settle`/`refute`) verifies *our* claims through *our* gate (AXLE +
`#print axioms` + no-theater). Mathlib/PhysLean theorems are already verified — by Lean's own kernel
during their library build. So the harvest is an **indexing** problem, not a verification problem:
walk a built environment, record each declaration's name, type, module, and axiom footprint, and
join it to the registry with honest provenance.

## 2. The honesty model (the critical design decision)

A harvested theorem must **never** read as "proved by us." The register gains an explicit
`verified_by` provenance facet, orthogonal to the register:

| `verified_by` | meaning |
|---|---|
| `AXLE` | verified through our independent gate (the current Brockian core) |
| `local-build` | reproduced by a local `lake build` + `#print axioms` on our toolchain |
| `mathlib-kernel` | indexed from a built Mathlib environment — Lean-kernel-verified upstream |
| `physlean-kernel` | indexed from a built PhysLean environment |

Rules the firewall (`verify_firewall.py`) will enforce, extended:
- A harvested decl is `PROVED` **only if** its `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}
  and it carries no `sorry`. Mathlib decls that use extra axioms (rare) are tagged accordingly and
  excluded from `PROVED`.
- `source ∈ {brockian, mathlib, physlean}` is recorded on every entry. Counts are always reported
  **split by source** — headline "N proved" never silently mixes "we proved" with "we indexed."
- The Brockian core `import`s Mathlib; harvested Mathlib entries and Brockian-original entries are
  de-duplicated by fully-qualified name. Brockian-original = declared in a `Brockian.*` module.

## 3. Extraction architecture

**Method:** Lean metaprogramming over a *built* environment — the robust route, not source parsing.
A small Lean tool walks `Environment.constants`, and for each theorem/def emits a JSON record:
`{ name, kind, module, type (pretty), axioms (via CollectAxioms), sorryFree }`.

- Mathlib: run against a built Mathlib (`lake build` where the olean cache is reachable).
- PhysLean: same, against a built PhysLean.
- Axiom footprint: `Lean.collectAxioms` per declaration (batched; the expensive step).

**Where it runs — NOT the Mac Mini.** The Mini (16 GB) cannot build Mathlib (env-blocked; documented
thrash). The harvest runs where Mathlib builds: a CI runner / cloud box with the olean cache, or a
LeanDojo-style prebuilt environment. Output is a JSON/NDJSON dump the Mini ingests. The Mini stays the
control plane; the harvest is a batch producer.

## 4. Storage at scale

~200k+ Mathlib declarations will not fit the single `registry/theorems.json`. Introduce a scalable
store:
- **`verified_declarations`** table (Supabase / SQLite): `name, source, module, kind, register,
  verified_by, axioms[], sorry_free, type, harvested_at, mathlib_rev`.
- `registry/theorems.json` remains the **Brockian-original** source of truth (small, git-tracked).
- The harvested corpus is a separate, larger store queried by the site + viz + `settle` (for reuse).
- A read API `GET /api/verified/search?q=...&source=...&register=...` serves the viz binding (§ A).

## 5. Register derivation for harvested decls

Reuse `derive_register` semantics with the provenance facet:
- theorem/lemma + axiom-clean + sorry-free → `PROVED` (`verified_by: mathlib-kernel`).
- def/structure → `DEFINITION`. `Prop`-container with no proof → not applicable (Mathlib has none).
- extra axioms → `PROVED (nonstandard-axioms)` tag, excluded from the clean headline count.

## 6. Integration points

- **Certificate factory** — harvested theorems become the *reuse substrate*: `settle` can cite a
  Mathlib lemma as a dependency without re-proving it; the dependency graph spans both.
- **Verified visualization (§ A component)** — a lab's visual claim resolves against the harvested
  store, so any Mathlib/PhysLean fact can back a picture, with its provenance shown honestly.
- **PhysLean → quantum bridge** — indexed physics (Hilbert spaces, operators, quantum formalisms)
  is the substrate for QuantumProof/IonQ verified circuits and error/entropy bounds, and for physics
  labs on torus.

## 7. Risks & mitigations

| Risk | Mitigation |
|---|---|
| Overclaim: "we proved Mathlib" | `source` + `verified_by` on every entry; counts always split by source; the site never merges them |
| Scale (200k decls, storage/compute) | dedicated store (§4); axiom collection batched; incremental harvest keyed on `mathlib_rev` |
| Can't build Mathlib on the Mini | harvest runs on a cache-reachable CI/cloud box; Mini ingests the dump |
| Version drift (Mathlib updates) | record `mathlib_rev`; re-harvest per pinned toolchain; the Brockian core pins its own |
| PhysLean maturity/coverage | treat PhysLean as a smaller, curated first target; expand as it matures |

## 8. Phased rollout

1. **Extractor** — the Lean env-dump tool; validate on a small Mathlib subset (name, type, axioms).
2. **Store + provenance** — the `verified_declarations` schema + `verified_by`/`source` facets;
   extend `verify_firewall.py` to enforce the split-by-source honesty rule.
3. **Full Mathlib harvest** — batch run on a cache-reachable box; ingest to the store.
4. **Search API + viz binding** — `GET /api/verified/search`; wire the § A component to it.
5. **PhysLean harvest** — same pipeline; light the physics labs + the quantum bridge.

## Acceptance

- Every harvested entry carries `source` + `verified_by`; no headline count merges "proved" with
  "indexed"; the firewall fails if it does.
- A viz claim can resolve against Mathlib and render its honest provenance badge.
- The Brockian-original registry is unchanged and de-duplicated against the harvest.
