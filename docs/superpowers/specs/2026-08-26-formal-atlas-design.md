# The Formal Atlas — Design

**Date:** 2026-08-26
**Status:** Approved design (Approach A: Harvest → Align → Serve)
**Home:** torus.riemannlab.com `/atlas` · data repo `primaryhosting/formal-atlas` (public) · Riemann Supabase

## 1. Mission

A living atlas of all formally verified mathematics: one public map where a "place"
is a mathematical statement (a **concept**), and every machine-checked verification
of it — in Lean/Mathlib, Isabelle/AFP, Coq/Rocq, Metamath, HOL Light, Mizar, and the
Brockian corpus — is attached to that place with full provenance. The atlas also
shows the **frontier**: famous theorems verified nowhere yet.

Nobody has this well. Per-library browsers exist; a concept-centric, cross-library,
continuously updated map does not. Riemann Lab is its home.

## 2. Goals / Non-goals

**Goals**
- Concept-centric map: one node per mathematical statement, N verifications attached.
- Living: scheduled harvesters keep every library layer fresh; Brockian follows the
  prover automatically (it already regenerates `/verified-registry.json` every ~30 min).
- Honest: every cross-library equivalence claim carries a confidence tier and
  provenance. No silent equivalences, no invented counts — all displayed numbers are
  measured by harvesters, never estimated.
- Frontier view: absorbs and supersedes the existing `/targets` top-100 board.
- Brockian corpus is a first-class highlighted layer (where we extend the world corpus),
  but structurally one library among peers.
- Citable: every harvest publishes a versioned dataset release ("editions" for free).

**Non-goals**
- Verifying proofs ourselves. The atlas *reports* each library's own checked status;
  it never re-checks foreign proofs and never claims more than the source asserts.
- Aligning all ~10⁵–10⁶ statements to concepts. The statement layer is exhaustive;
  the concept layer is curated and grows deliberately.
- Proof content rendering for foreign libraries (link out to each library's own pages).

## 3. Architecture

```
GitHub Actions (schedule, per-library)          Riemann Supabase           torus.riemannlab.com
┌─────────────────────────────────┐   upsert   ┌──────────────────┐  read  ┌────────────────┐
│ harvesters/  (formal-atlas repo)│ ─────────► │ atlas_* tables   │ ─────► │ /atlas section │
│  mathlib · afp · metamath ·     │            │ (anon RLS read)  │        │ (Lovable       │
│  coq · hollight · mizar ·       │  release   └──────────────────┘        │  dd8308ac)     │
│  brockian                       │ ─► JSON editions (GitHub Releases)     └────────────────┘
└─────────────────────────────────┘
```

Three units, each independently testable:

1. **`formal-atlas` repo (pipeline + dataset, public).** One harvester per ecosystem,
   all emitting the same normalized schema. GitHub Actions runs them on schedule and
   (a) upserts to Supabase, (b) attaches the normalized JSON to a tagged release.
   The Mac Mini runs none of this.
2. **Riemann Supabase (`atlas_*` tables).** The serving database. Anon-key read via
   RLS SELECT policies (same pattern as BCC tables); writes only via the pipeline's
   service key stored as a GitHub Actions secret.
3. **`/atlas` frontend** in the existing Lovable project `dd8308ac`
   (torus.riemannlab.com), reading Supabase. Registered in `site-registry.ts`,
   promoted into the primary "Verified" nav.

## 4. Data model (Supabase)

All tables prefixed `atlas_`.

- **`atlas_libraries`** — one row per ecosystem: `id, slug, name, prover, url,
  license, harvester_version, last_harvest_at, statement_count` (count is written by
  the harvester, displayed verbatim).
- **`atlas_statements`** — the exhaustive layer, one row per harvested declaration:
  `id, library_id, native_name` (e.g. `Complex.isAlgClosed`), `kind`
  (theorem/definition/axiom…), `statement_text` (pretty-printed, when the source
  provides it), `module`, `source_url`, `subject_codes text[]` (MSC 2020, when
  derivable), `first_seen_edition, last_seen_edition, retired boolean`.
  Statements that disappear upstream are marked retired, never deleted (no-delete rule).
  **Identity key** = `(library_id, native_name)`; an upstream rename therefore reads
  as retire+add — accepted semantics, and why `retired` counts are reported per
  edition rather than cumulatively headline-displayed.
- **`atlas_concepts`** — the curated layer: `id, slug, title, informal_statement,
  wikidata_id?, msc_primary, seed_source` (wiedijk100 / targets-board / curated /
  llm-proposed), `status` (open / partially-formalized / formalized), `notes`.
- **`atlas_alignments`** — the join with epistemic state: `concept_id, statement_id,
  tier` (**CURATED** = human/Wiedijk-sourced · **ALIGNED** = high-confidence with
  recorded evidence · **CANDIDATE** = machine-proposed, unconfirmed), `evidence`
  (jsonb: who/what matched it, model + prompt hash for LLM matches), `created_by,
  confirmed_by?`. Tier is rendered wherever the alignment is shown.
  **Curation write path:** curated concepts and tier promotions live as versioned
  files in the `formal-atlas` repo (`concepts/*.yaml`) — curation-as-code, so the
  no-delete/provenance story is git history; the pipeline syncs them to Supabase.
  No human writes directly to Supabase and no admin UI in v0/v1.
- **`atlas_harvest_runs`** — provenance spine: `library_id, started_at, edition_tag,
  source_commit/version, statements_seen, added, retired, status, log_url`.
  Every page footer cites the edition + per-library harvest timestamps it reflects.
  **Editions are global:** a weekly release workflow mints edition `N` as a cut
  across each library's latest successful harvest; `edition_tag` on a run (and
  `first/last_seen_edition` on statements) is the edition that first shipped that
  data. Per-library cadences stay independent underneath.

## 5. Harvesters

Each harvester is a standalone script (`harvesters/<library>/harvest.py`) with the
contract: *emit `statements.jsonl` in the normalized schema + a `manifest.json`
(source version, counts, checksums)*. A shared loader validates and upserts.

| Library | Source of truth | Cadence | Notes |
|---|---|---|---|
| Brockian | `/verified-registry.json` (prover-owned, sanitized) | 6 h | Never read raw `registry/theorems.json` for public display; the sanitized export is the badge authority. |
| Mathlib (Lean 4) | doc-gen4 declaration export / mathlib4 repo | daily | Largest mover; ~10⁵ declarations. |
| Metamath | `set.mm` (single parseable file) | weekly | Simplest harvester — build it first to prove the schema. |
| Isabelle AFP | AFP entry index + Isabelle name exports | weekly | Entry-level metadata first; statement-level as a later deepening. |
| Coq/Rocq | Coq Platform / opam package indexes | weekly | Package-level first, statement-level later. |
| HOL Light | distribution's theorem lists | monthly | |
| Mizar | MML abstracts | monthly | |

Ship order: **Brockian → Metamath → Mathlib** (v0), then AFP, then the rest. A
library whose statement-level harvest isn't built yet appears in the atlas as a
library card with entry/package-level data and an explicit "statement-level harvest:
not yet built" chip — coverage honesty over the appearance of completeness.

Failure handling: a harvester failure marks `atlas_harvest_runs.status=failed` and
leaves the previous data standing with its old timestamp visible; it never partially
overwrites. Schema-drift upstream (the common failure) fails validation loudly in CI.

## 6. Alignment layer (the novel core)

- **Seed (v0):** Freek Wiedijk's "Formalizing 100 Theorems" list — ~100 canonical
  theorems already hand-tracked across exactly these systems — imported as CURATED
  concepts + alignments. Plus our existing `/targets` top-100 board (104 problems,
  25 with formalized statements in the Brockian corpus) as concepts.
- **Growth:** (1) curated additions (each lab's PROVED claims map to concepts);
  (2) LLM-assisted matching proposes CANDIDATE alignments (statement text similarity
  + name heuristics), which a human or a high-bar verification pass promotes to
  ALIGNED with recorded evidence. CANDIDATEs are visibly marked and excluded from
  headline counts.
- **Honesty rules:** headline numbers count only CURATED + ALIGNED. A concept page
  showing "verified in 6 systems" links each of the 6 to its native source. Where
  two libraries formalize *different strengths* of a theorem, the alignment evidence
  says so; when in doubt, tier down.

## 7. Frontend (`/atlas` on torus.riemannlab.com)

Follows the existing DepthShell/register discipline and dual-theme legibility rules.

- **`/atlas`** — home: world counts (per-library, harvester-measured, with as-of
  timestamps), the concept map entry points, and the Brockian layer toggle.
- **`/atlas/concept/:slug`** — concept page: informal statement, MSC territory,
  status, and one card per verification (library, native name, source link, tier
  chip). The atlas's canonical page type.
- **`/atlas/territory/:msc`** — subject territories with coverage shading per
  library (only over statements that carry MSC codes; the "unclassified" mass is
  shown, not hidden). MSC derivation per library: Mathlib module paths, AFP topic
  tags, MML section structure, Metamath chapter headers, Brockian domain field —
  each recorded in the harvester manifest.
- **`/atlas/frontier`** — famous statements with zero verifications anywhere +
  partially-formalized concepts; absorbs `/targets` (which 301s here in v1).
- **`/atlas/library/:slug`** — library layer page; Brockian's highlights where it
  extends the world corpus (singular-series family, Weyl family, EGZ, …).
- **Search** — server-side (Supabase full-text over `atlas_statements.native_name`
  + `statement_text` + concept titles); no client-side megabyte dumps.
- Existing surfaces: Lab-50 Atlas stays (site-claims scope, cross-links); `/targets`
  redirects to `/atlas/frontier`; `/explore/lean-registry` becomes the Brockian
  library deep-browser linked from `/atlas/library/brockian`.

## 8. Testing & integrity gates

- **Harvester CI:** schema validation on every emit; golden-file tests per harvester
  on pinned upstream fixtures; count deltas beyond ±20% require a manual approval
  label (guards against silently harvesting garbage).
- **Site gate (pattern from `atlas.golden.test.ts`):** every rendered alignment
  resolves to a real statement row; every headline count recomputes from the data;
  CANDIDATE tiers never enter headline counts (test-enforced).
- **Provenance:** every page renders the edition tag + harvest timestamps it reflects.

## 9. Ops & security

- Pipeline: GitHub Actions in `formal-atlas` (public repo, secrets: Supabase service
  key only). Mac Mini not in the loop.
- Supabase: RLS SELECT-to-anon on `atlas_*` read tables; service-role writes only.
  ⚠ Known issue: the existing `RIEMANN_SUPABASE_KEY` 401s as service key (per the
  fleet-panel blocker) — mint/confirm a real service key before pipeline writes,
  and store it in GitHub Actions secrets, not just the vault.
- Licensing: dataset releases carry per-library license notices (Mathlib Apache-2.0,
  set.mm CC0, AFP per-entry, …); metadata-only harvesting keeps this simple.
  AFP rule: harvest names/entry/authors + each entry's license string onto its rows;
  statement bodies are included in releases only where the entry's license permits,
  otherwise name + link only.
- Cost: Actions minutes (public repo = free), Supabase storage ~1–2 GB at full scale;
  LLM alignment passes are batched and budget-capped.

## 10. Phasing

- **v0 (Edition 0):** `formal-atlas` repo + schema + 3 harvesters (Brockian,
  Metamath, Mathlib) + Wiedijk-100 & targets-board concept seed + `/atlas` home,
  concept pages, frontier. Proves harvest→align→serve end-to-end with honest gaps
  ("4 libraries not yet harvested" stated on the home page).
- **v1:** AFP + Coq harvesters, territories view, LLM CANDIDATE proposer +
  promotion workflow, nav promotion on riemannlab.com, `/targets` redirect.
- **v2:** HOL Light + Mizar, statement-level AFP/Coq deepening, API endpoint for
  third parties, editions announcement loop.

## 11. Risks

- **Alignment overclaiming** — the reputational risk. Mitigated by tiers, evidence
  records, tier-down-when-in-doubt, and headline counts excluding CANDIDATE.
- **Upstream format drift** — harvesters break; mitigated by loud CI validation and
  last-good-data-standing semantics.
- **Scope creep on the concept layer** — mitigated: exhaustive at the statement
  layer, deliberately curated at the concept layer; v0 ships with ~200 concepts.
- **Two-registry confusion (Brockian)** — already solved site-wide: the sanitized
  `/verified-registry.json` is the single public authority; the atlas obeys it.
