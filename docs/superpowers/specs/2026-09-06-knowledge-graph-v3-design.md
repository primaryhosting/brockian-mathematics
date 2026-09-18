# Knowledge Graph v3 — "the graph that understands itself"

Date: 2026-09-06
Status: APPROVED (Chris) — build overnight on a swarm.
Owner: ACUTIS / Riemann Lab

## Goal

Make the Riemann Lab Aristotle knowledge graph *bigger, smarter, more capable, and
remarkable* — not by adding nodes (it already has 13,744) but by making the graph
**understand itself** (analytics), **reason by meaning** (semantic embeddings), and
be **interrogable** (ask-the-graph). All delivered through the existing living-GitHub
static pipeline. Same honesty firewall. No new always-on infra.

## Non-negotiable constraints (read first)

1. **Delivery = static files in `~/Projects/riemann-corpus-data`**, fetched by the
   Lovable site via raw.githubusercontent.com. No service key. No DB writes.
2. **Do NOT modify the live loop while building.** `~/Scripts/riemann-corpus-sync.sh`,
   `build_graph.py`, and `build_graph2.py` are RUNNING every 30 min and must keep
   working. v3 is a **new standalone script `build_graph3.py`** + a new embedder.
   Wiring into the sync script happens only at the end, by the human-in-loop owner,
   after v3 outputs are proven deterministic.
3. **Determinism is mandatory.** PYTHONHASHSEED randomizes set/dict iteration and has
   already caused spurious daily git churn once. Every list written to disk MUST be
   explicitly sorted by a stable key. A double-build `cmp` must show byte-identical output.
4. **Honesty tiers preserved.** ARISTOTLE_CANDIDATE proofs are never presented as
   verified. Registry nodes have **statements stripped** — their embeddings are built
   from `name`+`module` only and MUST be flagged `emb_tier:"name_only"` vs `"rich"`.
   Analytics metrics are "structural, over *detected* citations," not ground truth.

## Node identity (the anchor — align to this exactly)

From `build_graph2.py`:
- theorem node id = `"t::" + name` (full registry theorem name).
- node set = **union of `verified-registry.json.theorems[].name` (13,104) and
  `aristotle-datastore.json.proofs[].target` (1,338)** = 13,744 theorem nodes.
- `field::<F>`, `concept::<F> › <C>`, `th::<slug>` for the other node types.
- A proof "has source" iff its `target` is a datastore proof (has `statement`,`source`,`content_hash`).
- Classification: reuse `build_graph2.classify_registry(name)` topic rules + `classify_corpus`.
  Do not reinvent taxonomy.

## Data inputs

- `~/Projects/brockian-mathematics/torus/public/aristotle-datastore.json` — 1,338 proofs
  with `{id,target,statement,source,content_hash,tier,...}`.
- `~/Projects/riemann-corpus-data/verified-registry.json` → `.theorems` — 13,104 rows with
  `{name,module,register,kind,axle_verdict,axioms_ok,sorry_free,...}` (statement empty).
- `~/Projects/riemann-corpus-data/athenaeum/thinker_sources_harvest.json` — 257 rows
  `{slug,title,year,url,license,kind,thinker_id}`.
- `~/Projects/brockian-mathematics/scripts/thinkers2.json` — 66 thinkers.
- Existing v2 dependency edges live in `graph2-edges.json` (`dependency`,`sim_content`,`sim_method`).

## Components

### A. Embedder — `scripts/embed_corpus.py` (long-pole, runs in background)
- Model: **Gemini `gemini-embedding-001`**, `outputDimensionality:768`, `taskType:SEMANTIC_SIMILARITY`.
  (OpenAI is out of credits; do not use it.) Key from `~/.openclaw/load-vault.sh` → `$GEMINI_API_KEY`.
- Endpoint: `POST /v1beta/models/gemini-embedding-001:batchEmbedContents?key=…` (batched); fall
  back to single `:embedContent` on batch error. Chunk size ≤ 100, exponential backoff on 429.
- **Resumable cache**: `~/Projects/brockian-mathematics/data/embeddings.jsonl`, one row
  `{"name":<theorem name>,"h":<sha1 of embed-text>,"v":[float,…768]}`. On each run, embed only
  names whose `h` changed or are missing. Free-tier daily caps are fine — it resumes next run.
- Embed text: rich nodes → `f"{name}\n{statement}\n{source[:1500]}"`; name-only nodes →
  `split_camel(name) + " " + split_path(module)`. Record `emb_tier` per node elsewhere (layout step).
- Idempotent, side-effect-free except the cache file. Log progress to
  `~/.openclaw/logs/embed_corpus.log`.

### B. `scripts/build_graph3.py` — the intelligence build (consumes registry+datastore+cache)
Writes to an output dir (default the persist repo). All outputs deterministic (sorted).

1. **Analytics** → `graph3-analytics.json`
   - Build directed dependency graph from v2 `dependency` edges (recompute the same way if
     graph2-edges absent). Compute, pure-python/numpy, deterministic:
     - `pagerank` (power iteration, fixed 100 iters, damping 0.85, sorted node order).
     - `betweenness` (Brandes; if >~4k nodes in the dep subgraph, run on the dependency
       subgraph only — isolated nodes get 0 — and note the scope in the file).
     - `in_degree`,`out_degree`.
     - `community_id` via **deterministic label propagation** (sorted seed = node index,
       fixed iteration count, ties broken by smallest community id then node id) over the
       UNDIRECTED union of dependency + semantic-neighbor edges.
   - Emit: per-node metrics map keyed by `t::name`; `keystones` (top-50 by pagerank),
     `bridges` (top-50 by betweenness), `communities` (id → {size, dominant_field,
     exemplars:[top-8 by pagerank], label}). `label` = most common concept in community.
   - Honesty header: `"scope":"metrics computed over detected Lean-citation graph; not ground truth"`.

2. **Semantic layout + neighbors** → `graph3-layout.json`, `graph3-neighbors.json`, `graph3-vectors.bin`(+`.json` manifest)
   - Load vectors from cache for all nodes that have them. Missing → excluded from semantic
     outputs (listed in a `missing` count; never fabricate a vector).
   - **Layout**: L2-normalize, **PCA to 3D** (numpy SVD, sign-fixed: force the component's
     largest-magnitude loading to be positive). Scale coords to a fixed cube. Write
     `{name: [x,y,z], emb_tier}` sorted by name.
   - **Semantic neighbors**: top-8 cosine neighbors per node via chunked matmul; write sorted
     edge list `[{"s","t","w"}]` (s<t, w rounded 3dp), sorted by (s,t). This supersedes v2 sim_content.
   - **In-browser search vectors**: int8-quantize (per-vector scale) the **rich-tier** vectors
     only (~1,338 × 768 ≈ 1 MB) → `graph3-vectors.bin` + manifest `{names[],dims,scale[]}` so the
     client can cosine-rank a query embedding. Name-only bulk stays server-side/neighbor-edges.

3. **Structural query index** → `graph3-index.json`
   - Compact adjacency for client-side traversal & shortest-path with **no LLM**:
     forward+reverse dependency adjacency (id→[ids]), node meta `{field,concept,tier,has_source,
     pagerank,community_id}`, and a name→id lookup. Keep it small; ints not strings where possible.

4. **External-link nodes** → folded into `graph3.json` overview
   - Add `source_doc` nodes from `thinker_sources_harvest.json` (`sd::<slug>`), each edged to its
     `th::<thinker>` (via `thinker_id`→slug map). Title/year/url/license carried through.
   - Mathlib/Metamath cross-links are **explicitly deferred** to a separate Formal-Atlas spec;
     leave a documented empty `external_libs:[]` slot in the schema. Do not build the mapping now.

5. **Overview** → `graph3.json` — counts, legends, field/concept/community rollups, thinker &
   source-doc nodes, keystone/bridge summaries. Mirrors the v2 overview shape so the frontend can
   extend rather than rewrite.

### C. Frontend (Lovable project `dd8308ac`, serial — owner-driven, NOT a swarm task)
- New **"Intelligence" mode** on `/verified/aristotle/graph`: node size ∝ pagerank, keystones
  glow by betweenness, toggle color-by-community vs color-by-field, **"semantic space" layout
  toggle** (PCA coords), keystone/bridge spotlight, pulse-along-dependency animation from a
  selected node.
- **Ask-the-graph panel**: structural queries client-side (filters, "what depends on X"
  transitive, shortest path between two nodes, neighbors by meaning/method, in-browser semantic
  search via `graph3-vectors.bin`). Natural-language mode routes through the existing narration
  LLM path / a thin `graph-ask` edge function that emits a *validated* query (cannot invent nodes).
- Additive only. Tiers preserved; name-only embeddings visibly marked.

## Swarm boundaries (what agents may/may not touch)

- **May create/edit**: `scripts/embed_corpus.py`, `scripts/build_graph3.py`,
  `scripts/graph3_*.py` helpers, `scripts/test_graph3.py`, this spec's sibling notes,
  and write OUTPUT json into a scratch/out dir for verification.
- **May read**: everything.
- **MUST NOT edit**: `~/Scripts/riemann-corpus-sync.sh`, `build_graph.py`, `build_graph2.py`,
  `classify_corpus.py`, `taxonomy_overrides.json`, anything in `~/Projects/riemann-corpus-data`
  working tree except a designated `out/` scratch dir. No git commits/pushes. No Lovable calls.
- **MUST NOT** call OpenAI, start LaunchAgents, or touch the vault beyond reading `$GEMINI_API_KEY`.

## Testing / acceptance

- `test_graph3.py`: double-build produces byte-identical files (determinism); pagerank sums≈1;
  no NaN/inf coords; every semantic edge endpoint exists as a node; community count in a sane
  range (2..200); rich vector count == number of datastore proofs with a cached vector;
  every `emb_tier` ∈ {rich,name_only}; overview counts equal sums of parts.
- Adversarial verify pass: an independent agent tries to break determinism and honesty
  (candidate leaking as verified, name-only vector treated as rich, fabricated nodes/edges).

## Sequencing

1. Embedder runs in background from the start (backfills the vector cache over hours).
2. Analytics + structural index + external-link nodes need **no vectors** → build first.
3. Layout + semantic neighbors + vector.bin consume the cache → build against whatever is
   cached, re-run when the backfill completes.
4. Verify (tests + adversarial). 5. Human wires `build_graph3.py` into the sync loop.
6. Frontend Intelligence mode + ask-the-graph (owner-driven via Lovable).
