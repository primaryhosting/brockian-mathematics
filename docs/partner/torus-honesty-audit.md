# torus.riemannlab.com — Ruthless Honesty Audit

**Audience:** IonQ · SAIR · verification-company partners · internal registry owners  
**Site audited:** https://torus.riemannlab.com (SPA; Cloudflare deployment id `d1c76a77-1b4e-4eff-9f6d-4a09708dbc26`)  
**Audit date:** 2026-08-02  
**Method:** HTML/meta + JS bundle string extraction (no authenticated session). Cross-check against local Brockian Verified Core registry (`registry/theorems.json`, `observatory/claims.json`) and marketing/legal surfaces.  
**Verdict:** **Not partner-safe as a verification company shopfront.** The product *brand* is dual formal verification; the *ledger* is a separate, disciplined system that torus does **not** consume. Shipping IonQ/SAIR demos off this surface without a badge/registry wire risks existential contradiction.

---

## Executive judgment (one paragraph)

Torus is an impressive **engagement platform** (labs, thinkers, Three.js, SAIR story UI) dressed in **verification-company language** it has not earned from its public surface. Hero and meta copy claim “world’s premier,” dual Lean 4 + Rocq formal verification, citation-grade rigor, and “No speculation.” Concurrently the same product ships **sorry-laden demo theorems**, a **hand-curated theorem registry** on Lean **4.24.0** disconnected from the AXLE-attested tip registry (Lean **4.32.0**, **1477 PROVED**), internal page-to-page **contradictions on the 53-theorem story** (41 proven / 12 axiomatized vs “all 53 / zero gaps” vs “75% verified”), and **no public** `theorems.json` / `claims.json` endpoint. Observatory charter in-repo says badges are **derived** and open problems stay **not_claimed**. Torus does the opposite: it *paints* verification.

---

## 1. What torus claims publicly

### 1.1 Meta / SEO / PWA (static HTML shell)

| Surface | Claim |
|---------|--------|
| `<title>` | Riemann Labs — The AI Mathematician |
| `meta description` | “The world's premier AI mathematics platform. **170+ thinkers, 52 interactive labs, dual Lean 4 + Rocq formal verification.** Where AI meets pure mathematics.” |
| Open Graph | “Explore mathematics with AI. Chat with 170+ historical mathematicians. Prove theorems. Generate conjectures.” |
| Twitter | Premier + dual formal verification |
| Canonical | `https://torus.riemannlab.com/` |
| Manifest | “Where AI Meets Pure Mathematics” |
| Sitemap / robots | Still point at **`prime-rigor-explorer.lovable.app`** (272 URLs) — production alias of the Lovable project |

SPA note: almost all body content is client-rendered. What partners *see* after JS load is authoritative for demos; crawlers and link previews still get the meta overclaims above.

### 1.2 Homepage hero counters (from `Index-*.js`)

Hard-coded counters (not registry-derived):

| Counter | Value |
|---------|-------|
| Thinkers | **170+** |
| Core Minds | **46** |
| Interactive Labs | **52+** |
| Lean 4 Declarations | **53** |
| Ψ Convergence | **—** / footer **Ψ = 0.00** (dead metric) |

Footer / secondary meta (same Index chunk) **contradicts** the hero lab count:

- Footer: “Lean 4 + Rocq dual verification · 170+ sourced thinkers · **140+ interactive labs** · … **No speculation — citation-grade rigor.**”
- Secondary description strings: “**140+** interactive labs” and “world’s premier…”

So the public site cannot agree with itself on **52+ vs 140+** labs, or on whether the headline Lean number is “declarations,” “theorems,” or “proven.”

### 1.3 Feature themes (homepage cards)

- Thinkers Athenaeum — 170+ mathematicians, “grounded in primary writings”
- Research Pipeline — Conjecture → Formalize → Verify → Publish
- Frontier Math — **35 open problems** from Millennium to Brockian
- Interactive Labs — 52+
- Compute Engine / Conjectures / Visualize / Physics labs
- **Verification — Dual Lean 4 + Rocq formal proof system**
- Lean Playground — prove interactively in Lean 4
- Crown jewels: Prime Distribution 3D (D₅ torus, **Goldbach tools**, theorem library), Spectral Manifold with **ζ zeros**, Brockian Waves

### 1.4 About vs Goals (direct internal contradiction)

From page chunks:

| Page | Claim |
|------|--------|
| **About** (`AboutPage-*.js`) | “**41 of 53 theorems are proven in Lean 4, 12 remain axiomatized**”; also “AI-generated content may contain errors…” and “Theorems (41 Proven)” |
| **Goals** (`GoalsPage-*.js`) | “**All 53 theorems formally verified in Lean 4. Zero axiomatized gaps.**” + “Live Lean 4 verification of Brockian theorems…” |
| **Index** | “**53 interdependent theorems, of which 75% are formally verified**” + “Layer 0 (BZFC) axioms formally verified in Lean 4 — **zero sorries remaining**” |

Three mutually incompatible stories about the same 53-theorem brand object. That alone is enough to fail a diligence question in the first five minutes.

### 1.5 “Verified” product surfaces in the SPA

| Route / page | Marketing posture | Reality from bundle text |
|--------------|-------------------|---------------------------|
| `/lean-theorem-registry` | Live Lean theorem registry, ingest 55+, sorry queue, completion rate | **Embedded** registry data (`leanTheoremRegistry-*.js`): ~**109 proven / 18 hole / 6 computational / 4 conditional / 1 conjecture**; many holes use **`proofMethod: "sorry"`**; toolchain pin **`leanprover/lean4:v4.24.0`** |
| `/lean-verification-hub` | Browser-native formal verification | Template theorems include **`sorry := sorry`** for D₅ bias cancellation and spectral Goldbach bound; UI string “**Verified proof registered on-chain**” |
| `/lean-dashboard` | LeanDojo auto-formalize + “Theorem verified and added to Knowledge Graph” | Partial proofs with sorry still flow; status language equates product “verified” with not-sorry-free AXLE PROVED |
| `/rocq` | Dual formal verification Lean + Rocq | `DualVerificationBadge` reads soft DB fields `lean_status` / `rocq_status` / `dual_verified` — **not** AXLE attestations; sample Rocq stubs prove **`True` with `trivial`** |
| `/brockian-framework-lean` | Framework formalization showcase | Mix of real-looking lemmas + **Continuum Hypothesis** “theorem” that is extension-theater; RH/Goldbach conditionals; not wired to tip registry |
| `/proofs` | Proven classical mathematics with citations | Pedagogical step-throughs (Weyl, Dirichlet, …) — **not** Brockian AXLE PROVED rows |
| Enterprise landing | “Lean 4 + Rocq dual-prover engine. Certify mathematical properties with auditable proof artifacts.” | No public artifact feed, no registry hash, no attestation download |
| Observatory / RH labs | Open problems + leanFormalization flags | Narrative proximity of RH / Goldbach / Millennium **without** mandatory OPEN badges from `observatory/claims.json` |

### 1.6 SAIR surface

`/sair-competition` is content-rich (equational theories, kernel-verified language, Axle Verifier “100ms,” EULER-style stories). That is a **competition / methodology** surface. It is *adjacent* to real work but **must not** be read as “torus UI state = SAIR submission certificates.”

### 1.7 Numbers floating in the wider org (not all on torus, but partners will google them)

| Source | Number | Conflict |
|--------|--------|----------|
| Torus hero | 53 Lean declarations | Undercounts tip registry **1811** decls / **1477 PROVED** |
| Torus About | 41 proven / 12 axiomatized | Historical “Lean FILES / pentagonal law” count |
| Torus Goals | All 53, zero gaps | Contradicts About + registry honesty |
| One-pager `~/.openclaw/deliverables/launch-docs/riemann-labs/one-pager.md` | **41 verified theorems** | Same stale 41 |
| Legal briefing | 1,300+ machine-verified + 53 core (41/12) | Mixes campaign totals with core story |
| Offering matrix | **1,300+** theorem library license | Close to tip PROVED ~1477 but **not linked** to public torus |
| TrendRadar QP blurb | **41 machine-verified theorems** | Stale; wrong product surface |
| Marketing context | One-liner: **“Proving the unprovable.”** | Directly hostile to verification brand |
| Tip `registry/theorems.json` (2026-08-02) | **PROVED 1477 · DEFINITION 306 · CONDITIONAL 21 · DISCHARGED 6 · CONJECTURE 1** | SSOT for partners |

---

## 2. Contradiction risks vs Brockian registry discipline

### 2.1 What the registry actually requires

From `README.md` / `docs/REGISTRY-CONSISTENCY.md` / `observatory/claims.json` charter:

| Register | Gate (short) |
|----------|----------------|
| **PROVED** | sorry-free + `#print axioms ⊆ {propext, Classical.choice, Quot.sound}` + no smuggled `native_decide` + **independent AXLE verified** at named env |
| **COMPUTATION** | finite decide checks — never sold as PROVED |
| **CONDITIONAL** | named hypothesis + rung (classical / literature / open) |
| **CONJECTURE** | nullary Prop container — never a theorem |
| **OPEN / not_claimed** | RH, global Goldbach, twin infinitude stay **not claimed** |

Observatory charter (machine text):

> Badges are derived from the Lean registry when `lean` is non-empty.  
> PROVED requires AXLE-verified + axiom-clean theorems.  
> Open problems (twins infinitude, Goldbach global, RH) stay **not_claimed**.

### 2.2 Explicit open / non-claims (must appear on any partner-facing torus)

From `observatory/claims.json` (generated 2026-08-02):

| Claim ID | Status | Meaning |
|----------|--------|---------|
| **OPEN-RH** | not_claimed | Riemann Hypothesis |
| **OPEN-GOLDBACH** | not_claimed | Binary Goldbach (global) |
| **OPEN-TWIN-INF** | not_claimed | Twin primes infinitude |
| **GC-TRANSFER** | conjecture | Global residual transfer |
| **GC-SCHEMA** / **RH-BROCKIAN-SYSTEM** | conditional | Schema implications only |
| **RH-XI-BRIDGE** / **XI-FUNC-EQ** | proved scaffolding | **Not** RH |

`Brockian/GoldbachComb.lean` states transfer material **must not be treated as machine-verified** without the full proof; transfer is a **named conjecture**.

### 2.3 How torus violates the firewall

| Discipline rule | Torus failure mode |
|-----------------|--------------------|
| Registers are **derived**, never hand-painted | Hero **53**, About **41/12**, Goals **all 53**, Index **75%**, embedded registry **~109 proven** — five different hand paints |
| PROVED ⇔ AXLE + axioms | UI “verified” / dual_verified / knowledge graph / **on-chain** without attestation IDs |
| Open problems stay open | Goldbach **labs**, RH forge, “Spectral Realization ⟹ RH” conditional rows without permanent **OPEN** chrome; RH listed as searchable **theorem** type in command palette |
| No theater (`sorry`/`admit` blocked in closed modules) | Verification hub **ships** `theorem … : sorry := sorry`; registry lists **holes** for `|D₅|=10`, cos(2π/5), operator self-adjointness — while tip Brockian core has **PROVED** analogues under different names/modules |
| Single SSOT (`registry/theorems.json`) | Torus Supabase edge functions (`lean-registry-ai`, `theorem_registry`, dual status tables) are a **parallel fake SSOT** |
| Toolchain honesty | Site registry **4.24.0** vs tip **4.32.0** — partners cannot recheck the same environment |
| “No speculation — citation-grade rigor” | Meta claim contradicted by About’s own “AI-generated content may contain errors” |
| Dual verification as **independent** recheck | Rocq path is optional UI + soft status, not a second prover attestation on the same declaration hash |

### 2.4 The existential product risk

A verification company whose public site:

1. advertises dual formal verification as a product feature,  
2. shows sorry-bearing “theorems,” and  
3. cannot serve `registry/theorems.json` or a signed export  

…will be **failed by the first technical partner** who clicks Lean Registry → expands a hole → asks for the AXLE attestation. That is not a polish bug; it is brand suicide for IonQ/SAIR diligence.

---

## 3. Inventory of amazing features to KEEP

These are real product strengths if **relabeled as pedagogy / exploration / ops**, not as PROVED:

1. **Scale of interactive labs** — physics, CS, number theory, moonshots (Millennium forge, Goldbach tools, spectral manifold). Engagement moat.
2. **Thinkers Athenaeum UX** — persona-scale historical interface (even if “170+” needs a countable catalog export).
3. **3D Brockian visualization stack** — D₅ torus, prime explorer, waves, phase-colored |ζ_B|; demo candy that *shows* structure.
4. **Command palette / deep route graph** — hundreds of routes; research-ops feel.
5. **SAIR competition narrative UI** — progress storytelling for equational / distillation work (keep, but certificate-backed).
6. **Lean Playground / dual-prover *lab*** concept — excellent if framed as **sandbox**, with sorry redlines.
7. **Research pipeline metaphor** — Conjecture → Formalize → Verify → Publish maps cleanly to the real problem pipeline once badges are real.
8. **Enterprise booking (Cal.com)** + collaborate CTA — partner motion exists.
9. **PWA shell, social cards, responsive dark academic chrome** — presentation quality is high.
10. **In-repo observatory generators already correct** — `scripts/gen_claims.py` / `gen_observatory.py` / `observatory/claims.json` are the right architecture; torus should **consume** them, not reinvent status enums.
11. **Crown-jewel lab framing** — Prime Distribution 3D as the demo spine for Brockian geometry (not for RH closure).
12. **Multi-surface brand** — Riemann Labs + Brockian + SAIR under one domain is fine once honesty chrome is consistent.

**Keep the cathedral. Replace the stained-glass “verified” stickers with registry glass.**

---

## 4. Punch-list — wire badges to registry / observatory

### 4.1 Contract (do this once)

| Field | Source of truth |
|-------|-----------------|
| Declaration name | `registry/theorems.json` → `theorems[].name` (or equivalent) |
| Register | `PROVED \| DEFINITION \| CONDITIONAL \| DISCHARGED \| CONJECTURE` only |
| AXLE | `axle.verdict`, `axle.environment` (e.g. `verified` @ `lean-4.32.0`) |
| Axioms gate | `axioms_ok` |
| Book / program claims | `observatory/claims.json` → `status` ∈ {proved, conditional, conjecture, open, not_claimed, …} |
| Export identity | `generated_from` + git commit / content hash of theorems.json |

**Rule:** UI may show PROVED **only if** register=PROVED **and** axle.verdict=verified **and** axioms_ok. Else badge is CONDITIONAL / OPEN / DRAFT / PEDAGOGY.

### 4.2 Engineering tasks

1. **Publish signed static exports** (or authenticated partner API):
   - `https://torus.riemannlab.com/registry/theorems.json` (or CDN) = CI artifact from brockian-mathematics tip  
   - `https://torus.riemannlab.com/observatory/claims.json`  
   - Optional: per-decl `attestations/{Module}.json`  
2. **Kill or quarantine** client-bundled `leanTheoremRegistry-*.js` as SSOT; relegate to “legacy snapshot (do not cite)” if needed during migration.  
3. **Badge component** shared by homepage, `/lean-theorem-registry`, embeds (`/embed/theorem/:id`), labs: renders register + env + link to attestation.  
4. **Homepage counters** replace hard-coded 53/41/75% with live:
   - `PROVED` count, `CONDITIONAL` count, `not_claimed` open problems count  
   - Labs/thinkers counts from real catalogs or honest “N curated” language  
5. **Open-problem chrome** on every RH / Goldbach / twin infinitude surface: fixed banner “**NOT CLAIMED — scaffold only**” driven by claim IDs OPEN-RH, OPEN-GOLDBACH, OPEN-TWIN-INF.  
6. **Sorry redline:** any code sample or registry row with `sorry`/`admit` forces badge **DRAFT** and blocks “verified,” dual_verified, and on-chain language.  
7. **Rocq dual badge:** only light when both provers have stored certificates for the **same statement hash**; otherwise “Rocq sandbox.”  
8. **Remove** “registered on-chain,” “world’s premier,” “Proving the unprovable,” “citation-grade rigor / no speculation” until true.  
9. **Align Goals/About/Index** to one Honesty Charter page (copy from strategy brief brand sentence: *We ship what is proven and mark what is not.*).  
10. **Sitemap / robots** → `torus.riemannlab.com` hosts only; drop lovable preview host from production SEO.  
11. **Toolchain badge** must match tip (`v4.32.0`) or show “historical 4.24 snapshot.”  
12. **CI check:** fail deploy if any public string matches `machine-verified|formally verified|dual verification` without a nearby registry hash or badge component.

### 4.3 Minimal data shape for torus

```json
{
  "registry_hash": "<sha256 of theorems.json>",
  "generated_at": "ISO-8601",
  "summary": { "PROVED": 1477, "CONDITIONAL": 21, "CONJECTURE": 1 },
  "decl": {
    "name": "Brockian.Admissibility....",
    "register": "PROVED",
    "axle": { "verdict": "verified", "environment": "lean-4.32.0" },
    "axioms_ok": true,
    "source": "Brockian/Admissibility.lean"
  }
}
```

Map book claims via existing `observatory/claim_map.yaml` → do **not** invent a third claim language on Supabase.

---

## 5. Priority fixes before IonQ / SAIR partner demos

### P0 — demo blockers (do before any external technical meeting)

| ID | Fix | Why |
|----|-----|-----|
| P0-1 | **Quarantine verification language** on home/meta: replace “dual Lean 4 + Rocq formal verification” and “premier” with “formalization sandbox + registry-backed core (link)” | First screen sets diligence frame |
| P0-2 | **Resolve 53-theorem contradiction** — single public number story: either tip registry summary **or** a named “Core 53” *subset* table with per-row registers — never both “all proved” and “12 axiomatized” | Partners will open About and Goals |
| P0-3 | **OPEN banners** on RH, Goldbach global, twin infinitude, Goldbach completion lab, RH forge | Explicit non-claims in observatory already exist |
| P0-4 | **Remove or mark DRAFT** every `sorry := sorry` sample and hole listed as if live research truth (`/lean-verification-hub`, registry holes for elementary D₅ facts) | One screenshot ends the meeting |
| P0-5 | **Serve `claims.json` + registry summary** on torus (static is enough) and show hash on demo slides | Proves SSOT exists |
| P0-6 | **Delete “on-chain verified,” “zero axiomatized gaps,” “Proving the unprovable”** from product + marketing context | Credibility toxins |
| P0-7 | **Demo script** only cites PROVED rows with attestation env (e.g. admissibility, ξ scaffolding, Franklin discharge) — never “we verified RH/Goldbach” | Matches strategy brief §3 |

### P1 — before second meeting / pilot SOW

| ID | Fix |
|----|-----|
| P1-1 | Wire Lean Theorem Registry page to tip `theorems.json` (read-only explorer) |
| P1-2 | DualVerificationBadge → attestation-backed or rename to “Sandbox status” |
| P1-3 | Homepage counters live from registry_summary |
| P1-4 | Fix 52+ vs 140+ labs / 236 labs (About/Goals) with one inventory export |
| P1-5 | Sitemap host cleanup; canonical consistency |
| P1-6 | Toolchain pin display 4.32.0 aligned with AXLE env |
| P1-7 | Partner one-pager numbers = registry date stamp (retire “41 theorems” everywhere) |
| P1-8 | Separate “Pedagogy proofs” (`/proofs` classical walkthroughs) from “Machine-checked registry” nav |

### P2 — productization / scale

| ID | Fix |
|----|-----|
| P2-1 | CI deploy gate (string lint + registry hash freshness) |
| P2-2 | Embed endpoints `/embed/theorem/:id` resolve only registry names |
| P2-3 | Rocq second-prover path as real dual attestation program (or drop dual from brand) |
| P2-4 | Lab content CMS field `claim_ids[]` mandatory for any “verified” chip |
| P2-5 | Public Honesty Charter page + link in footer next to “Powered by Brockian…” |
| P2-6 | Ψ Convergence either implemented from real pipeline metrics or removed |
| P2-7 | Reconcile LegalDen “1,300+” license offering with actual PROVED export process |

---

## 6. Concrete local file paths

### 6.1 Verified Core (SSOT) — `~/Projects/brockian-mathematics`

| Path | Role |
|------|------|
| `/Users/acutis/Projects/brockian-mathematics/registry/theorems.json` | Derived theorem registry (PROVED 1477 as of audit) |
| `/Users/acutis/Projects/brockian-mathematics/REGISTRY.md` | Human-readable registry |
| `/Users/acutis/Projects/brockian-mathematics/registry/attestations/*.json` | Per-module AXLE attestations |
| `/Users/acutis/Projects/brockian-mathematics/observatory/claims.json` | Public claim badges (derived) |
| `/Users/acutis/Projects/brockian-mathematics/observatory/claims.yaml` | YAML twin |
| `/Users/acutis/Projects/brockian-mathematics/observatory/claim_map.yaml` | Book claim ID → Lean names |
| `/Users/acutis/Projects/brockian-mathematics/observatory/index.html` | Static observatory UI |
| `/Users/acutis/Projects/brockian-mathematics/scripts/gen_registry.py` | theorems.json generator |
| `/Users/acutis/Projects/brockian-mathematics/scripts/gen_claims.py` | claims generator |
| `/Users/acutis/Projects/brockian-mathematics/scripts/gen_observatory.py` | HTML generator (anti-hand-paint) |
| `/Users/acutis/Projects/brockian-mathematics/scripts/no_theater_lint.py` | sorry/theater lint |
| `/Users/acutis/Projects/brockian-mathematics/scripts/audit_registry_consistency.py` | Consistency firewall |
| `/Users/acutis/Projects/brockian-mathematics/Brockian/GoldbachComb.lean` | Transfer **not** machine-verified language |
| `/Users/acutis/Projects/brockian-mathematics/Brockian/Sieve.lean` | Phase–depth torus keepers (math “torus,” not the website) |
| `/Users/acutis/Projects/brockian-mathematics/docs/partner/2026-08-02-verified-intelligence-strategy-brief.md` | Partner strategy; §5.3 already flags torus risk |
| `/Users/acutis/Projects/brockian-mathematics/docs/REGISTRY-CONSISTENCY.md` | Audit semantics |
| `/Users/acutis/Projects/brockian-mathematics/README.md` | Triple verification discipline |

### 6.2 Torus / Riemann Labs product source

| Path | Finding |
|------|---------|
| **No first-party torus app tree** found under `~/Projects` with `package.json` for the SPA | Production is **Lovable-hosted** |
| Lovable project id **`dd8308ac-0860-42ae-908c-41b306b58858`** | `~/openclaw-bridge/lovable_manager.cjs` key `spectral`; marketing context “Lovable Project: dd8308ac” |
| Preview host | `prime-rigor-explorer.lovable.app` (sitemap still uses this) |
| Production host | `torus.riemannlab.com` |
| Deployed assets (remote only) | `/assets/index-Df9lOa5Z.js`, `Index-*.js`, `leanTheoremRegistry-*.js`, `LeanVerificationHubPage-*.js`, `RocqProverPage-*.js`, `DualVerificationBadge-*.js`, … |
| Supabase edge (from bundle) | `https://ocketgwbdzpxfjjkbfyb.supabase.co/functions/v1/lean-registry-ai` — parallel registry AI, not tip AXLE |

### 6.3 Adjacent local materials (claims hygiene)

| Path | Note |
|------|------|
| `/Users/acutis/Projects/marketing-contexts/riemannlabs-context.md` | Website + **“Proving the unprovable”** |
| `/Users/acutis/Projects/RiemannLabs/` | Minimal (grant draft only) |
| `/Users/acutis/Desktop/SAIR-RIEMANN-LABS-PACKAGE/` | Whitepapers still cite **53 theorems (41 proven, 12 axiomatized)** |
| `/Users/acutis/.openclaw/deliverables/launch-docs/riemann-labs/one-pager.md` | **41 verified theorems** |
| `/Users/acutis/Projects/LegalDen/Operations/riemann-labs/offerings/RL-OFFERING-MATRIX.md` | Machine-verified deliverables; **1,300+** library license |
| `/Users/acutis/Projects/LegalDen/Compliance/lawyer-meeting-2026-05-14/00-MASTER-LEGAL-BRIEFING.md` | 1,300+ + 53/41/12 mix |
| `/Users/acutis/Projects/TrendRadar/trendradar_company_push.py` | Stale **41 machine-verified** on QP mission string |
| `/Users/acutis/Claude/Artifacts/from-signed-line-to-torus` | Artifact dir name only (math narrative) |

---

## 7. Grep findings — “machine-verified” / torus / riemannlab (local)

Representative hits (not exhaustive):

| Location | Pattern / issue |
|----------|-----------------|
| brockian-mathematics README / paper / scripts | **Legitimate** “machine-verified” gated by registry |
| GoldbachComb.lean | “**not be treated as machine-verified**” (correct honesty) |
| marketing-contexts/riemannlabs-context.md | torus URL + “**Proving the unprovable**” |
| LegalDen RL + QP offerings | “Machine-verified Lean 4 proofs” as **deliverable** (OK only if tied to registry artifacts) |
| SAIR package whitepaper / euler paper | **53 (41/12)** citation of Brockian law |
| launch-docs one-pager / demo-script | 41 theorems; demo-script “machine-verified proof” for crypto protocol |
| TrendRadar | 41 machine-verified on wrong product blurb |
| torus public site | dual verification / formally verified / sorry demos (this audit) |

---

## 8. Recommended partner-facing sentence (replace current hero)

> **Riemann Labs builds exploration tools and a verification-gated mathematics core.**  
> Interactive labs and historical thinkers help you see structure.  
> **Only declarations in the public registry with AXLE-verified, axiom-clean PROVED status are machine-checked.**  
> The Riemann Hypothesis, global Goldbach, and twin-prime infinitude remain **open / not claimed**; we publish scaffolding and conditionals with explicit badges.

That sentence is defensible. The current hero is not.

---

## 9. Bottom line

| Dimension | Score (honest) |
|-----------|----------------|
| Visual / lab product | Strong — keep |
| Verification company credibility | **Fail** until P0 |
| Alignment with tip registry | **Broken** (parallel 4.24 sorry registry) |
| RH / Goldbach honesty | **At risk** without permanent OPEN chrome |
| Readiness for IonQ/SAIR technical demo | **No** — use registry export + curated PROVED demos instead of raw torus verification pages |

**Audit artifact path:**  
`/Users/acutis/Projects/brockian-mathematics/docs/partner/torus-honesty-audit.md`

---

*Read-only audit. No git commit. Torus production code lives on Lovable/CDN; local SSOT is brockian-mathematics registry/observatory.*
