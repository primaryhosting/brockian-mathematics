# The Formal Atlas — Method

> Canonical source for the `/atlas/method` page on torus.riemannlab.com.
> Companion to the approved design: `docs/superpowers/specs/2026-08-26-formal-atlas-design.md`.
> Epistemic framework: Christopher Brock, *Mathematics in the Age of Mechanical
> Reproduction: Trace, cult, and what verification cannot certify* (20 Aug 2026),
> [PDF in the public repo](https://github.com/primaryhosting/euler-sair-stage2/blob/main/CONTRIBUTION-PACK/1-PAPER/mathematics-in-the-age-of-mechanical-reproduction.pdf).

---

## What the Atlas asserts — and what it doesn't

The Formal Atlas is a living map of machine-verified mathematics: one page per
mathematical statement (a **concept**), with every machine-checked verification of
it — Lean/Mathlib, Isabelle/AFP, Coq/Rocq, Metamath, HOL Light, Mizar, the
Brockian corpus — attached to that page with full provenance.

Machine proof is now abundant, and abundance separates things that mathematics
long treated as traveling together. A kernel can accept a proof no human has
understood; a library can hold a hundred thousand theorems no map connects; two
libraries can each "verify Dirichlet's theorem" while formalizing statements of
different strength. Following *Mechanical Reproduction*, the Atlas refuses to run
these apart-things together. Every number and badge on the site answers exactly
one of three separated questions:

| Layer | The relation | What the Atlas does with it |
|---|---|---|
| **Correctness** | formal statement → proof | **Reported, never re-adjudicated.** Each verification card states the *source library's own* checked status, with a link to its native page. The Atlas re-checks nothing and never claims more than the source asserts. |
| **Statement fidelity** | informal concept → formal statement | **Tiered, with evidence.** Whether a library's formal statement actually formalizes *this* concept is a fallible claim. Every alignment carries a visible confidence tier and a recorded evidence trail. |
| **Reactivability** | artifact → competent reader | **Served.** A concept page reconnects the formal deposits to the informal statement, the subject territory, and the cross-library picture — a reactivation device, not just an index. |

Correctness is the only layer a kernel settles. The other two are where maps of
mathematics have historically overclaimed, so they are where the Atlas spends its
discipline.

## The tier system

Every concept–statement link carries one of three tiers, rendered wherever the
alignment appears:

- **CURATED** — human-sourced. Seeded from Freek Wiedijk's *Formalizing 100
  Theorems* tracking and from hand-curated additions, maintained as versioned
  files (`concepts/*.yaml`) whose git history is the provenance record.
- **ALIGNED** — high-confidence, with recorded evidence: what matched it, who or
  what confirmed it, and (for machine matches) the model and prompt hash.
- **CANDIDATE** — machine-proposed, unconfirmed. Visibly marked, and **never
  counted in any headline number**.

Three rules govern the tiers:

1. **Headline counts include only CURATED + ALIGNED.** A concept "verified in six
   systems" links each of the six to its native source; if we can't show it, we
   don't count it.
2. **Tier down when in doubt.** Where two libraries formalize different strengths
   of a theorem — a common and mathematically meaningful situation — the
   alignment evidence says so, and the weaker reading wins.
3. **No silent equivalences.** Cross-library equivalence is asserted only by an
   alignment row with a tier and evidence, never by name similarity or page
   adjacency.

This is the statement-fidelity protocol of *Mechanical Reproduction* applied at
atlas scale: verification guards every arrow except the first one — the arrow
from the problem to its formalization — so that arrow gets an explicit,
inspectable contract instead of a vibe.

## Provenance: measured, dated, versioned

- **Every displayed number is measured by a harvester, never estimated.** Library
  counts are written by the harvest run that observed them and displayed
  verbatim, with as-of timestamps.
- **Every page cites its edition.** Weekly editions are cut as versioned dataset
  releases; each page footer names the edition and per-library harvest
  timestamps it reflects. The Atlas you cite is reproducible: the edition is a
  download, not a memory.
- **Nothing is silently deleted.** Statements that disappear upstream are marked
  retired, not erased; a failed harvest leaves the previous data standing under
  its old timestamp rather than partially overwriting. The record only grows.
- **Coverage honesty over apparent completeness.** A library whose deep harvest
  isn't built yet appears with exactly what has been harvested and an explicit
  "statement-level harvest: not yet built" notice — stated gaps, not decorated
  ones.

## The frontier

The Atlas maps what is verified; the **frontier** maps what is not — famous
theorems with zero machine verifications anywhere, and concepts formalized in
some systems but not others. Deciding which unproved statements *matter* is the
faculty Turing bracketed in a footnote and every proof pipeline inherits
unexamined. The Atlas makes that selection explicit and public: the frontier is
seeded from the Wiedijk 100 and the Riemann Lab targets board, and every
frontier entry names its seed source.

## The Brockian layer

The Brockian corpus appears as one library among peers — same schema, same
tiers, same harvest discipline — highlighted where it extends the world corpus.
Its public authority is the prover-owned sanitized registry
(`/verified-registry.json`); the Atlas reads that export and nothing else.
Attestation status (AXLE-kernel-verified) is stated as exactly that, in the same
per-library plain speech used for every other system.

## Why this is worth doing carefully

A map of all verified mathematics is only valuable if its claims are cheaper to
check than to doubt. The Atlas's bet, made explicit in *Mechanical
Reproduction*, is that mechanical reproduction of proof doesn't diminish
mathematics — it relocates the scarce thing. When kernels are abundant, what is
scarce is fidelity (is this *the* theorem?), reactivability (can a reader
recover what this deposit knows?), and honest selection (what should be proved
next?). Those are the three services the Atlas exists to provide, and every
design rule above is one of them made mechanical.

---

*Corrections and challenges are welcome — an alignment you can refute is a
CANDIDATE we mis-tiered, and the evidence trail exists so you can show us.*
