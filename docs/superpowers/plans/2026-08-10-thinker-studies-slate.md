# Athenaeum Phase 4 — The Thinker Studies (slate)

**Directive (Chris):** "maybe even a 'lab' per thinker. that is their work and thinking, an education tool and a wow factor."

## What a Study is
A per-thinker educational journey at `/athenaeum/:slug/study` — the thinker's work AND thinking, taught. Distinct from the 50 labs (phenomenon-centered) — a Study is person-centered pedagogy:
- **Surface**: their story as one cinematic scene (stills + ?forceStills=1) — the life arc from the premium profile, animated around their signature mathematics.
- **Explore — "The Lessons"**: a guided teaching sequence (reuse GuidedTour stepper + ChallengeCard checkpoints) through their signature computation, REUSING existing kernels wherever the thinker already runs in the 50 labs. Each lesson: one idea, one interactive, one checkpoint question with verifiable answer.
- **Rigor — "Their ledger"**: the claims about THEIR results, scoped from the labs' ledgers + their relatedCorpusModules; registers as everywhere (PROVED verbatim-only, OPEN stays OPEN).
- Ratchets apply (permalinks, export, a11y, PerfMeter, RelatedLabs rail → their appearance labs + fellow thinkers).

## Kernel reuse map (no new heavy compute for batch 1)
| Study | Kernels/labs reused | Lessons spine |
|---|---|---|
| Euler | pentagonal + franklin + zeta (Euler product) | Basel → product formula → pentagonal theorem (conj. 1741 → proof 1750) → Franklin's later involution |
| Galois | galois (whyfive derived series) + d5-characters | equations→symmetries → groups → derived series stalls at A₅ → why 5 is special |
| Riemann | line-walker + orchestra (explicit formula) + rs-anatomy | one 8-page paper → continue ζ → functional equation → zeros→primes → the Hypothesis stays OPEN |
| Shannon | entropy + galton (source statistics) | surprise → H = −Σp log p → source coding limit → channel capacity (story-level) |
| Erdős | erdos-szekeres + cauchy-davenport (EGZ) + random-walk (probabilistic method flavor) | monotone subsequences → zero-sum EGZ → the probabilistic method idea |

Batch 2+ candidates: Gauss (reciprocity + pi-li-race), Weyl (equidistribution + schrodinger), Penrose (penrose), Pólya (random-walk), Hardy–Littlewood joint study (singular-series + twin-constant), Kesten (percolation), Fermat (wilson + reciprocity), de Bruijn (penrose pentagrid + formal-proof story), Hales (spheres), Franklin (franklin deep).

## Execution
One build message per batch of 5 (sequential, verify each: tests + typecheck + browser 3 depths + a Study's checkpoint answers verified compute-first). Studies rail on thinker pages + hall cards. Batch 1: Euler, Galois, Riemann, Shannon, Erdős.

**Status:** slate written 2026-08-10; batch 1 queued behind Phase 3 (Conversations).
