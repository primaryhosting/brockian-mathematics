# The Athenaeum — Thinkers Program

**Directive (Chris, 2026-08-10):** Many visitors will come specifically to see and chat with the thinkers. We need: all the work from all the thinkers, their bios and works; the ability to chat with the expert of each domain; the ability to work problems with the chat from their perspective. Expanded same day: "full bios and books and papers, and maybe even a 'lab' per thinker — their work and thinking, an education tool and a wow factor."

## Honesty contract extensions (this program's register)

1. **Persona ≠ person.** Every chat surface states plainly it is an AI speaking *from the perspective of* the thinker, never an impersonation. The teaser card carries this framing before the chat even exists.
2. **Bios contain no invented facts.** Documented facts only; legendary anecdotes labeled as legend (Galois's final night, Gauss's schoolroom sum); uncertain dates marked approximate.
3. **Works lists are "Selected works," never claimed exhaustive** (Euler alone has ~850 papers; the Opera Omnia problem). Books/papers get year + one-line; landmark-first ordering.
4. **Every "appearance" is real** — derived by scanning the labs' actual attributions; integrity test resolves each appearance's lab slug against SITE_REGISTRY and each corpus module verbatim against /verified-registry.json.

## The phases

- **Phase 1 — The Hall** (IN FLIGHT, msg umsg_01kznybnt8f0abzyr433m6j415): `/athenaeum` gallery + `/athenaeum/:slug` pages. Roster derived from real attributions across the 50 labs + Observatory (~40+ thinkers). Deterministic geometric portrait motifs from each thinker's own mathematics (no fake photographs). Appearances = "their mathematics, running live" link cards into the labs. Supersedes/absorbs the old `/labs/ask` surface.
- **Phase 2 — Scholarly depth:** full sectioned bios (Life / The Mathematics / Legacy, ~600–900 words, documented-facts-only), Selected Works lists (books + landmark papers, year + venue + one-liner), timeline strip. This upgrades Phase 1's ~120-word bios in place.
- **Phase 3 — The Conversations:** per-thinker persona chat via Lovable Cloud AI (server-side key, no client secrets). System prompt grounded in the thinker's documented results, era, and the site's labs/corpus claims about their work; honesty framing pinned in the UI; chat can cite labs and registry theorems. Rate-limited, graceful empty/error states.
- **Phase 4 — The Thinker Studies (the wow factor):** one educational lab per thinker — their work and thinking as an interactive experience. DepthShell pattern (Surface = their story as one cinematic scene; Explore = their signature computation live; Rigor = claims incl. corpus PROVED where the registry genuinely formalizes their result). REUSE existing kernels wherever a thinker already runs in the 50 (Euler↔pentagonal, Galois↔why-five, Penrose↔penrose, Shannon↔entropy, Franklin↔franklin, Weyl↔equidistribution, Kesten↔percolation, Pólya↔random-walk, Zeckendorf↔zeckendorf, Wilson↔wilson, Collatz↔collatz, …); new mini-kernel tasks only for thinkers without one. Rolling batches of ~5, flagship thinkers first (Euler, Gauss, Riemann, Galois, Erdős, Shannon, Penrose, Weyl, Hardy–Littlewood, Noether-class as attested). All ten ratchets R1–R10 apply from Study 1.
- **Phase 5 — The Workbench:** chat + problem-working — bring a problem, work it from the thinker's perspective; chat links into labs/Studies and can reference specific claims. (Design details after Phase 3 ships and its real behavior is observed.)

**Execution:** one Lovable build message per phase-step, sequential, verify (full vitest + typecheck + 0 console errors + browser eyes) before the next; publish only on explicit go. Same controller-polling pattern as the 50-lab program.

**Status:** Phase 1 building (2026-08-10).
