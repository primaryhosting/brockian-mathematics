# Understanding seL4 — Proof Structure and an Honest Contribution Map

*Companion to `CAPABILITY_BRIEF.md`. Purpose: show we understand what seL4's verification actually is, and pinpoint where AI-assisted, independently-gated proving genuinely helps — and where it does not.*

## 1. What seL4 is

seL4 is a capability-based **microkernel** (~9–10k lines of C plus a few hundred lines of assembly), and it is the most comprehensively verified general-purpose OS kernel in existence. "Verified" here is not a single theorem; it is a **stack of refinement and security proofs** in **Isabelle/HOL**, developed by NICTA → Data61 → Proofcraft/Kry10 and collaborators (Klein, Murray, Sewell, Andronick, Heiser, et al.) over roughly **15 years and on the order of 20–30 person-years**, comprising on the order of **hundreds of thousands to ~1M lines of proof** across its components.

## 2. The proof stack (this is the part that matters)

seL4's assurance is a chain of **refinements**, each a forward simulation, plus **security theorems** proved at the top and **transported down**:

```
   Access-control / security model  ── integrity, confidentiality (noninterference), authority confinement
            │  (proved on the abstract spec)
   Abstract specification            (Isabelle/HOL; "what the kernel does")
            │  refinement  (forward simulation, a coupling relation + the kernel invariant)
   Executable specification          (derived from an executable Haskell prototype)
            │  refinement
   C implementation                  (given a formal C semantics via a verified C parser)
            │  translation validation (decompilation + graph refinement + SMT)
   Compiled ARM/RISC-V binary        (the machine code that actually runs)
```

Three things are worth internalizing because they define where help is possible:

- **The kernel invariant is enormous.** Functional-correctness refinement is carried by an invariant with *thousands* of conjuncts that must be shown preserved by **every** kernel operation. Most of the proof *effort* is maintaining and re-establishing this invariant across ~300 operations and their case splits — mechanical, voluminous, and brutal to maintain when code changes.
- **Security is proved once, then transported.** Integrity (Sewell et al.), confidentiality/information-flow (Murray et al., S&P 2013), and authority confinement are proved against the *abstract* model; refinement carries them to C. This is exactly the `safety_transported` pattern we mechanized in `Brockian.HighAssurance.Refinement`.
- **Binary correctness is a separate, SMT-heavy leg.** Translation validation (Sewell et al., PLDI 2013) proves the *compiled binary* refines the C, via decompilation into a logic and graph-based refinement discharged largely by **SMT** — a different toolchain (HOL4 + solvers) from the C-level Isabelle proof.

The headline cost figure — a proof-to-code ratio on the order of **~20:1** — is not an accident of laziness. It is the price of the invariant bookkeeping, the refinement obligations, and the per-port re-verification.

## 3. Why "re-prove seL4" is the wrong goal

- It is **already fully proven**, in Isabelle. Reproducing it in Lean would be years of effort for **zero new assurance**.
- The *creative* content — the abstract spec, the invariant design, the refinement architecture — is done and is deep human work. An AI adds nothing by re-deriving it.

So the question is not "can we prove seL4" but **"where does AI-assisted, independently-gated proving reduce the ~20:1 cost or extend the guarantee?"**

## 4. Contribution map — where this pipeline plugs in (honest)

| seL4 activity | Cost driver | Where AI + gate helps | Confidence |
|---|---|---|---|
| **Invariant preservation** across operations | Thousands of conjuncts × ~300 ops; huge, mechanical | Generate/repair the per-operation preservation proofs; the *gate* re-checks each independently so AI output is trusted, not assumed | High — this is the bulk, and it is exactly the "bounded but enormous" regime AI is strong at |
| **Proof maintenance** after a code change | A small C change breaks many proofs | AI-assisted proof repair, gate-verified; provenance tracks what changed | High |
| **New-platform ports** (RISC-V, new ARM/x86) | Each port re-does refinement + binary translation validation | Accelerate the re-verification; the SMT-backed binary leg is a natural fit for an SMT gate backend | Medium–High |
| **Binary translation validation** | Decompilation + graph refinement + SMT | Our Phase-1 multi-prover gate (add Z3/CVC5) targets exactly this style of obligation | Medium |
| **New properties on seL4-*based* systems** (HACMS pattern) | Above-kernel components need their own proofs | Verify new components/properties with the pipeline; the security-core work in `Brockian.HighAssurance.*` is a template | High |
| **AI-contributed proofs into the l4v corpus** | Trust: can you accept a machine-written proof? | The gate (independent re-verification + axiom audit + statement-fidelity + empty-stub/circularity detection) is the *acceptance criterion* | High — this is the differentiator |
| Abstract spec / invariant *design* | Deep human insight | **Not** an AI contribution. AI assists proofs, not the specification of "correct." | — |

## 5. What we bring that is not "another prover"

1. **An independent verification leg.** Our gate re-checks a proof with a *second* toolchain and audits its axioms — a machine-written proof only counts if an independent verifier agrees and it uses no `native_decide`/`sorryAx`. For AI-generated contributions this is the acceptance gate.
2. **A statement-fidelity + honesty discipline.** Our recent audit of 114 AI "proofs" of open problems found **zero unsound proofs but nine empty stubs scored as passing** and pervasive mislabeling of conditional/circular results. Any high-assurance org putting AI in the loop needs precisely this failure taxonomy and the guard for it.
3. **A demonstrated ability to mechanize the seL4 property classes** — integrity, confidentiality (2-domain and full-lattice), separation, confinement, and refinement — see `CAPABILITY_BRIEF.md` §2, all independently verified.

## 6. The honest boundary

- **We do not replace Isabelle, SAW, or the l4v proofs.** We orchestrate and independently gate. A real engagement bridges our gate to Isabelle/HOL and SMT backends (Phase 1).
- **We do not write the spec or the invariant.** Those remain human. AI attacks the *proof*, not the *definition of correct*.
- **A verified kernel *implementation* is a multi-year systems effort.** We can build the verified *mathematics* and accelerate the *proof engineering*; we cannot conjure a running verified kernel overnight, and Brockian number theory is the wrong tool for the implementation (it is the right *training* for the security proofs — the no-go/confinement invariants are the same mathematical shape).

## 7. References (for the reader who wants ground truth)

- Klein et al., *seL4: Formal Verification of an OS Kernel*, SOSP 2009.
- Klein et al., *Comprehensive Formal Verification of an OS Microkernel*, ACM TOCS 2014.
- Murray et al., *seL4: from General Purpose to a Proof of Information Flow Enforcement*, IEEE S&P 2013.
- Sewell, Myreen, Klein, *Translation Validation for a Verified OS Kernel*, PLDI 2013.
- The `l4v` proof repository (seL4 Foundation).

*Figures (line counts, person-years, ratios) are the widely-cited approximate values; treat them as order-of-magnitude, not exact, and defer to the seL4 Foundation's current numbers.*
