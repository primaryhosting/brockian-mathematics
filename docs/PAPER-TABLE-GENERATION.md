# Paper Table Generation

`scripts/gen_paper_theorem_table.py` generates the Markdown theorem table used by the paper appendix.

Default command:

```sh
python3 scripts/gen_paper_theorem_table.py
```

Input:

- `registry/theorems.json`

Output:

- `paper/theorem_table.md`

The default output includes claim-bearing rows only: `PROVED`, `CONDITIONAL`, and `CONJECTURE`. This keeps the appendix focused on mathematical claims rather than API definitions. To include definitions for a full API appendix, run:

```sh
python3 scripts/gen_paper_theorem_table.py --include-definitions
```

Each row records:

- declaration name
- register
- Lean kind
- module
- AXLE environment and verdict
- axiom-clean status
- clipped provenance note

The script is read-only with respect to the registry. It writes only `paper/theorem_table.md` unless an explicit `--output` path is passed.
