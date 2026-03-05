# ProofGolf

A `#golf` command for Lean 4 that measures proof complexity.

```lean
#golf example (P : Prop) : P ∨ ¬P := by exact Classical.em P
-- Golf: 18 chars | term: 5 nodes | pp: 23 chars | axioms: 3 (Classical.choice, propext, Quot.sound)
```

## Metrics

| Metric | Description |
|--------|-------------|
| **chars** | Non-whitespace characters in the proof body. `;` is free (equivalent to newline), `<;>` counts. |
| **term** | Node count of the elaborated proof term (`Expr.sizeWithoutSharing`). |
| **pp** | Character count of the pretty-printed proof term. |
| **axioms** | Foundational axioms used transitively (same as `#print axioms`). |

Works for `example`, `theorem`, and `def`.

## Setup

Add to your `lakefile.toml`:

```toml
[[require]]
name = "ProofGolf"
git = "https://github.com/FordUniver/ProofGolf"
rev = "main"
```

Then run `lake update ProofGolf` and add `import ProofGolf` at the top of any file where you want to use it.
