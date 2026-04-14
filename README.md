# proof-remover

`proof-remover` takes a Lean file, keeps the last theorem-like declaration by default, keeps the declarations needed for the retained targets, and rewrites retained theorem/lemma/instance proofs to `sorry`.

The repo currently includes one example input file:

- `test-files/heisenberg.lean`

## Usage

Build:

```bash
lake build
```

Run:

```bash
lake exe proof-remover path/to/input.lean --out path/to/output.lean
```

Keep specific theorem-like declarations instead of the default last one:

```bash
lake exe proof-remover path/to/input.lean --keep Namespace.foo --keep Namespace.bar --out path/to/output.lean
```

Keep only the definitions needed for the retained target, without emitting the target theorem itself:

```bash
lake exe proof-remover path/to/input.lean --defs-only --out path/to/output.lean
```

Skip verification:

```bash
lake exe proof-remover path/to/input.lean --out path/to/output.lean --no-verify
```

## Example

```bash
lake exe proof-remover test-files/heisenberg.lean --out /tmp/heisenberg.out.lean
```

## Notes

- Retained `def` bodies are kept.
- `--keep` expects declaration names; for namespaced declarations, use the full name.
- `--defs-only` still uses the retained theorem target to compute dependencies, but omits that target from the emitted file.
- Verification is enabled by default.
