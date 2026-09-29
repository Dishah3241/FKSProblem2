# Comparator run, 2026-09-28

Comparator accepted `FKSProblem2.Palomar.target` under both NanoDa and Lean's default kernel.
The target is `questionAt3`: every simple graph on seven vertices, or its complement, has
an injective unit-distance representation in Euclidean three-space. The full FKS Problem 2
is not the submitted claim and remains marked open.

- **Tree:** worktree based on `30cf389bad8cf051c641b70c926b76dede0eac13`. The release
  edits to README and metadata were uncommitted during the run; all Lean files,
  `comparator.json`, the toolchain and dependency pins matched that commit. This record is
  added after the run. No release commit was made: the caller retains responsibility for
  committing, checking the final clean tree and landing it.
- **Library:** GraphDimension at `9acc3a712d477b79c3a699c160b20726309eb3c6`, matching
  both `lake-manifest.json` and the local dependency's `HEAD`.
- **Toolchain:** Lean `v4.35.0-rc2`; Mathlib at
  `065356127b1dc0016f66b7283ce0ce2c4055aa55` (`v4.35.0-rc2`).
- **Configuration:** `comparator.json`, target `FKSProblem2.Palomar.target`, permitted
  axioms `propext`, `Quot.sound`, `Classical.choice`, and `enable_nanoda: true`.
- **Sandbox:** disabled. The Comparator sandbox uses Linux `bwrap`, which is unavailable
  on this macOS host. As in rung 3's local run, these results check the mathematics, not
  isolation. Sandboxed Palomar preflight on the final release commit remains to be run.

## Command and result

From the project directory, after `scripts/worktree-setup.sh`:

```sh
PATH="$HOME/src/nanoda_lib/target/release:$HOME/.elan/bin:$PATH" \
  ~/.elan/bin/lake comparator --config comparator.json --inadvisably-no-sandbox
```

Exit status: `0`. The build and final kernel messages were:

```text
WARNING: Sandbox disabled, this run is not trustworthy.
Resolving dependencies
Building Challenge
⚠ [2424/2425] Replayed Challenge
warning: Challenge.lean:157:8: declaration uses `sorry`
Build completed successfully (2425 jobs).
Building Solution
Build completed successfully (2836 jobs).
Running nanoda kernel on solution
nanoda kernel accepts the solution
Running Lean default kernel on solution
Lean default kernel accepts the solution
Your solution is okay!
```

The two long export lines are omitted above; both name `FKSProblem2.Palomar.target`.
The warning in `Challenge.lean` is its deliberate advertised hole. The solution has none.

## Target axiom check

A scratch file importing `Solution` printed the axioms of the Palomar target and the
frozen statement's proof. It was checked with the package's implicit-variable settings:

```sh
~/.elan/bin/lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false tmp/ReleaseAxioms.lean
```

```text
'FKSProblem2.Palomar.target' depends on axioms: [propext, Classical.choice, Quot.sound]
'FKSProblem2.StatementA.questionAt3.proof' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Local blueprint check

The worktree did not contain the generated `blueprint/lean_decls` file, so the first
`leanblueprint checkdecls` invocation failed. Following the workspace's documented local
fallback, the names were extracted from the current LaTeX source, skipping comments and
handling multiline lists:

```sh
python3 - <<'PY'
from pathlib import Path
import re
source = Path('blueprint/src/content.tex').read_text()
source = '\n'.join(line.split('%', 1)[0] for line in source.splitlines())
names = [name.strip()
         for group in re.findall(r'\\lean\{([^}]*)\}', source, re.S)
         for name in group.split(',')]
assert len(names) == 40
assert all(re.fullmatch(r'[A-Za-z0-9_.]+', name) for name in names)
Path('blueprint/lean_decls').write_text('\n'.join(names) + '\n')
PY
PATH="$HOME/.elan/bin:$PATH" leanblueprint checkdecls
```

The check exited `0` with no missing declarations. The generated list is not a release
source file and was removed afterwards. This validates the 40 declaration references;
it is not a PDF or web-rendering check. CI runs `leanblueprint all` before `checkdecls`.
