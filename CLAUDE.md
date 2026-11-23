# CLAUDE.md

Monorepo of independent Lean 4 libraries. See README.md for the human-facing overview.

## Layout and commands

- Each library is its own Lake package in `packages/<name>/` with a `lakefile.toml`.
  There is no root lakefile; run `lake` inside a package directory.
- `lean-toolchain` at the root is the single source of truth; `packages/*/lean-toolchain` are
  symlinks to it. Bump the version there only.
- `scripts/check.sh [pkg...]` — `lake build --wfail` + `lake test` for every (or the named) package.
  This is what CI runs; run it before committing.
- `scripts/new-package.sh <kebab-name> <ModuleName>` — scaffold a new package.
- One package per domain, split into modules inside. Data structures all live in
  `packages/collections` as `Collections/<Name>.lean` (+ `Collections/<Name>/*.lean`), in
  `namespace Collections`, with tests in `CollectionsTest/<Name>/*.lean`; add the import to
  `Collections.lean` and the test modules to `CollectionsTest.lean`. Scaffold a new package only
  for a new domain.
- CI (`.github/workflows/ci.yml`) auto-discovers packages; no edits needed when adding one.

## Conventions

- Library files start with `module`; public API goes in `@[expose] public section`.
  Inside an exposed section, helpers referenced by public defs must themselves be public
  (`private` defs are not accessible from exposed public definitions).
- `autoImplicit = false`. `linter.missingDocs = true` for library targets (not tests): every
  public def/structure/field/constructor needs a docstring. Theorems and instances don't.
- Builds must be warning-free (`--wfail`), including unused simp args and deprecations.
- Keep IO thin: pair every `IO` function with a pure core that takes randomness/time as
  arguments; test and prove things about the pure core.
- Do not import `Lean` (the compiler package) from library code, not even via `meta import`:
  every executable that imports the library then links all of Lean (~7 MB → ~120 MB).
  Write syntax extensions as `macro`s, which only need `Init`.
- Tests: `<Lib>Test.lean` is the `testDriver` exe; `<Lib>Test/*.lean` is a `lean_lib` named
  `tests` with `globs = ["<Lib>Test.+"]`. Put pure checks in `#guard` (checked at build time) and
  randomized/IO checks in the runtime suites. Test vectors should come from specs or be
  cross-checked with an independent implementation (e.g. Python), never invented.
- Lines ≤ 100 characters.

## Lean 4.36 gotchas seen so far

- `bv_decide` (needs `import Std.Tactic.BVDecide`) is the go-to for UInt/BitVec facts. Unfold
  definitions with `simp only [...]` first; `dsimp only [f]` handles `let`/`have` bodies that
  `unfold` + `split` can't see through.
- For literals mixed with shifts, the binop elaborator may pick `Nat`; add `(… : UInt64)`.
- `Except` has no `DecidableEq`, so `#guard parse s = .error e` fails; compare via `Option`.
- Derived `Ord` instances were awkward to unfold in proofs; write `Ord` by hand when you need to
  reason about it.
- `Vector` append indexing doesn't simp well; write vectors as explicit `#v[...]` literals.

## Toolchain in cloud sessions

The `lean-playground` cloud environment allows `release.lean-lang.org` (toolchain manifests) and
`releases.lean-lang.org` (archives), and its setup script installs elan plus the pinned toolchain,
so `lake` works out of the box. In an environment without those hosts, elan's install fails with
a proxy 403; add both hosts to the environment rather than working around it.
