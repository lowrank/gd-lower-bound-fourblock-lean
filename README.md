# Lean 4 verification of a gradient-descent lower bound

This repository formalizes a finite-horizon lower bound for gradient descent on
smooth convex functions. For every exponent
`sqrt (2 + sqrt 3) < p < 2` and every nonnegative step-size schedule of length
`T`, the main theorem constructs a smooth convex objective and a gradient
descent trajectory whose final objective gap is at least a positive constant
times `L * R^2 * (T + 1)^(-p)`. The dimension of the construction is at most
`T + 1`.

The Lean development accompanies a manuscript maintained separately. The
labels in `TRACEABILITY.md` record the correspondence between that manuscript
and the formal declarations.

## Build

```sh
lake update
lake exe cache get
lake build
```

The main result is `GDLowerBound.mainTheorem : mainStatement`. To repeat the
kernel audit, run

```sh
lake env lean AxiomAudit.lean
rg -n '\b(sorry|admit)\b|^\s*axiom\b' . \
  --glob '*.lean' --glob '!**/.lake/**'
```

The development contains no `sorry`, `admit`, or project-defined axioms.
See `TRACEABILITY.md` for the correspondence between manuscript labels and
Lean declarations, and `STATUS.md` for verification details.
