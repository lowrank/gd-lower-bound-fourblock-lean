# A sharper Lean 4 lower bound for gradient descent



**NOTE**: We are aware there are better bounds available now:

- ``sqrt(3)``: https://chungentsai.github.io/gd-lower-bounds.html
- ``1.635``: arXiv:2609.02855
- ``1.450``: arXiv:2609.04032

This repository records and proves a finite-horizon lower bound for gradient descent with
an arbitrary predetermined nonnegative step-size schedule. Its new four-block
theorem lowers the formally verified exponent threshold from the original
Ma--Chen value

```text
sqrt (2 + sqrt 3) = 1.9318516525...
```

to the exact rational Lean target

```text
45720 / 25000 = 1.8288.
```


More precisely, `GDLowerBound.FourBlock.sharperMainTheorem` proves that for
every `1.8288 < p < 2` there is a constant `c > 0` such that, for every
horizon `T >= 1`, every `L,R > 0`, and every nonnegative schedule of length
`T`, one can construct an `L`-smooth convex objective and a
gradient-descent trajectory satisfying

```text
f(x_T) - f_* >= c * L * R^2 * (T + 1)^(-p).
```

The construction has dimension between `1` and `T + 1` and starts at
distance exactly `R` from a minimizer. The stronger normalized statement
`sharperNormalizedLowerBound` holds at the exact exponent `1.8288` itself.

## Provenance: the Ma--Chen formalization is the base

This development is built directly on the public repository
[`jianhaoma/gd-lower-bound-lean`](https://github.com/jianhaoma/gd-lower-bound-lean)
at commit
[`e41ce4b`](https://github.com/jianhaoma/gd-lower-bound-lean/commit/e41ce4b).
That repository formalizes Jianhao Ma and Yuxin Chen's paper
[**A lower bound for stepsize-based acceleration of gradient descent**](https://arxiv.org/abs/2608.10418)
(arXiv:2608.10418, 2026) and proves the original threshold
`sqrt (2 + sqrt 3)`.

The inherited code supplies the schedule and rank infrastructure, matching
theory, geometric realization of the schedule functional by a smooth convex
instance, scaling argument, and the original public theorem
`GDLowerBound.mainTheorem`. Those components remain the foundation of the
sharper result. The new work extends them; it does not replace or reimplement
the Ma--Chen formalization.

## What is newly added

The principal addition is the no-`sorry` development under
`GDLowerBound/FourBlock/`, together with its certificate-generation scripts
and integration into `GDLowerBound.lean`. It adds:

- the exact exponential equalization envelope and chronological outside-in
  matching reductions;
- four-block reciprocal-mass coordinates and a robust local energy gap;
- rational central, side, tail, square-root, and logarithm certificate
  checkers, with generated certificate data checked inside Lean;
- sharp moment and drift rigidity budgets for schedules;
- fixed-dilation harmonic sampling and explicit finite sampling errors;
- exact middle-block occupancy identities and signed weighted-error bounds;
- a uniform finite-window four-block dichotomy with every boundary and
  discretization error retained;
- exact `log 2` bookkeeping for dyadic endpoint growth;
- maximal-dyadic terminal and short-window propagation; and
- a terminating global scan, formalized by well-founded recursion on the
  remaining rank gap, that does not accumulate a loss at every successful
  functional branch.

The intermediate exact-envelope route also gives the fully formal theorem
`GDLowerBound.FourBlock.exactEnvelopeMainTheorem` for every
`1.8565576222695287 < p < 2`.

The accompanying analytic manuscript optimizes the same four-block mechanism
to `1.82844`. That decimal is not claimed as a Lean theorem here:
`1.8288` was deliberately selected as a nearby rational target with enough
slack for practical exact certificate checking.

## Proof architecture

The improvement comes from retaining information that the original scalar
matching compression discards. Exact equalization first removes a quadratic
edge majorant. Four-block matching then keeps adjacent reciprocal-mass
defects, while rigidity identities convert excessive rank growth into an
upper bound for their averaged energy. Directed rational certificate trees
establish a strictly larger pointwise local energy gap.

The global step uses a maximal dyadic window. Every sufficiently large window
either produces a strictly later rank with a direct functional contribution,
or its endpoint mass ratio already obeys the `0.8288` growth law. The latter
endpoint is within a fixed factor of the terminal rank. In the former case the
rank strictly increases, so recursion on `longCount h - k` terminates.
Combining this scan with the inherited geometric realization and scaling
theorem yields the stated exponent `1 + 0.8288 = 1.8288`.

## Repository map

- `GDLowerBound/` outside `FourBlock/`: inherited Ma--Chen formalization.
- `GDLowerBound/FourBlock/`: new exact-envelope, four-block, finite-window,
  certificate, propagation, and global-scan modules.
- `GDLowerBound/FourBlock/SharperNormalized.lean`: exact normalized floor and
  final sharper theorem.
- `scripts/`: reproducible generators and experiments for the rational Lean
  certificate data. Search is kept outside the trusted proof; Lean checks the
  emitted data.
- `AxiomAudit.lean`: theorem and dependency audit.
- `TRACEABILITY.md`: manuscript-to-Lean theorem correspondence.
- `STATUS.md`: detailed completion and verification record.

## Build and audit

The project uses Lean `v4.32.1` and the matching Mathlib release.

```sh
lake update
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

To scan the project sources for proof placeholders or declarations outside
the intended trusted base, run:

```sh
rg -n --glob '*.lean' \
  '\b(sorry|admit|axiom|unsafe|implemented_by|opaque)\b' .
rg -n --glob '*.lean' 'sorryAx' .
```

The proof blueprint can be generated locally with

```sh
leanblueprint all
```

This compiles the printable PDF and web version, builds the Lean project, and
checks every Lean declaration referenced by the blueprint.  Generated files
are written under `blueprint/print/` and `blueprint/web/`.

The development contains no `sorry`, `admit`, project `axiom`, `unsafe`,
`implemented_by`, or `opaque` declarations. `#print axioms` for the
sharper theorem reports Lean's ordinary logical foundations together with
explicitly audited `native_decide` soundness dependencies for the finite
rational certificate computations. See `STATUS.md` for the recorded audit
and `TRACEABILITY.md` for the proof map.
