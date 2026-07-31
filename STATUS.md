# Formalization status

## Objective

Formalize the finite-horizon lower bound from the accompanying manuscript in Lean 4/mathlib,
including the construction of a smooth convex hard instance, the scalar
schedule analysis, and the final scaling argument.

## Acceptance criteria

- `lake build` succeeds from a clean checkout.
- No `sorry`, `admit`, or project-defined axioms remain.
- The final theorem has the same quantifier order and conclusions as
  `thm:main` in the manuscript.
- `#print axioms` reports only ordinary mathlib foundations.
- Edge cases include zero schedules, no long steps, the empty chain, repeated
  excess values, and empty cutoff ranges.

## Completed

- M0: pinned Lean 4/mathlib project (`v4.32.1`).
- Exact finite-horizon statement recorded as `GDLowerBound.mainStatement`.
- Core interfaces for smooth convex objectives and GD trajectories.
- Schedule decomposition, deterministic excess ranking, chronological chains,
  tail masses, and the finite lower-bound functional.
- Convex projection and projection-envelope kernel.
- Full geometric realization of every chain, including the explicit GD
  trajectory, saturated amplitudes, empty chain, and functional attainment in
  dimension at most `T+1`.
- Labeled matching extremum, total-weight estimate, budget equalization, and
  the order-independent endpoint bound.
- Adjacent-rank identities, density bound, one-step Lyapunov inequality,
  boundary propagation, and bounded-rank prefix estimate.
- Exact `L,R` scaling and the reductions from a normalized functional floor to
  the theorem statement.
- Complete finite cutoff scan, normalized schedule floor, and
  `GDLowerBound.mainTheorem : mainStatement`.

## Current milestone

Complete and audited.

## Verification

- Full dependency-aware `lake build`: 8,688 jobs, successful.
- Source scan: no `sorry`, `admit`, project `axiom`, `unsafe`,
  `implemented_by`, or `opaque` declarations.
- `#print axioms GDLowerBound.mainTheorem`: only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Explicit edge-case coverage includes the empty chain, no long steps,
  repeated excess values, zero steps, and empty cutoff intervals.
