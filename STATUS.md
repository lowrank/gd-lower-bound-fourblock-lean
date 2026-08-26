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
- Exact chronological-envelope cutoff at every rank at least `200000000`,
  with direct rational square-root/log certification.
- A second complete cutoff scan and normalized floor at
  `criticalP = 1.8565576222695287`, ending in
  `GDLowerBound.FourBlock.exactEnvelopeMainTheorem`.
- Sharp defect-weighted and joint moment/defect finite rigidity budgets for
  the four-block route.
- Exact fixed-dilation sampling by consecutive backward blocks, including
  explicit normalized variation errors for endpoint defect and squared
  increment deviation.
- Finite upper expansion of every dilation defect into its middle-block
  mean deficit, endpoint defect, harmonic discretization error, and
  reciprocal-square remainder.
- Exact finite Fubini rearrangement of averaged middle blocks into a
  single rank sum with explicit harmonic occupancy weights and checked
  support bounds.
- Explicit interior occupancy estimates
  `|w2(n) - log (3/2)| <= 6/n` and
  `|w3(n) - log (4/3)| <= 8/n`, derived from exact floor/ceiling harmonic
  formulas and neighboring logarithmic integrals.
- Uniform truncated-boundary occupancy upper bounds and sign-safe weighted
  deficit estimates, including `18/n^2` and `24/n^2` interior errors.
- Exact common-range summation of both occupancy terms on `(2M,4N]`.
- Complete finite upper bound for the harmonically averaged schedule energy,
  with all endpoint, block, occupancy, and control errors named explicitly.
- Common-interval sharp and moment rigidity budgets, including the exact
  one-rank endpoint-defect shift charge.
- Normalized finite averaging composition: under the explicit mean-growth
  and finite-margin hypotheses, the averaged energy is below the robust
  local gap.
- Strict weighted-average extraction: the normalized estimate and the
  pointwise dichotomy force an actual sampled scale on the small-functional
  branch.
- Schedule-independent upper bounds for both normalized rigidity slacks,
  packaged with the remaining sampling error as `fourBlockWindowError`.
- Certified dyadic harmonic growth
  `H(M, 2^R M) >= (2/3)R - 1/M`, without evaluating a huge finite sum.
- Exact endpoint-mass-to-mean-growth bridge and the combined
  `finiteWindowEndpointGrowth_forces_small_scale` theorem.
- Window-length-independent `O(1/M)` bounds for the complete control
  allowance and both dilation-block reciprocal-square remainders.
- Scale-invariant dyadic endpoint-sampling bounds
  `(104 R + 2)/M` and `(288 R + 27)/M`, uniform over dilations `2,3,4`.
- Fixed-ratio occupancy boundary-band bounds
  `sum E₂ <= 6 + 9/M` and `sum E₃ <= 9 + 12/M`.
- A single complete dyadic schedule-error estimate, followed by the master
  schedule-independent bound `fourBlockWindowError_dyadic_le`.
- Archimedean depth/base-scale selection proving
  `exists_dyadicFourBlockWindow`: the full explicit finite-window error fits
  the certified strict margin for some dyadic window.

- Uniform tail selection `exists_uniform_dyadicFourBlockWindow`: every sufficiently
  deep dyadic window and every sufficiently large base scale fits the strict
  finite margin.
- Exact-`log 2` endpoint threshold and unconditional window dichotomy:
  each valid dyadic window either yields a later functional rank or has
  endpoint mass growth with coefficient exactly `massExponent = 0.8288`.
- Maximal-dyadic endpoint selection, bounded prefix comparison, short-tail
  propagation, and terminal factor-two propagation.
- A terminating well-founded global scan on the remaining rank gap, followed
  by the exact-envelope cutoff scan and bounded-rank branches.
- End-to-end no-`sorry` normalized floor at the exact exponent
  `exponent = 1.8288`, and
  `GDLowerBound.FourBlock.sharperMainTheorem` for every
  `1.8288 < p < 2`.

## Current milestone

The sharper four-block route is now end-to-end.  Lean proves
`sharperNormalizedLowerBound`, an unconditional normalized schedule
floor at the exact rational exponent
`exponent = 45720/25000 = 1.8288`.  Monotonicity in the target exponent
and the checked geometric/scaling reduction then give
`sharperMainTheorem` for every `1.8288 < p < 2`.

The global improvement comes from a maximal-dyadic scan.  On each valid
window, exact `log 2` bookkeeping gives an unconditional alternative:
either averaging produces a strictly later functional rank, or the endpoint
mass ratio grows with exponent `massExponent = 0.8288`.  The latter
endpoint lies within a factor two of the terminal rank and immediately yields
the normalized mass bound.  The former branch strictly increases the rank,
so well-founded recursion on `longCount h - k` terminates without
accumulating a per-window loss.  This is why the formal theorem retains the
exact `1.8288` exponent.

## Verification

- Full dependency-aware `lake build`: successful (8,829 jobs).
- Source scan: no `sorry`, `admit`, project `axiom`, `unsafe`,
  `implemented_by`, or `opaque` declarations.
- `#print axioms GDLowerBound.FourBlock.sharperMainTheorem`: only
  `propext`, `Classical.choice`, `Quot.sound`, and the explicitly audited
  `native_decide` kernels for exact rational/log certificate checks.
- Explicit edge-case coverage includes the empty chain, no long steps,
  repeated excess values, zero steps, and empty cutoff intervals.
