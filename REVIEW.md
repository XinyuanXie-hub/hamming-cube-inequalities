# Stage 1 review: Hamming cube II

Source: https://arxiv.org/pdf/2602.20462v1 (24 February 2026), pages 1–2.
The full proposed formal statement is in `Challenge.lean`; the three fully
qualified targets are in `comparator.json`. No solution proof has been started.

## Source correspondence

Common definitions: `Cube n` represents the binary cube, `flip` changes exactly
one coordinate, `avg` is the uniform expectation, and `density` is normalized
cardinality. Finite subsets suffice because the cube is finite. All three
statements retain the paper's ambient hypothesis `n ≥ 1`.

- Theorem 1.1, page 1, (1.1): the local `h` counts outgoing coordinate flips
  inside A and is zero outside A. `Real.logb 2` is base-two logarithm. Lean's
  total inverse and logarithm make the right-hand side zero for the empty set,
  agreeing with the paper's continuous extension L(0) = 0 (page 4). The prose
  discussion of subcube sharpness and failure below exponent 1/2 is not an
  additional formal target.
- Theorem 1.2, page 2: pairwise disjointness and union equal to `univ` encode
  the partition. The local edge measure counts coordinate flips from A to B,
  divided by 2^n. Each crossing edge has exactly one endpoint in A, so there is
  no factor of two. The other terms are sqrt(n) times normalized |W| and 1/2.
- Theorem 1.3, page 2, (1.3): real-valued f with every value 0 or 1 is an
  equivalent encoding of the stated Boolean codomain. The local gradient
  keeps the factor 1/2 inside each squared coordinate difference. `deviation`
  is the L1 norm of f minus its uniform mean. The conjunction also includes
  the theorem's equality assertion for either coordinate half-cube, encoded
  by f(x) = 1 exactly when x_i = b. No converse classification is claimed.

## Historical context

This review preceded the completed proof and verification. The original archive was based on lean-verification-template commit a2b0336c176c884d3e7ea3b833b74673b0c2917d. See VERIFICATION.json and evidence/candidate-comparator.log for the final outcome.
