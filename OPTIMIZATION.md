# Verified degree-six proof optimization

The selected profile remains exactly the verified degree-six R, together with
the same logarithmic L, cubic Q, and four affine lower chords. The approved
Challenge and comparator configuration are unchanged.

## Mathematical change

For two mixed-case chord intervals x in [a,b], the old coordinates were
x=a+(b-a)u and y=1/2+(1/2-x)v. This makes y depend on both parameters and
raises the degree of the squared polynomial certificate in u.

The new proof certifies a larger rectangle using
x=a+(b-a)u and y=1/2+(1/2-a)v. Every required point lies in this rectangle:
y<=1-x and x>=a imply y<=1-a. Because y is now independent of u, the R(y)
terms no longer raise the polynomial degree in u. Exact Bernstein coefficient
certificates and the transport back to the original domain are proved in Lean.

Only LR1Q, LR3Q, their case assembly, and coordinate transport changed. The
other cases and all analytic bounds are reused unchanged. The idea was
reconstructed locally during the degree-five investigation; neither the
blocked handoff download nor the degree-five polynomial is a dependency.

## Size reductions

- Total Lean proof source: 10,343 -> 7,548 lines (2,795 fewer; 27.0%).
- Mixed-case certificate leaves: 24 -> 19.
- Nonzero Bernstein terms: 2,474 -> 1,458.
- Combined LR1Q/LR3Q serialized Lean module size:
  606,664,512 -> 92,116,768 bytes (84.8% smaller).

No proof code was merely moved out of the line count. It covers Solution.lean
and every Solution/*.lean source in each project, excluding the fixed reference
Challenge and external Mathlib dependencies in both cases.

## Verification and measurement

The optimized proof passed the unchanged complete comparator with Lean,
NanoDa and con-ron: 34,628 declarations, exit code zero, and
`Your solution is okay!`. The first measured optimized run took 340.399 seconds.
The fresh unchanged-baseline control passed in 738.134 seconds.
The optimized run used 53.9% less wall time (2.17x speed ratio)
in this matched pair. Each version was measured once in this comparison;
this is an observed result, not a statistical performance guarantee.
Both use the same environment, toolchain, dependencies, prebuilt project
caches and full comparator script. No other Lean workloads run during these
measurements. These are cached-build end-to-end verification measurements,
not clean dependency-build benchmarks.

The original verified baseline remains preserved in
/workspace/hamming-cube-review. The optimized project is a separate local clone
at /workspace/hamming-cube-optimization, branch proof-optimization, with its own
build/dependency/cache copies. Both originate from the exact template commit
recorded in REVIEW.md. No saved environment was created or changed, and no
repository was pushed or published.
