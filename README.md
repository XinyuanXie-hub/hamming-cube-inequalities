<!-- Adapted from XinyuanXie-hub/Konig-constant, under the included Apache-2.0 license. Mathematical statements, source reference, and verification links changed for the Hamming cube. -->
<!-- Original adaptation notice: Adapted from XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Mathematical statement and verification links changed for König; pictures omitted. -->

# Isoperimetric inequalities on the Hamming cube

This project uses Lean to verify the two statements below, corresponding to Theorems 1.1 and 1.3 of the paper cited below.

> Polona Durcik, Paata Ivanisvili, Joris Roos, and Xinyuan Xie,
> *Sharp isoperimetric inequalities on the Hamming cube II: The critical exponent*,
> [arXiv:2602.20462](https://arxiv.org/abs/2602.20462).

## Mathematical statements

Let $`n\geq1`$, let $`Q_n=\{0,1\}^n`$, and write $`x^{(i)}`$ for the vertex obtained by flipping coordinate $`i`$ of $`x`$. Let $`\mu(A)=|A|/2^n`$ and let $`\mathbb E`$ denote uniform expectation on $`Q_n`$.

<a name="theorem-1"></a>

**Theorem 1.** For every $`A\subseteq Q_n`$ with $`\mu(A)\leq1/2`$, define

```math
h_A(x)=\begin{cases}
|\{i:x^{(i)}\notin A\}|,&x\in A,\\
0,&x\notin A.
\end{cases}
```

Then

```math
\mu(A)\sqrt{\log_2\!\frac{1}{\mu(A)}}\leq\mathbb E\sqrt{h_A}.
```

At $`\mu(A)=0`$, the left side is defined to be zero. This is the inequality in Theorem 1.1 of the paper; its additional prose about subcube sharpness and failure at smaller exponents is not included in the formal statement.

<a name="theorem-2"></a>

**Theorem 2.** For every Boolean-valued function $`f:Q_n\to\{0,1\}`$, define

```math
|\nabla f(x)|=\left(\sum_{i=1}^n\left(\frac{f(x)-f(x^{(i)})}{2}\right)^2\right)^{1/2}.
```

Then

```math
\mathbb E|f-\mathbb Ef|\leq\mathbb E|\nabla f|.
```

Equality holds when $`f`$ is the indicator of either coordinate half-cube $`\{x:x_i=b\}`$, for any coordinate $`i`$ and $`b\in\{0,1\}`$.

## Verification

To verify the correctness of the theorems in Lean, one only needs to check that the statements and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) and [Theorem 2](#theorem-2) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the latest “Lean CI” workflow run on `main`, or open the [workflow runs directly](https://github.com/XinyuanXie-hub/hamming-cube-inequalities/actions/workflows/lean.yml?query=branch%3Amain).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the end of the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.

