<!-- Adapted from XinyuanXie-hub/Konig-constant, under the included Apache-2.0 license. Mathematical statements, source reference, and verification links changed for the Hamming cube. -->
<!-- Original adaptation notice: Adapted from XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Mathematical statement and verification links changed for König; pictures omitted. -->

# Isoperimetric inequalities on the Hamming cube

This project uses Lean to verify the three statements below, corresponding to Theorems 1.1, 1.2, and 1.3 of the paper cited below.

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

At $`\mu(A)=0`$, the left side is defined to be zero. This is the inequality in Theorem 1.1 of the paper; its additional prose about subcube sharpness and failure at smaller exponents is not part of the approved formal statement.

<a name="theorem-2"></a>

**Theorem 2.** If $`Q_n=A\sqcup B\sqcup W`$ and $`\mu(A)=1/2`$, then

```math
\frac12\leq e(A,B)+\sqrt n\,\mu(W),\qquad
e(A,B)=2^{-n}\sum_{x\in A}|\{i:x^{(i)}\in B\}|.
```

Each edge from $`A`$ to $`B`$ is counted once. This is the Kahn–Park partition inequality, Theorem 1.2 of the paper.

<a name="theorem-3"></a>

**Theorem 3.** For every Boolean-valued function $`f:Q_n\to\{0,1\}`$, define

```math
|\nabla f(x)|=\left(\sum_{i=1}^n\left(\frac{f(x)-f(x^{(i)})}{2}\right)^2\right)^{1/2}.
```

Then

```math
\mathbb E|f-\mathbb Ef|\leq\mathbb E|\nabla f|.
```

Equality holds when $`f`$ is the indicator of either coordinate half-cube $`\{x:x_i=b\}`$, for any coordinate $`i`$ and $`b\in\{0,1\}`$. This is Theorem 1.3 of the paper; no converse classification of equality cases is claimed.

## Verification

To verify the correctness of the theorems in Lean, one only needs to check that the statements and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1), [Theorem 2](#theorem-2), and [Theorem 3](#theorem-3) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the latest “Lean CI” workflow run on `main`, or open the [workflow runs directly](https://github.com/XinyuanXie-hub/hamming-cube-inequalities/actions/workflows/lean.yml?query=branch%3Amain).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the end of the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.

The repository is private, so the verification link goes directly to authenticated GitHub Actions rather than a public Pages site. [REPRODUCE.md](REPRODUCE.md) gives local verification commands. The archived November 6 three-kernel result and exact source hashes are retained in [VERIFICATION.json](VERIFICATION.json) and [evidence/candidate-comparator.log](evidence/candidate-comparator.log); those historical results should not be confused with the status of a newer workflow run.
