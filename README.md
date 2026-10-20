# Lean verification of *The record statistic and forward stability of Schubert products*

This repository, `rhodges-math/schubert-forward-stability` (release 1.0.0),
contains a Lean 4 formalization of *The record statistic and forward stability
of Schubert products* (Andrew Hardt, Reuven Hodges, and Hanzhang Yin, 2026),
[arXiv:2604.02964](https://arxiv.org/abs/2604.02964).

All results of the paper are formalized. The formalization proves the record
probabilities of uniform, Grassmannian and Boolean permutations (Theorem 1.1),
and the Hardt–Wallach formula expressing the forward stability
$\mathrm{FS}(u,v)$ of a product of Schubert polynomials through the records of
$u$ and $v$ (1.2). For independent uniform $u$ and $v$ it proves
$\mathbb{E}\[\mathrm{FS}(u,v)\] = 2n-2\ln n-2\gamma+c+o(1)$ with
$c \in \[1,\pi^2/6\]$ and a Gaussian limit law (Theorem 1.3); for Grassmannian
permutations, $\mathbb{E}\[\mathrm{FS}(u,v)\] = \tfrac32 n-\tfrac{1}{2\sqrt\pi}\sqrt n-2+o(1)$
and the limit law $-\tfrac12\max(Z\_1,Z\_2)$ (Theorem 1.4); and for Boolean
permutations, $\mathbb{E}\[\mathrm{FS}(u,v)\] = n+O(1)$ (Theorem 1.5). It proves the
corresponding results for backward stability (Section 6). Every other statement
of the paper is formalized as well: its lemmas, propositions, corollaries,
definitions, examples, remarks and displayed equations, and the standard
results it cites, 99 entries in all, listed in
[docs/STATEMENTS.md](docs/STATEMENTS.md). The conjectures of the paper are
stated, and neither proved nor assumed.

These results are proved with no hypotheses beyond Lean's standard axioms. The
development uses Lean **4.35.0-rc3** and a pinned version of **Mathlib**.
Lean 4.35.0-rc3 is a release candidate; the pin may move to the stable Lean
4.35.0 release.

Four of its five libraries are independent of the paper and may be of use
beyond it: permutations of the positive integers that move finitely many
points, with their records, patterns and random models; Schubert polynomials
over any commutative ring, with their structure constants and stability; limit
theorems for triangular arrays on varying probability spaces; and strong
mixing, with the Bernstein inequality of Merlevède, Peligrad and Rio; see
[Libraries](#libraries).

## AI assistance and verification

**I used GPT-6.1 Sol and Claude Opus 5.5 to help construct the Lean files.** I
reviewed all definitions, hypotheses, and theorem statements to check that
they faithfully express the intended mathematics, including the results of
the paper listed below.

The development was compiled with Lean, and the axiom dependencies of every
declaration were audited: they use only `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorry`-based proofs or additional unproved axioms.
The mathematical review addresses the correspondence between the formal
statements and the paper, which Lean's proof checking alone does not establish.

## Main results

The entry point is
[SchubertForwardStability/Paper/Main.lean](SchubertForwardStability/Paper/Main.lean),
which imports every result of the paper;
[docs/STATEMENTS.md](docs/STATEMENTS.md) lists each statement of the paper with
its Lean counterparts.

```lean
import SchubertForwardStability

open RecordStability SchubertPolynomial

#check record_probability_families
#check productForwardStability_eq_recordBound
#check uniform_product_expectation
#check uniform_product_gaussian
#check grassmannian_expectation
#check grassmannian_gaussian
#check boolean_product_expectation
#check productBackStability_add_eq_max
#check backward_identDistrib
#check backward_asymptotics
```

Names below are relative to the namespace `RecordStability`, except those
beginning with `SchubertPolynomial.`, `FinitaryPerm.`, `LimitTheorems.` or
`StrongMixing.`, which are in the general libraries, and Mathlib names.

### Notation

Permutations are the permutations of the positive integers that move finitely
many points, `FinitaryPerm ℕ+`; the symmetric group $S\_n$ is the finite set
`symmetricGroup n` of those that fix every position above $n$, so that
$S\_n \subseteq S\_{n+1}$ as in the paper. Multiplication is composition. A
random permutation uniform in a finite family $\mathcal W$ has law
`unif 𝒲`, and an independent uniform pair $(u,v)$ has law `pairLaw 𝒲`, the
uniform law on $\mathcal W\times\mathcal W$. Expectations are integrals against
these laws, $o(1)$ is a limit in `Filter.atTop`, $O(1)$ is `Asymptotics.IsBigO`,
and convergence in distribution is Mathlib's `TendstoInDistribution`.

| Paper | Lean |
| --- | --- |
| $S\_{\mathbb{Z}\_+}$; $S\_n$; $\mathrm{Grass}\_n$; $\mathcal{B}\_n$ | `FinitaryPerm ℕ+`; `symmetricGroup n`; `grassmannian n`; `boolean n` |
| $\mathrm{Unif}(\mathcal W)$; $u,v$ independent uniform in $\mathcal W$ | `unif 𝒲`; `pairLaw 𝒲` |
| $\mathrm{rec}\_j(w)=1$; $\chi\_j(w)$ | `FinitaryPerm.IsRecord w j`; `w.nonRecordIndicator j` |
| $\mathrm{FS}(w)$; $\Lambda\_i(w)$ | `FinitaryPerm.forwardStability w`; `w.nonRecordsFrom i` |
| $\mathfrak{S}\_w$ over a commutative ring $R$ | `SchubertPolynomial.schubert R w` |
| $c^w\_{u,v}$ | `SchubertPolynomial.structureConst u v w` |
| $1\times w$; $w\_0 \in S\_n$ | `SchubertPolynomial.shiftRight w`; `FinitaryPerm.longestElement n` |
| $\mathrm{FS}(u,v)$; $\mathrm{BS}(u,v)$ | `productForwardStability u v`; `productBackStability u v` |
| $\gamma$; $F\_m$; $\mathcal{N}(0,1)$ | `Real.eulerMascheroniConstant`; `Int.fib m`; `gaussianReal 0 1` |

### Theorem 1.1: record probabilities

Let $n \ge 1$ and $j \in \[n\]$. If $w$ is uniform in $S\_n$, then
$\mathbb{P}(\mathrm{rec}\_j(w)=1) = 1/j$. If $w$ is uniform in $\mathrm{Grass}\_n$, then

$$
\mathbb{P}(\mathrm{rec}\_j(w)=1)=\frac{\sum\_{k=j}^{n}\binom{n}{k}+2^{j-1}-n}{2^{n}-n}.
$$

If $w$ is uniform in $\mathcal{B}\_n$, then

$$
\mathbb{P}(\mathrm{rec}\_j(w)=1)=\frac{F\_{2n-2}-F\_{2j-4}F\_{2(n-j)-1}}{F\_{2n-1}}
=\frac{2\phi^{2n-2}+2\phi^{2-2n}+\phi^{2n-4j+3}-\phi^{4j-2n-3}}{\sqrt5\\,(\phi^{2n-1}+\phi^{1-2n})},
$$

where $F\_m$ is the Fibonacci sequence extended to negative indices and
$\phi=(1+\sqrt5)/2$.

The four formulas are the four conjuncts of `record_probability_families`,
stated for every $n$ and every position $j \le n$. The uniform case is Rényi's
theorem, which is proved here: the record indicators of a uniform permutation
are independent.

These declarations are in `RecordStability`
([RecordProbabilities.lean](SchubertForwardStability/Paper/RecordProbabilities.lean))
and `FinitaryPerm` (the Permutations library).

| Declaration | Result |
| --- | --- |
| `record_probability_families` | All of Theorem 1.1 |
| `FinitaryPerm.iIndepFun_uniform_records` | The record indicators of a uniform element of $S\_n$ are independent |
| `FinitaryPerm.uniform_record_probability` | Position $j$ is a record with probability $1/j$ |
| `FinitaryPerm.card_boolean_int_fib` | $\lvert\mathcal{B}\_n\rvert=F\_{2n-1}$ |

### Equation (1.2): forward stability through records

For all $u,v \in S\_{\mathbb{Z}\_+}$,

$$
\mathrm{FS}(u,v)=\max\_{1\le i\le 1+\max(\mathrm{FS}(u),\mathrm{FS}(v))}\bigl(\Lambda\_i(u)+\Lambda\_i(v)+i-1\bigr).
$$

Here $\mathrm{FS}(u,v)$ is the least $m \ge 1$ such that $w \in S\_m$ for every
$w$ with $c^w\_{u,v}\ne0$, and the structure constants are the coordinates of
$\mathfrak{S}\_u\mathfrak{S}\_v$ in the basis of Schubert polynomials. The paper cites
this formula from Hardt and Wallach; it is proved here, from the
divided-difference definition of Schubert polynomials: by induction with the
transition equation, the degree of $\mathfrak{S}\_w$ in $x\_i$ is the number of
non-records of the sequence $w(i),w(i+1),\ldots$.

These declarations are in `SchubertPolynomial`
([RecordBound.lean](SchubertForwardStability/SchubertPolynomials/Products/RecordBound.lean),
[SuffixDegrees.lean](SchubertForwardStability/SchubertPolynomials/Stability/SuffixDegrees.lean)).

| Declaration | Result |
| --- | --- |
| `productForwardStability_eq_recordBound` | Equation (1.2) |
| `schubert_degreeOf_eq_suffixCount` | The degree of $\mathfrak{S}\_w$ in $x\_i$ is the number of non-records after position $i$ |
| `productForwardStability` | $\mathrm{FS}(u,v)$, the least $m \ge 1$ containing the support of the product |
| `FinitaryPerm.pairRecordBound` | The right side of (1.2) |

### Theorem 1.3: uniform permutations

Let $u$ and $v$ be independent and uniform in $S\_n$. As $n\to\infty$,

$$
\mathbb{E}\[\mathrm{FS}(u,v)\] = 2n-2\ln n-2\gamma+c+o(1),
\qquad
\frac{\mathrm{FS}(u,v)-(2n-2\ln n)}{\sqrt{2\ln n}} \xrightarrow{d} \mathcal{N}(0,1),
$$

where $c\in\[1,\pi^2/6\]$ and $\gamma$ is the Euler–Mascheroni constant.

The expectation statement asserts that some $c\in\[1,\pi^2/6\]$ makes the
difference tend to $0$. The proof follows the paper: $\mathrm{FS}(u,v)$ is the
maximum of a walk driven by the record indicators, the record count obeys a
central limit theorem, and the overshoot of the walk is controlled. The
Lindeberg and Lyapunov central limit theorems and Slutsky's theorem are proved
in the limit theorems library.

These declarations are in `RecordStability`
([Uniform/Expectation.lean](SchubertForwardStability/Paper/Uniform/Expectation.lean),
[Uniform/ProductGaussian.lean](SchubertForwardStability/Paper/Uniform/ProductGaussian.lean)).

| Declaration | Result |
| --- | --- |
| `uniform_product_expectation` | The expectation in Theorem 1.3 |
| `uniform_product_gaussian` | The limit law in Theorem 1.3 |
| `uniform_record_gaussian` | Proposition 3.7: the record count is asymptotically normal |
| `LimitTheorems.tendstoInDistribution_lindeberg` | Lindeberg's theorem for triangular arrays |

### Theorem 1.4: Grassmannian permutations

Let $u$ and $v$ be independent and uniform in $\mathrm{Grass}\_n$. As
$n\to\infty$,

$$
\mathbb{E}\[\mathrm{FS}(u,v)\] = \frac{3}{2}n-\frac{1}{2\sqrt{\pi}}\sqrt{n}-2+o(1),
\qquad
\frac{\mathrm{FS}(u,v)-\frac32 n}{\sqrt n}\xrightarrow{d}-\frac12\max(Z\_1,Z\_2),
$$

with $Z\_1,Z\_2$ independent standard normal.

The proof follows the paper: in the subset model $\mathbb{G}\_n$,
$\mathrm{FS}(u,v)$ is an explicit function of two subset maxima and sizes up to an
exponentially rare error, and the total variation distance between
$\mathbb{G}\_n$ and the uniform law on $\mathrm{Grass}\_n$ tends to $0$. The limit law
is stated with the product of two standard normal laws.

These declarations are in `RecordStability`
([Grassmannian/Expectation.lean](SchubertForwardStability/Paper/Grassmannian/Expectation.lean),
[Grassmannian/ProductGaussian.lean](SchubertForwardStability/Paper/Grassmannian/ProductGaussian.lean)).

| Declaration | Result |
| --- | --- |
| `grassmannian_expectation` | The expectation in Theorem 1.4 |
| `grassmannian_gaussian` | The limit law in Theorem 1.4 |
| `grassmannian_totalVariation_le` | Lemma 4.13: the subset model is close to uniform |

### Theorem 1.5: Boolean permutations

Let $u$ and $v$ be independent and uniform in $\mathcal{B}\_n$. Then
$\mathbb{E}\[\mathrm{FS}(u,v)\] = n+O(1)$.

The statement is that $\mathbb{E}\[\mathrm{FS}(u,v)\]-n$ is $O(1)$ as $n\to\infty$. The
proof follows the paper: a Boolean permutation is encoded by a word of block
tags, whose presence process is a time-inhomogeneous Markov chain; its strong
mixing and the Bernstein inequality of Merlevède, Peligrad and Rio bound the
excess of the walk over its final value. The Bernstein inequality is proved
here, from its Laplace-transform estimate, as one-sided tail bounds and as a
two-sided bound with a factor $2$.

The block-tag encoding also gives an exact uniform sampler for $\mathcal{B}\_n$
(Remark 5.22). Lean writes it as a program that counts its steps, where each
arithmetic operation, memory access and choice among at most three outcomes
with integer weights is one step, whatever the size of the numbers. Its output
is uniform on $\mathcal{B}\_n$, and every run uses at most $16n$ steps.

These declarations are in `RecordStability`
([Boolean/Expectation.lean](SchubertForwardStability/Paper/Boolean/Expectation.lean),
[Boolean/SamplerCost.lean](SchubertForwardStability/Paper/Boolean/SamplerCost.lean))
and the strong mixing library.

| Declaration | Result |
| --- | --- |
| `boolean_product_expectation` | Theorem 1.5 |
| `finiteMixingCoeff_boolean_le` | Proposition 5.24: geometric strong mixing |
| `StrongMixing.mpr_positive_lower_tail` | Lemma 5.25 |
| `boolean_sampler_linear` | Remark 5.22: a uniform sampler for $\mathcal{B}\_n$ with at most $16n$ steps |

### Backward stability (Section 6)

Backward stability $\mathrm{BS}(u,v)$ is the least $k\ge0$ such that for every
$r\ge0$,

$$
\mathfrak{S}\_{1^{k+r}\times u}\mathfrak{S}\_{1^{k+r}\times v}
=\sum\_{w}c^{w}\_{1^k\times u,\\,1^k\times v}\\,\mathfrak{S}\_{1^r\times w}.
$$

For $n\ge1$ and $u,v\in S\_n$,
$\mathrm{BS}(u,v)+n=\max\\{n,\mathrm{FS}(w\_0uw\_0,w\_0vw\_0)\\}$ (6.1). Consequently, for
$u,v$ independent and uniform in $S\_n$, $\mathrm{Grass}\_n$ or $\mathcal{B}\_n$,
$\mathrm{BS}(u,v)+n$ has the law of $\max\\{n,\mathrm{FS}(u,v)\\}$ (Corollary 6.2),
and the asymptotics of forward stability carry over (Corollary 6.4):
$\mathbb{E}\[\mathrm{BS}(u,v)\] = n-2\ln n-2\gamma+c+o(1)$ with the constant $c$ of
Theorem 1.3 and a normal limit law for uniform permutations,
$\mathbb{E}\[\mathrm{BS}(u,v)\] = \tfrac12 n-\tfrac{1}{2\sqrt\pi}\sqrt n-2+o(1)$ and the
limit law $-\tfrac12\max(Z\_1,Z\_2)$ for Grassmannian permutations, and
$\mathbb{E}\[\mathrm{BS}(u,v)\] = O(1)$ for Boolean permutations.

Lean defines `productBackStability` as the least $k$ from which the support of
the product is stable under further shifts, and proves that this is the
definition above (`productBackStability_eq_sInf_expansion`) and that it equals
the last number of shifts at which an output moves $1$, or $0$. The identity
is proved from the $w\_0$-symmetry of the structure constants. The backward
asymptotics use the bounds $\mathbb{E}\[\max(0,n-\mathrm{FS})\]\le 1/n$ for uniform
permutations, $\mathbb{P}(\mathrm{FS}\lt n)\le Ce^{-cn}$ for Grassmannian permutations,
and $\mathbb{E}\[\max(0,n-\mathrm{FS})\]\le 1/3$ for Boolean permutations.

These declarations are in `SchubertPolynomial`
([Backward/Stabilization.lean](SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean),
[Backward/Identity.lean](SchubertForwardStability/SchubertPolynomials/Backward/Identity.lean))
and `RecordStability`
([Backward/Law.lean](SchubertForwardStability/Paper/Backward/Law.lean),
[Backward/Asymptotics.lean](SchubertForwardStability/Paper/Backward/Asymptotics.lean)).

| Declaration | Result |
| --- | --- |
| `productBackStability_eq_sInf_expansion` | $\mathrm{BS}(u,v)$ is the least $k$ satisfying the identity above |
| `productBackStability_add_eq_max` | Equation (6.1): $\mathrm{BS}(u,v)+n=\max\\{n,\mathrm{FS}(w\_0uw\_0,w\_0vw\_0)\\}$ |
| `backward_identDistrib` | Corollary 6.2: $\mathrm{BS}+n$ has the law of $\max\\{n,\mathrm{FS}\\}$ |
| `backward_asymptotics` | All of Corollary 6.4, with the uniform constant shared with Theorem 1.3 |
| `backward_expectation` | $\mathbb{E}\[\mathrm{BS}\]=\mathbb{E}\[\mathrm{FS}\]-n+\mathbb{E}\[\max(0,n-\mathrm{FS})\]$ |
| `uniform_backward_expectation`, `uniform_backward_gaussian` | $\mathbb{E}\[\mathrm{BS}\]=n-2\ln n-2\gamma+c+o(1)$, and the normal limit |
| `grassmannian_backward_expectation`, `grassmannian_backward_gaussian` | $\mathbb{E}\[\mathrm{BS}\]=\frac12 n-\frac{1}{2\sqrt\pi}\sqrt n-2+o(1)$, and the limit $-\frac12\max(Z\_1,Z\_2)$ |
| `boolean_backward_expectation` | $\mathbb{E}\[\mathrm{BS}\]=O(1)$ |

### Every other statement

Every other statement of the paper, and every standard result it cites, is
listed in [docs/STATEMENTS.md](docs/STATEMENTS.md) with its Lean counterparts.
The conjectures of Sections 7 and 8 are stated in
[Conjectures.lean](SchubertForwardStability/Paper/Conjectures.lean) as Lean
propositions; no result depends on them.

## Libraries

The Lean library `SchubertForwardStability` is divided into six parts. The
first five are general and do not import the last, which contains the paper.

### The Permutations library

[SchubertForwardStability/Permutations/](SchubertForwardStability/Permutations)
(namespaces `FinitaryPerm` and `PermutationPattern`, 180 files)
develops the permutations of the positive integers that move finitely many
points. They form the subgroup of `Equiv.Perm ℕ+` generated by transpositions,
and contain each symmetric group $S\_n$. The library covers inversions, length,
descents, the Lehmer code and reduced words; records, the non-record counts
$\Lambda\_i$ and forward stability; Grassmannian and Boolean permutations,
with $\lvert\mathcal{B}\_n\rvert=F\_{2n-1}$, the commutation classes of Boolean
reduced words, the encoding of Boolean permutations by block tags, the Markov
chain of a uniform Boolean permutation and an exact sampler; patterns and
avoidance, with the Catalan counts of 132- and 231-avoiders and the equality
of their record-set distributions; and uniform random permutations, Rényi's
independence of records, and the subset model of Grassmannian permutations.

| Declaration | Result |
| --- | --- |
| `FinitaryPerm.iIndepFun_uniform_records` | The record indicators of a uniform element of $S\_n$ are independent (Rényi) |
| `FinitaryPerm.card_boolean_int_fib` | $\lvert\mathcal{B}\_n\rvert=F\_{2n-1}$ |
| `FinitaryPerm.booleanTags_bijOn` | Boolean permutations correspond to valid block-tag words |
| `FinitaryPerm.tagLaw_conditional_next` | The presence process of a uniform Boolean permutation is Markov |
| `FinitaryPerm.tagSuffixSampler_uniform` | The sequential sampler is uniform on Boolean permutations |
| `PermutationPattern.card_avoiding231_catalan` | $\lvert\mathrm{Av}\_n(231)\rvert=\mathrm{Cat}\_n$ |
| `PermutationPattern.recordFiberCard_catalan_eq` | 132- and 231-avoiders have the same number of elements with each record set |
| `FinitaryPerm.longest_class_law` | Conjugation by $w\_0$ preserves the uniform, Grassmannian and Boolean laws |

### The Schubert polynomials library

[SchubertForwardStability/SchubertPolynomials/](SchubertForwardStability/SchubertPolynomials)
(namespace `SchubertPolynomial`, 78 files) develops divided
differences on `MvPolynomial ℕ+ R` and Schubert polynomials over any
commutative ring $R$: their stability, the basis they form, the coinvariant
algebra, Monk's rule and the transition equation, the structure constants with
their $w\_0$-symmetry and Li's shift stability, and the forward and backward
stability of a product.

| Declaration | Result |
| --- | --- |
| `SchubertPolynomial.schubertBasis` | The Schubert polynomials form a basis of the polynomial ring |
| `SchubertPolynomial.structureConst_conjugate_longest` | $c^w\_{u,v}=c^{w\_0ww\_0}\_{w\_0uw\_0,w\_0vw\_0}$ |
| `SchubertPolynomial.structureConst_shiftRight` | $c^{1\times w}\_{1\times u,1\times v}=c^w\_{u,v}$ (Li) |
| `SchubertPolynomial.productForwardStability_eq_recordBound` | The Hardt–Wallach formula for $\mathrm{FS}(u,v)$ |
| `SchubertPolynomial.productBackStability_add_eq_max` | Backward stability through forward stability |

### The limit theorems library

[SchubertForwardStability/LimitTheorems/](SchubertForwardStability/LimitTheorems)
(namespace `LimitTheorems`, 34 files) develops convergence in
probability and Slutsky's theorem for random variables on varying probability
spaces, the Lindeberg and Lyapunov central limit theorems for triangular arrays
with finite rows, the total variation distance and maximal couplings of laws on
finite sets, and binomial estimates: a Chernoff bound, De Moivre's mean absolute
deviation, a Stirling estimate of the central binomial coefficient and the
binomial central limit theorem.

| Declaration | Result |
| --- | --- |
| `LimitTheorems.tendstoInDistribution_lindeberg` | Lindeberg's central limit theorem for triangular arrays |
| `LimitTheorems.tendstoInDistribution_lyapunov` | Lyapunov's central limit theorem |
| `LimitTheorems.slutsky_prod` | Slutsky's theorem on varying spaces |
| `LimitTheorems.exists_maximalCoupling` | A coupling attaining the total variation distance |
| `LimitTheorems.tendsto_binomial_gaussian` | The binomial central limit theorem |

### The strong mixing library

[SchubertForwardStability/StrongMixing/](SchubertForwardStability/StrongMixing)
(namespace `StrongMixing`, 81 files) develops Rosenblatt's
$\alpha$-mixing coefficients of sequences and of finite rows, their behaviour
under coordinate maps, reindexing and independent noise, Ibragimov's covariance
inequality, contraction estimates for two-state Markov chains, and the
Bernstein inequality of Merlevède, Peligrad and Rio for bounded, centered,
geometrically $\alpha$-mixing sequences, as a Laplace-transform bound and as
tail bounds.

| Declaration | Result |
| --- | --- |
| `StrongMixing.mixingCoeff` | Rosenblatt's coefficient at lag $h$ |
| `StrongMixing.finiteMixingCoeff_pair_le` | Mixing of independent pairs of rows (Bradley, Theorem 5.1(a)) |
| `StrongMixing.bounded_covariance_le` | Ibragimov's covariance inequality |
| `StrongMixing.mpr_positive_laplace_le` | The Merlevède–Peligrad–Rio Laplace-transform bound |
| `StrongMixing.mpr_positive_two_sided` | The two-sided tail bound, with a factor $2$ |

The four libraries are at version 0.1.0, recorded with per-file SHA-256 hashes
in `LIBRARY_MANIFEST.json`. The limit theorems library imports only Mathlib,
and the strong mixing library imports it; the Permutations library imports the
TypeA files below, and the Schubert polynomials library imports both.

### The TypeA files

[SchubertForwardStability/TypeA/](SchubertForwardStability/TypeA) (namespace
`Schubert`, 11 files) holds the finite permutations, length, adjacent
transpositions and divided differences of the flag-variety library, version
0.1.0, of [rhodges-math/rs-counterexample](https://github.com/rhodges-math/rs-counterexample),
by the same author. Only the module prefix of their imports differs.

### The paper

[SchubertForwardStability/Paper/](SchubertForwardStability/Paper) (namespace
`RecordStability`, 68 files) contains the results of the paper,
organized by section: `Walk/`, `Uniform/` (Section 3), `Grassmannian/`
(Section 4), `Boolean/` (Section 5), `Backward/` (Section 6) and `Catalan/`
(Section 8), with `Conjectures.lean`, `Main.lean` and `Audit.lean`. The general
parts of Sections 4, 5 and 8 (the subset model, the block-tag encoding and its
Markov chain, and the record-set equidistribution) are proved in the
Permutations library, and [docs/STATEMENTS.md](docs/STATEMENTS.md) links them.

## Build and verify

Install [Lean and Lake through elan](https://lean-lang.org/install/) and
[Python 3](https://www.python.org/downloads/). Git must also be available.
The `lean-toolchain` file selects Lean 4.35.0-rc3 automatically, and
`lake-manifest.json` pins Mathlib and its public dependencies.

From the repository directory, run:

```text
lake exe cache get
python build.py --jobs 3
lake env lean SchubertForwardStability/Paper/Audit.lean
```

On Windows, `py -3` can replace `python`; a short project path is recommended.
The first setup requires internet access and space for Lean and Mathlib.
The first command downloads public dependency caches. The Python helper
recompiles all **453 local Lean modules** in dependency order, and exits
with a nonzero status if a module fails. With three jobs the full build takes
about 45 minutes on a laptop.

To resume an interrupted build, or to check that every module was compiled
from the current sources:

```text
python build.py --jobs 3 --resume
python build.py --check
```

A standard `lake build` target is also configured.

The audit prints the axiom dependencies of every result of the paper listed in
[docs/STATEMENTS.md](docs/STATEMENTS.md). The expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

Recorded checks:

- [provenance/BUILD_CHECK.json](provenance/BUILD_CHECK.json)
- [provenance/ENDPOINT_AUDIT.txt](provenance/ENDPOINT_AUDIT.txt)

To check the distributed snapshot's hashes and the local import completeness:

```text
python verify_bundle.py
```

`SHA256SUMS.json` describes this release snapshot. Intentional edits require
updating the hash inventory before that integrity check can pass again.

## Source layout

- `SchubertForwardStability/Permutations/`, `SchubertPolynomials/`,
  `LimitTheorems/`, `StrongMixing/`: the general libraries.
- `SchubertForwardStability/TypeA/`: files of the flag-variety library.
- `SchubertForwardStability/Paper/`: the paper, by section (`Walk/`,
  `Uniform/`, `Grassmannian/`, `Boolean/`, `Backward/`, `Catalan/`), with
  `RecordProbabilities.lean` (Theorem 1.1) and `Conjectures.lean` (Sections 7
  and 8).
- `SchubertForwardStability/Paper/Main.lean` and `Audit.lean`; the root module
  `SchubertForwardStability.lean` imports everything.
- `LIBRARY_MANIFEST.json`: the versions and file hashes of the libraries.
- `docs/STATEMENTS.md`: the statements of the paper and their Lean
  counterparts.
- `provenance/`: the build record, the axiom audit, the pinned dependencies and
  the module inventory.

## Attribution and licensing

This repository is licensed under the [Apache License 2.0](LICENSE).
Redistributions must retain the [NOTICE](NOTICE) file. If you use or adapt this
code, please cite this repository; citation metadata is in
[CITATION.cff](CITATION.cff).

`SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean` is adapted
from Mathlib's `ConvergenceInDistribution.lean` (Rémy Degenne, **Apache License
2.0**); its header keeps the original copyright notice and states the
modification.

Mathlib and its dependencies are downloaded by Lake at pinned revisions and keep
their own licenses; see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
