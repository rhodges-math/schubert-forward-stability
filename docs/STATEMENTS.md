# Statements of the paper and their Lean counterparts

Each statement of *The record statistic and forward stability of Schubert products*
(Andrew Hardt, Reuven Hodges, and Hanzhang Yin, 2026),
[arXiv:2604.02964](https://arxiv.org/abs/2604.02964), with its status and the Lean
declarations that formalize it, in the order of the paper. The index covers every
theorem, proposition, lemma, corollary, definition, example, remark and conjecture of the
paper, the displayed equations its proofs cite, the definitions made in its prose, and the
standard results it cites. Numbers are those printed in the paper
(arXiv:2604.02964v2), and labels are its LaTeX labels; a statement without a
number is given with its section. Definitions and conjectures have status *stated*: a
conjecture is stated as a Lean proposition and is neither proved nor assumed. A short note
follows a statement whose Lean statement or proof differs from the paper. Paths are relative
to the repository root; declarations from Mathlib are named without a path.

| Statement | Label | Status |
| --- | --- | --- |
| Records, Grassmannian and Boolean permutations, and uniform sampling (Section 1.1) | — | stated |
| Theorem 1.1 | `thm:record-probabilities` | formalized |
| Stability, basis and integrality of Schubert polynomials (Section 1.2) | — | formalized |
| Divided differences (Section 1.2) | — | stated |
| Schubert polynomials (Section 1.2) | — | stated |
| The structure constants and the forward stability of a product (Section 1.2) | — | stated |
| Shift stability of the structure constants, and backward stability (Section 1.2) | — | formalized |
| The forward stability $\mathrm{FS}(w)$ and the tail counts $\Lambda\_i(w)$ (Section 1.3) | — | stated |
| Equation (1.2) | `eq:mainFSEq` | formalized |
| Theorem 1.3 | `theoremUniformMain` | formalized |
| Theorem 1.4 | `thm:GrassmannianMain` | formalized |
| Theorem 1.5 | `thm:BooleanExpectation` | formalized |
| Equation (2.1) | `eq:delta_i` | formalized |
| Equation (2.2) | `eq:upper_inequality` | formalized |
| Definition 2.3 | `def:tv` | stated |
| Equation (2.4) | `tv-definition` | formalized |
| Definition 2.5 | — | stated |
| Definition 2.6 | `def:sigma-generated` | stated |
| Definition 2.7 | `def:rosenblatt-alpha` | stated |
| Lemma 3.1 | `lem:renyi_records` | formalized |
| Equation (3.2) | `eq:chi_marginals` | formalized |
| Lemma 3.3 | `lem:Yi_expectation` | formalized |
| Corollary 3.4 | `lem:prob_delta_i` | formalized |
| Lemma 3.5 | `lem:max_bound` | formalized |
| Proposition 3.6 | — | formalized |
| Proposition 3.7 | `prop:record_clt` | formalized |
| The Lyapunov central limit theorem for triangular arrays (Section 3) | — | formalized |
| Slutsky's theorem, the continuous mapping theorem and characteristic functions (Sections 3–4) | — | formalized |
| Lemma 3.8 | `lemma:distY2` | formalized |
| Equation (3.9) | `eq:Y2-records` | formalized |
| Lemma 3.10 | `lemma:vanishingZn` | formalized |
| Proposition 4.1 | `prop:grass_rec_uniform_exact` | formalized |
| The distribution $G\_n$ on Grassmannian permutations (Section 4.2) | — | stated |
| Lemma 4.2 | `lem:grass_binomial_descent` | formalized |
| Lemma 4.3 | `lem:grass_FS_equals_M` | formalized |
| Lemma 4.4 | `lem:grass_lambda` | formalized |
| Lemma 4.5 | `lem:grass_path_shape` | formalized |
| Corollary 4.6 | `cor:grass_fs_value` | formalized |
| Lemma 4.7 | `lem:grass_tail_bounds` | formalized |
| Optimal couplings, the binomial Chernoff bound and De Moivre's mean absolute deviation (Section 4) | — | formalized |
| Proposition 4.8 | `prop:grass_fs_exact_prob` | formalized |
| Lemma 4.9 | `lem:expected_max` | formalized |
| Lemma 4.10 | `lem:expected_max_descent` | formalized |
| Proposition 4.11 | `prop:grass-exp` | formalized |
| Proposition 4.12 | `prop:grass-dist` | formalized |
| Lemma 4.13 | `lem:grass_TV_single` | formalized |
| Reduced words of Boolean permutations (Section 5) | — | formalized |
| Equation (5.1) | `eq:bool-cardinality` | formalized |
| Remark 5.2 | `def:cont-comm-inv` | formalized |
| Definition 5.3 | `def:block-tag-word` | stated |
| Lemma 5.4 | `lem:block-boundary-encoding` | formalized |
| Lemma 5.5 | `lem:chi-as-local` | formalized |
| Lemma 5.6 | `lem:bool-rec-recurrence` | formalized |
| Example 5.7 | — | formalized |
| Corollary 5.8 | `cor:Nnj-fib` | formalized |
| Equation (5.10) | `eq:tagiuri-vajda` | formalized |
| Lemma 5.11 | `lem:fib-identity` | formalized |
| Proposition 5.13 | `prop:two-expressions` | formalized |
| Equation (5.14) | `eq:intermediateFibIdent` | formalized |
| Theorem 5.15 | `thm:Nnj-recurrence` | formalized |
| Equation (5.16) | `eq:Nnj-exact` | formalized |
| Equation (5.17) | `eq:bool-rec-prob-phi` | formalized |
| Lemma 5.18 | `lem:alpha-factor` | formalized |
| Definition 5.19 | `def:extension-counts` | formalized |
| Lemma 5.20 | `lem:transfer-matrix` | formalized |
| Lemma 5.21 | `lem:state-markov` | formalized |
| Remark 5.22 | `rem:boolean-sampling` | formalized |
| Lemma 5.23 | `lem:dobrushin` | formalized |
| Proposition 5.24 | `prop:boolean-strong-mixing` | formalized |
| Lemma 5.25 | `lem:mpr-block` | formalized |
| Lemma 5.27 | `lem:bool-uniform-drift` | formalized |
| Equation (5.28) | `eq:bool-uniform-drift-expr` | formalized |
| Lemma 5.29 | `lem:bool-terminal` | formalized |
| Lemma 5.30 | `lem:boolean-fs-lower` | formalized |
| Equation (6.1) | `eq:bs-fs` | formalized |
| Conjugation by $w\_0$ preserves the three families (Section 6) | — | formalized |
| The $w\_0$-symmetry of the structure constants (Section 6) | — | formalized |
| Corollary 6.2 | — | formalized |
| Equation (6.3) | `eq:bs-distribution` | formalized |
| Corollary 6.4 | `cor:backward-asymptotics` | formalized |
| Definition 7.1 | — | stated |
| Definition 7.2 | — | stated |
| Definition 7.3 | — | stated |
| Definition 7.4 | — | stated |
| Definition 7.5 | — | stated |
| Definition 7.6 | — | stated |
| Conjecture 7.7 | `conj:fs-rdense` | stated |
| Conjecture 7.8 | `conj:fs-rint` | stated |
| Conjecture 7.9 | `conj:fs-rsparse` | stated |
| Proposition 8.1 | `prop:132-231-record-set-count` | formalized |
| Equation (8.3) | `eq:231-split-rev` | formalized |
| Equation (8.4) | `eq:record-recursion-rev` | formalized |
| Catalan counts of $\mathrm{Av}\_m(231)$ and $\mathrm{Av}\_m(132)$ (Section 8) | — | formalized |
| Corollary 8.5 | `cor:132-231-record-eqdist` | formalized |
| Corollary 8.6 | `cor:132-231-record-eqdist-prob` | formalized |
| Corollary 8.7 | `cor:132-231-fs-eqdist` | formalized |
| Definition 8.8 | — | stated |
| Definition 8.9 | — | stated |
| Conjecture 8.10 | `conj:record-equivalence-recursive` | stated |

## Statements

### Records, Grassmannian and Boolean permutations, and uniform sampling (Section 1.1)

Status: **stated**

- `FinitaryPerm.leftInversionCount` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.IsRecord` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.nonRecordIndicator` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.grassmannian` ([SchubertForwardStability/Permutations/Classes/Grassmannian.lean](../SchubertForwardStability/Permutations/Classes/Grassmannian.lean))
- `FinitaryPerm.boolean` ([SchubertForwardStability/Permutations/Classes/Boolean.lean](../SchubertForwardStability/Permutations/Classes/Boolean.lean))
- `FinitaryPerm.unif` ([SchubertForwardStability/Permutations/Random/Uniform.lean](../SchubertForwardStability/Permutations/Random/Uniform.lean))
- `FinitaryPerm.symmetricGroup` ([SchubertForwardStability/Permutations/Finitary/Finite.lean](../SchubertForwardStability/Permutations/Finitary/Finite.lean))
- `FinitaryPerm.IsGrassmannian` ([SchubertForwardStability/Permutations/Classes/Grassmannian.lean](../SchubertForwardStability/Permutations/Classes/Grassmannian.lean))
- `FinitaryPerm.IsBoolean` ([SchubertForwardStability/Permutations/Classes/Boolean.lean](../SchubertForwardStability/Permutations/Classes/Boolean.lean))
- `FinitaryPerm.pairLaw` ([SchubertForwardStability/Permutations/Random/Uniform.lean](../SchubertForwardStability/Permutations/Random/Uniform.lean))
- `FinitaryPerm.recordSet` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.recordCount` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))

### Theorem 1.1 (`thm:record-probabilities`)

Status: **formalized**

- `RecordStability.record_probability_families` ([SchubertForwardStability/Paper/RecordProbabilities.lean](../SchubertForwardStability/Paper/RecordProbabilities.lean))

### Stability, basis and integrality of Schubert polynomials (Section 1.2)

Status: **formalized**

Cited in the paper and proved here over every commutative ring, from the divided-difference definition of $\mathfrak{S}\_w$. The identification with products of Schubert classes is not formalized.

- `SchubertPolynomial.ambientSchubert_succ` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_eq_ambient` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_linearIndependent` ([SchubertForwardStability/SchubertPolynomials/Basis/Global.lean](../SchubertForwardStability/SchubertPolynomials/Basis/Global.lean))
- `SchubertPolynomial.schubert_span_eq_top` ([SchubertForwardStability/SchubertPolynomials/Basis/Global.lean](../SchubertForwardStability/SchubertPolynomials/Basis/Global.lean))
- `SchubertPolynomial.schubertBasis_apply` ([SchubertForwardStability/SchubertPolynomials/Basis/Global.lean](../SchubertForwardStability/SchubertPolynomials/Basis/Global.lean))
- `SchubertPolynomial.finiteSchubertBasis_apply` ([SchubertForwardStability/SchubertPolynomials/Basis/Finite.lean](../SchubertForwardStability/SchubertPolynomials/Basis/Finite.lean))
- `SchubertPolynomial.artinSpan_eq_span_schubert` ([SchubertForwardStability/SchubertPolynomials/Basis/Finite.lean](../SchubertForwardStability/SchubertPolynomials/Basis/Finite.lean))
- `SchubertPolynomial.structureConst_expansion` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))
- `SchubertPolynomial.structureCoefficients_unique` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))
- `SchubertPolynomial.structureConst_finite_support` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))

### Divided differences (Section 1.2)

Status: **stated**

Here $\partial\_i$ acts on $R\[x\_1,x\_2,\ldots\]$ for any commutative ring $R$, by $(x\_i-x\_{i+1})\\,\partial\_i(p)=p-s\_i(p)$.

- `SchubertPolynomial.dividedDifference` ([SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean))
- `SchubertPolynomial.root_mul_dividedDifference` ([SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean))
- `SchubertPolynomial.dividedDifference_mul` ([SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean))
- `SchubertPolynomial.dividedDifference_sq` ([SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Positive.lean))
- `SchubertPolynomial.dividedDifference_map` ([SchubertForwardStability/SchubertPolynomials/Divided/Naturality.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Naturality.lean))
- `SchubertPolynomial.dividedDifference_braid` ([SchubertForwardStability/SchubertPolynomials/Divided/Relations.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Relations.lean))
- `SchubertPolynomial.dividedDifference_commute` ([SchubertForwardStability/SchubertPolynomials/Divided/Relations.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Relations.lean))
- `SchubertPolynomial.wordDividedDifference` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_append` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_map` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_braid` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_commute` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_repeat` ([SchubertForwardStability/SchubertPolynomials/Divided/Words.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Words.lean))
- `SchubertPolynomial.wordDividedDifference_eq` ([SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean))
- `SchubertPolynomial.wordDividedDifference_zero` ([SchubertForwardStability/SchubertPolynomials/Divided/Unreduced.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Unreduced.lean))
- `SchubertPolynomial.permutationDividedDifference` ([SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean))
- `SchubertPolynomial.permutationDividedDifference_eq` ([SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean))
- `SchubertPolynomial.permutationDividedDifference_one` ([SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Independence.lean))
- `SchubertPolynomial.permutationDividedDifference_mul` ([SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean))
- `SchubertPolynomial.permutationDividedDifference_mul_zero` ([SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean))
- `SchubertPolynomial.permutationDividedDifference_map` ([SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean](../SchubertForwardStability/SchubertPolynomials/Divided/Multiplication.lean))

### Schubert polynomials (Section 1.2)

Status: **stated**

Here $\mathfrak{S}\_w=\partial\_{w^{-1}w\_0}(x\_1^{n-1}x\_2^{n-2}\cdots x\_{n-1})$ for any $n$ with $w\in S\_n$, with coefficients in any commutative ring.

- `SchubertPolynomial.staircaseExponent` ([SchubertForwardStability/SchubertPolynomials/Stability/Staircase.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Staircase.lean))
- `SchubertPolynomial.staircaseMonomial` ([SchubertForwardStability/SchubertPolynomials/Stability/Staircase.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Staircase.lean))
- `SchubertPolynomial.ambientSchubert` ([SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean))
- `SchubertPolynomial.schubert` ([SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean))
- `SchubertPolynomial.ambientSchubert_eq_word` ([SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean))
- `SchubertPolynomial.ambientSchubert_succ` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.ambientSchubert_eq` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_eq_ambient` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_eq_word` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.ambientSchubert_one` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_one` ([SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean))
- `SchubertPolynomial.schubert_longestElement` ([SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Ambient.lean))
- `SchubertPolynomial.schubert_map` ([SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Construction.lean))

### The structure constants and the forward stability of a product (Section 1.2)

Status: **stated**

- `SchubertPolynomial.structureCoefficients` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))
- `SchubertPolynomial.structureConst` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))
- `SchubertPolynomial.structureConst_eq_repr` ([SchubertForwardStability/SchubertPolynomials/Products/Constants.lean](../SchubertForwardStability/SchubertPolynomials/Products/Constants.lean))
- `SchubertPolynomial.productForwardStability` ([SchubertForwardStability/SchubertPolynomials/Products/Forward.lean](../SchubertForwardStability/SchubertPolynomials/Products/Forward.lean))
- `SchubertPolynomial.productForwardStability_eq_sup` ([SchubertForwardStability/SchubertPolynomials/Products/Forward.lean](../SchubertForwardStability/SchubertPolynomials/Products/Forward.lean))
- `SchubertPolynomial.productForwardStability_le_iff_support` ([SchubertForwardStability/SchubertPolynomials/Products/Forward.lean](../SchubertForwardStability/SchubertPolynomials/Products/Forward.lean))
- `SchubertPolynomial.productForwardStability_isLeast` ([SchubertForwardStability/SchubertPolynomials/Products/Forward.lean](../SchubertForwardStability/SchubertPolynomials/Products/Forward.lean))
- `SchubertPolynomial.productForwardStability_one` ([SchubertForwardStability/SchubertPolynomials/Products/Forward.lean](../SchubertForwardStability/SchubertPolynomials/Products/Forward.lean))

### Shift stability of the structure constants, and backward stability (Section 1.2)

Status: **formalized**

Li's identity is cited in the paper and proved here. Backward stability is also shown to be the last shift at which some output of the product moves $1$, and $0$ if there is none.

- `SchubertPolynomial.structureConst_shiftRight` ([SchubertForwardStability/SchubertPolynomials/Stability/ShiftConstants.lean](../SchubertForwardStability/SchubertPolynomials/Stability/ShiftConstants.lean))
- `SchubertPolynomial.productBackStability` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.productBackStability_eq_sInf_expansion` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.isSupportStableFrom_iff_expansion` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.productBackStability_isLeast` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.isSupportStableFrom_iff` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.productBackStability_eq_sSup` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))
- `SchubertPolynomial.productBackStability_one` ([SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Stabilization.lean))

### The forward stability $\mathrm{FS}(w)$ and the tail counts $\Lambda\_i(w)$ (Section 1.3)

Status: **stated**

- `FinitaryPerm.forwardStability` ([SchubertForwardStability/Permutations/Finitary/Bounds.lean](../SchubertForwardStability/Permutations/Finitary/Bounds.lean))
- `FinitaryPerm.forwardStability_le_iff_mem` ([SchubertForwardStability/Permutations/Finitary/Finite.lean](../SchubertForwardStability/Permutations/Finitary/Finite.lean))
- `FinitaryPerm.nonRecordsFrom` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.nonRecordsFrom_eq_card` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))
- `FinitaryPerm.isRecord_iff_leftInversions_empty` ([SchubertForwardStability/Permutations/Statistics/Records.lean](../SchubertForwardStability/Permutations/Statistics/Records.lean))

### Equation (1.2) (`eq:mainFSEq`)

Status: **formalized**

Cited in the paper and proved here: by induction with the transition equation, the degree of $\mathfrak{S}\_w$ in $x\_i$ is the number of non-records of $w(i),w(i+1),\ldots$.

- `SchubertPolynomial.schubert_degreeOf_eq_suffixCount` ([SchubertForwardStability/SchubertPolynomials/Stability/Recurrence/SuffixDegrees.lean](../SchubertForwardStability/SchubertPolynomials/Stability/Recurrence/SuffixDegrees.lean))
- `SchubertPolynomial.productForwardStability_eq_suffixBound` ([SchubertForwardStability/SchubertPolynomials/Products/RecordBound.lean](../SchubertForwardStability/SchubertPolynomials/Products/RecordBound.lean))
- `SchubertPolynomial.productForwardStability_eq_recordBound` ([SchubertForwardStability/SchubertPolynomials/Products/RecordBound.lean](../SchubertForwardStability/SchubertPolynomials/Products/RecordBound.lean))
- `FinitaryPerm.pairRecordBound` ([SchubertForwardStability/Permutations/Statistics/SuffixMaximum.lean](../SchubertForwardStability/Permutations/Statistics/SuffixMaximum.lean))

### Theorem 1.3 (`theoremUniformMain`)

Status: **formalized**

- `RecordStability.uniform_product_expectation` ([SchubertForwardStability/Paper/Uniform/Expectation.lean](../SchubertForwardStability/Paper/Uniform/Expectation.lean))
- `RecordStability.uniform_product_gaussian` ([SchubertForwardStability/Paper/Uniform/ProductGaussian.lean](../SchubertForwardStability/Paper/Uniform/ProductGaussian.lean))

### Theorem 1.4 (`thm:GrassmannianMain`)

Status: **formalized**

- `RecordStability.grassmannian_expectation` ([SchubertForwardStability/Paper/Grassmannian/Expectation.lean](../SchubertForwardStability/Paper/Grassmannian/Expectation.lean))
- `RecordStability.grassmannian_gaussian` ([SchubertForwardStability/Paper/Grassmannian/ProductGaussian.lean](../SchubertForwardStability/Paper/Grassmannian/ProductGaussian.lean))

### Theorem 1.5 (`thm:BooleanExpectation`)

Status: **formalized**

- `RecordStability.boolean_product_expectation` ([SchubertForwardStability/Paper/Boolean/Expectation.lean](../SchubertForwardStability/Paper/Boolean/Expectation.lean))
- `RecordStability.booleanMeanWalk` ([SchubertForwardStability/Paper/Boolean/Means.lean](../SchubertForwardStability/Paper/Boolean/Means.lean))
- `RecordStability.booleanMeanMax` ([SchubertForwardStability/Paper/Boolean/Means.lean](../SchubertForwardStability/Paper/Boolean/Means.lean))

### Equation (2.1) (`eq:delta_i`)

Status: **formalized**

- `RecordStability.recordWalkStep_eq` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))
- `RecordStability.recordWalkStep_values` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))
- `RecordStability.abs_recordWalkStep_le` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))
- `RecordStability.recordWalk` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))
- `RecordStability.recordWalkStep` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))

### Equation (2.2) (`eq:upper_inequality`)

Status: **formalized**

- `RecordStability.product_ambient_walk_bound` ([SchubertForwardStability/Paper/Uniform/MaximumGap.lean](../SchubertForwardStability/Paper/Uniform/MaximumGap.lean))
- `RecordStability.recordWalkMaxAt` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))
- `RecordStability.recordWalkMax` ([SchubertForwardStability/Paper/Walk/Basic.lean](../SchubertForwardStability/Paper/Walk/Basic.lean))

### Definition 2.3 (`def:tv`)

Status: **stated**

- `LimitTheorems.totalVariation` ([SchubertForwardStability/LimitTheorems/TotalVariation/Basic.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Basic.lean))

### Equation (2.4) (`tv-definition`)

Status: **formalized**

- `LimitTheorems.totalVariation_eq_half_sum` ([SchubertForwardStability/LimitTheorems/TotalVariation/Basic.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Basic.lean))
- `LimitTheorems.totalVariation_eq_half_sum_support` ([SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean))

### Definition 2.5

Status: **stated**

- `LimitTheorems.identDistrib_iff_cdf` ([SchubertForwardStability/LimitTheorems/Convergence/Distribution.lean](../SchubertForwardStability/LimitTheorems/Convergence/Distribution.lean))

### Definition 2.6 (`def:sigma-generated`)

Status: **stated**

- `StrongMixing.generatedSigma` ([SchubertForwardStability/StrongMixing/Coefficients/Generated.lean](../SchubertForwardStability/StrongMixing/Coefficients/Generated.lean))
- `StrongMixing.comap_le_generatedSigma` ([SchubertForwardStability/StrongMixing/Coefficients/Generated.lean](../SchubertForwardStability/StrongMixing/Coefficients/Generated.lean))
- `StrongMixing.generatedSigma_fibers` ([SchubertForwardStability/StrongMixing/Coefficients/Atoms.lean](../SchubertForwardStability/StrongMixing/Coefficients/Atoms.lean))

### Definition 2.7 (`def:rosenblatt-alpha`)

Status: **stated**

- `StrongMixing.strongMixingCoeff` ([SchubertForwardStability/StrongMixing/Coefficients/Basic.lean](../SchubertForwardStability/StrongMixing/Coefficients/Basic.lean))
- `StrongMixing.mixingCoeff` ([SchubertForwardStability/StrongMixing/Coefficients/Basic.lean](../SchubertForwardStability/StrongMixing/Coefficients/Basic.lean))
- `StrongMixing.IsStrongMixing` ([SchubertForwardStability/StrongMixing/Coefficients/Basic.lean](../SchubertForwardStability/StrongMixing/Coefficients/Basic.lean))
- `StrongMixing.IsGeometricMixing` ([SchubertForwardStability/StrongMixing/Coefficients/Basic.lean](../SchubertForwardStability/StrongMixing/Coefficients/Basic.lean))
- `StrongMixing.finiteMixingCoeff` ([SchubertForwardStability/StrongMixing/Coefficients/Basic.lean](../SchubertForwardStability/StrongMixing/Coefficients/Basic.lean))
- `StrongMixing.finiteMixingCoeff_const_indep` ([SchubertForwardStability/StrongMixing/Coefficients/Extension.lean](../SchubertForwardStability/StrongMixing/Coefficients/Extension.lean))
- `StrongMixing.finiteMixingCoeff_eq_cuts` ([SchubertForwardStability/StrongMixing/Coefficients/Boundaries.lean](../SchubertForwardStability/StrongMixing/Coefficients/Boundaries.lean))
- `StrongMixing.constantExtension` ([SchubertForwardStability/StrongMixing/Coefficients/Generated.lean](../SchubertForwardStability/StrongMixing/Coefficients/Generated.lean))
- `StrongMixing.positiveExtension` ([SchubertForwardStability/StrongMixing/Coefficients/Extension.lean](../SchubertForwardStability/StrongMixing/Coefficients/Extension.lean))

### Lemma 3.1 (`lem:renyi_records`)

Status: **formalized**

Cited in the paper and proved here, from the independence of $d\_1(w),\ldots,d\_n(w)$, with $d\_j(w)$ uniform on $\lbrace 0,\ldots,j-1\rbrace$.

- `FinitaryPerm.iIndepFun_uniform_records` ([SchubertForwardStability/Permutations/Random/Records.lean](../SchubertForwardStability/Permutations/Random/Records.lean))
- `FinitaryPerm.uniform_record_probability` ([SchubertForwardStability/Permutations/Random/Records.lean](../SchubertForwardStability/Permutations/Random/Records.lean))
- `FinitaryPerm.integral_uniform_record` ([SchubertForwardStability/Permutations/Random/Records.lean](../SchubertForwardStability/Permutations/Random/Records.lean))

### Equation (3.2) (`eq:chi_marginals`)

Status: **formalized**

- `FinitaryPerm.uniform_nonRecord_zero` ([SchubertForwardStability/Permutations/Random/NonRecords.lean](../SchubertForwardStability/Permutations/Random/NonRecords.lean))
- `FinitaryPerm.integral_uniform_nonRecord` ([SchubertForwardStability/Permutations/Random/NonRecords.lean](../SchubertForwardStability/Permutations/Random/NonRecords.lean))

### Lemma 3.3 (`lem:Yi_expectation`)

Status: **formalized**

- `RecordStability.integral_uniform_walk` ([SchubertForwardStability/Paper/Uniform/Means.lean](../SchubertForwardStability/Paper/Uniform/Means.lean))

### Corollary 3.4 (`lem:prob_delta_i`)

Status: **formalized**

- `RecordStability.uniform_upward_probability` ([SchubertForwardStability/Paper/Uniform/Overshoot.lean](../SchubertForwardStability/Paper/Uniform/Overshoot.lean))

### Lemma 3.5 (`lem:max_bound`)

Status: **formalized**

- `RecordStability.integral_uniform_overshoot` ([SchubertForwardStability/Paper/Uniform/Overshoot.lean](../SchubertForwardStability/Paper/Uniform/Overshoot.lean))

### Proposition 3.6

Status: **formalized**

- `RecordStability.uniform_product_expectation` ([SchubertForwardStability/Paper/Uniform/Expectation.lean](../SchubertForwardStability/Paper/Uniform/Expectation.lean))
- `RecordStability.uniform_ambient_overshoot_limit` ([SchubertForwardStability/Paper/Uniform/Expectation.lean](../SchubertForwardStability/Paper/Uniform/Expectation.lean))
- `RecordStability.recordWalkMaxFrom` ([SchubertForwardStability/Paper/Walk/Tails.lean](../SchubertForwardStability/Paper/Walk/Tails.lean))
- `RecordStability.recordWalkExcess` ([SchubertForwardStability/Paper/Walk/Tails.lean](../SchubertForwardStability/Paper/Walk/Tails.lean))

### Proposition 3.7 (`prop:record_clt`)

Status: **formalized**

- `RecordStability.uniform_record_gaussian` ([SchubertForwardStability/Paper/Uniform/LogScale.lean](../SchubertForwardStability/Paper/Uniform/LogScale.lean))

### The Lyapunov central limit theorem for triangular arrays (Section 3)

Status: **formalized**

Cited in the paper and proved here, from Lindeberg's theorem for triangular arrays.

- `LimitTheorems.tendsto_charFun_prod_lindeberg` ([SchubertForwardStability/LimitTheorems/CentralLimit/Lindeberg.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/Lindeberg.lean))
- `LimitTheorems.tendstoInDistribution_lindeberg` ([SchubertForwardStability/LimitTheorems/CentralLimit/Lindeberg.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/Lindeberg.lean))
- `LimitTheorems.tendstoInDistribution_lindeberg_div` ([SchubertForwardStability/LimitTheorems/CentralLimit/Normalization.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/Normalization.lean))
- `LimitTheorems.tailSecond_le_third` ([SchubertForwardStability/LimitTheorems/CentralLimit/ThirdMomentTail.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/ThirdMomentTail.lean))
- `LimitTheorems.tendsto_tailSecond_third` ([SchubertForwardStability/LimitTheorems/CentralLimit/ThirdMomentTail.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/ThirdMomentTail.lean))
- `LimitTheorems.tendstoInDistribution_lyapunov` ([SchubertForwardStability/LimitTheorems/CentralLimit/Lyapunov.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/Lyapunov.lean))
- `LimitTheorems.tendstoInDistribution_sum_div` ([SchubertForwardStability/LimitTheorems/CentralLimit/Normalization.lean](../SchubertForwardStability/LimitTheorems/CentralLimit/Normalization.lean))

### Slutsky's theorem, the continuous mapping theorem and characteristic functions (Sections 3–4)

Status: **formalized**

Slutsky's theorem is proved here; the continuous mapping theorem and the results on characteristic functions are those of Mathlib.

- `LimitTheorems.tendstoInDistribution_of_sub` ([SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean](../SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean))
- `LimitTheorems.slutsky_prod` ([SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean](../SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean))
- `LimitTheorems.slutsky_continuous` ([SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean](../SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean))
- `LimitTheorems.slutsky_add` ([SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean](../SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean))
- `LimitTheorems.slutsky_mul` ([SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean](../SchubertForwardStability/LimitTheorems/Convergence/Slutsky.lean))
- `LimitTheorems.tendstoInDistribution_indep` ([SchubertForwardStability/LimitTheorems/Convergence/Independent.lean](../SchubertForwardStability/LimitTheorems/Convergence/Independent.lean))
- `MeasureTheory.TendstoInDistribution.continuous_comp`
- `MeasureTheory.Measure.ext_of_charFun`
- `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`

### Lemma 3.8 (`lemma:distY2`)

Status: **formalized**

The joint limit of the two record counts uses the weak continuity of products of probability measures instead of characteristic functions.

- `RecordStability.uniform_second_gaussian` ([SchubertForwardStability/Paper/Uniform/SecondGaussian.lean](../SchubertForwardStability/Paper/Uniform/SecondGaussian.lean))

### Equation (3.9) (`eq:Y2-records`)

Status: **formalized**

- `RecordStability.recordWalk_second` ([SchubertForwardStability/Paper/Walk/Tails.lean](../SchubertForwardStability/Paper/Walk/Tails.lean))

### Lemma 3.10 (`lemma:vanishingZn`)

Status: **formalized**

- `RecordStability.uniform_excess_vanishes` ([SchubertForwardStability/Paper/Uniform/Excess.lean](../SchubertForwardStability/Paper/Uniform/Excess.lean))

### Proposition 4.1 (`prop:grass_rec_uniform_exact`)

Status: **formalized**

- `FinitaryPerm.card_grassmannian` ([SchubertForwardStability/Permutations/Random/SubsetCounts.lean](../SchubertForwardStability/Permutations/Random/SubsetCounts.lean))
- `FinitaryPerm.grassmannian_record_probability` ([SchubertForwardStability/Permutations/Random/GrassRecordLaw.lean](../SchubertForwardStability/Permutations/Random/GrassRecordLaw.lean))

### The distribution $G\_n$ on Grassmannian permutations (Section 4.2)

Status: **stated**

- `FinitaryPerm.grassmannianLaw` ([SchubertForwardStability/Permutations/Random/Subsets.lean](../SchubertForwardStability/Permutations/Random/Subsets.lean))
- `FinitaryPerm.ae_mem_grassmannianLaw` ([SchubertForwardStability/Permutations/Random/PointMasses.lean](../SchubertForwardStability/Permutations/Random/PointMasses.lean))
- `FinitaryPerm.grassmannianLaw_singleton_one` ([SchubertForwardStability/Permutations/Random/PointMasses.lean](../SchubertForwardStability/Permutations/Random/PointMasses.lean))
- `FinitaryPerm.grassmannianLaw_singleton_encoded` ([SchubertForwardStability/Permutations/Random/PointMasses.lean](../SchubertForwardStability/Permutations/Random/PointMasses.lean))
- `FinitaryPerm.exists_grassmannianOfSubset` ([SchubertForwardStability/Permutations/Classes/GrassClassification.lean](../SchubertForwardStability/Permutations/Classes/GrassClassification.lean))
- `FinitaryPerm.grassmannianLaw_singleton_nonid` ([SchubertForwardStability/Permutations/Random/PointMasses.lean](../SchubertForwardStability/Permutations/Random/PointMasses.lean))
- `FinitaryPerm.grassmannianLaw_singleton` ([SchubertForwardStability/Permutations/Random/PointMasses.lean](../SchubertForwardStability/Permutations/Random/PointMasses.lean))
- `FinitaryPerm.grassmannianOfSubset` ([SchubertForwardStability/Permutations/Classes/Grassmannian.lean](../SchubertForwardStability/Permutations/Classes/Grassmannian.lean))
- `FinitaryPerm.subsetLaw` ([SchubertForwardStability/Permutations/Random/Subsets.lean](../SchubertForwardStability/Permutations/Random/Subsets.lean))
- `FinitaryPerm.subsetPermutation` ([SchubertForwardStability/Permutations/Random/Subsets.lean](../SchubertForwardStability/Permutations/Random/Subsets.lean))
- `RecordStability.grassmannianResidual` ([SchubertForwardStability/Paper/Grassmannian/Residual.lean](../SchubertForwardStability/Paper/Grassmannian/Residual.lean))

### Lemma 4.2 (`lem:grass_binomial_descent`)

Status: **formalized**

- `FinitaryPerm.subsetLaw_card_binomial` ([SchubertForwardStability/Permutations/Random/CardLaw.lean](../SchubertForwardStability/Permutations/Random/CardLaw.lean))

### Lemma 4.3 (`lem:grass_FS_equals_M`)

Status: **formalized**

- `RecordStability.subset_support_maximum` ([SchubertForwardStability/Paper/Grassmannian/Records.lean](../SchubertForwardStability/Paper/Grassmannian/Records.lean))

### Lemma 4.4 (`lem:grass_lambda`)

Status: **formalized**

- `RecordStability.subset_nonRecordsFrom` ([SchubertForwardStability/Paper/Grassmannian/Records.lean](../SchubertForwardStability/Paper/Grassmannian/Records.lean))
- `RecordStability.subset_recordWalkStep` ([SchubertForwardStability/Paper/Grassmannian/Records.lean](../SchubertForwardStability/Paper/Grassmannian/Records.lean))

### Lemma 4.5 (`lem:grass_path_shape`)

Status: **formalized**

- `RecordStability.subset_walk_shape` ([SchubertForwardStability/Paper/Grassmannian/Records.lean](../SchubertForwardStability/Paper/Grassmannian/Records.lean))

### Corollary 4.6 (`cor:grass_fs_value`)

Status: **formalized**

- `RecordStability.subset_productForwardStability` ([SchubertForwardStability/Paper/Grassmannian/Records.lean](../SchubertForwardStability/Paper/Grassmannian/Records.lean))

### Lemma 4.7 (`lem:grass_tail_bounds`)

Status: **formalized**

- `FinitaryPerm.subsetLaw_extreme_tails_eventually` ([SchubertForwardStability/Permutations/Random/ExtremeTails.lean](../SchubertForwardStability/Permutations/Random/ExtremeTails.lean))

### Optimal couplings, the binomial Chernoff bound and De Moivre's mean absolute deviation (Section 4)

Status: **formalized**

Cited in the paper and proved here.

- `LimitTheorems.exists_maximalCoupling` ([SchubertForwardStability/LimitTheorems/TotalVariation/Coupling.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Coupling.lean))
- `LimitTheorems.totalVariation_le_mismatch` ([SchubertForwardStability/LimitTheorems/TotalVariation/Coupling.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Coupling.lean))
- `LimitTheorems.productCoupling_mismatch_le` ([SchubertForwardStability/LimitTheorems/TotalVariation/Product.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Product.lean))
- `LimitTheorems.supportedCoupling_fst` ([SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean))
- `LimitTheorems.supportedCoupling_snd` ([SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean))
- `LimitTheorems.supportedCoupling_mismatch` ([SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean](../SchubertForwardStability/LimitTheorems/TotalVariation/Support.lean))
- `LimitTheorems.centralBinomial_error_isBigO` ([SchubertForwardStability/LimitTheorems/Binomial/CentralBinomial.lean](../SchubertForwardStability/LimitTheorems/Binomial/CentralBinomial.lean))
- `LimitTheorems.binomial_chernoff` ([SchubertForwardStability/LimitTheorems/Binomial/Chernoff.lean](../SchubertForwardStability/LimitTheorems/Binomial/Chernoff.lean))
- `LimitTheorems.binomial_deviation_mean` ([SchubertForwardStability/LimitTheorems/Binomial/Deviation.lean](../SchubertForwardStability/LimitTheorems/Binomial/Deviation.lean))
- `LimitTheorems.tendsto_binomial_gaussian` ([SchubertForwardStability/LimitTheorems/Binomial/Gaussian.lean](../SchubertForwardStability/LimitTheorems/Binomial/Gaussian.lean))
- `RecordStability.subset_card_joint_gaussian` ([SchubertForwardStability/Paper/Grassmannian/CardGaussian.lean](../SchubertForwardStability/Paper/Grassmannian/CardGaussian.lean))
- `RecordStability.subset_card_maximum_gaussian` ([SchubertForwardStability/Paper/Grassmannian/CardGaussian.lean](../SchubertForwardStability/Paper/Grassmannian/CardGaussian.lean))

### Proposition 4.8 (`prop:grass_fs_exact_prob`)

Status: **formalized**

- `RecordStability.grassmannian_residual_bounds` ([SchubertForwardStability/Paper/Grassmannian/ResidualMeans.lean](../SchubertForwardStability/Paper/Grassmannian/ResidualMeans.lean))

### Lemma 4.9 (`lem:expected_max`)

Status: **formalized**

- `FinitaryPerm.subsetLaw_maximum_mean` ([SchubertForwardStability/Permutations/Random/SubsetMeans.lean](../SchubertForwardStability/Permutations/Random/SubsetMeans.lean))

### Lemma 4.10 (`lem:expected_max_descent`)

Status: **formalized**

- `RecordStability.grassmannian_card_maximum_mean` ([SchubertForwardStability/Paper/Grassmannian/CardMean.lean](../SchubertForwardStability/Paper/Grassmannian/CardMean.lean))

### Proposition 4.11 (`prop:grass-exp`)

Status: **formalized**

- `RecordStability.grassmannian_encoded_expectation` ([SchubertForwardStability/Paper/Grassmannian/Expectation.lean](../SchubertForwardStability/Paper/Grassmannian/Expectation.lean))

### Proposition 4.12 (`prop:grass-dist`)

Status: **formalized**

- `RecordStability.grassmannian_encoded_gaussian` ([SchubertForwardStability/Paper/Grassmannian/ProductGaussian.lean](../SchubertForwardStability/Paper/Grassmannian/ProductGaussian.lean))

### Lemma 4.13 (`lem:grass_TV_single`)

Status: **formalized**

- `RecordStability.grassmannian_totalVariation` ([SchubertForwardStability/Paper/Grassmannian/TotalVariation.lean](../SchubertForwardStability/Paper/Grassmannian/TotalVariation.lean))
- `RecordStability.grassmannian_totalVariation_le` ([SchubertForwardStability/Paper/Grassmannian/TotalVariation.lean](../SchubertForwardStability/Paper/Grassmannian/TotalVariation.lean))

### Reduced words of Boolean permutations (Section 5)

Status: **formalized**

Cited in the paper and proved here.

- `FinitaryPerm.IsBoolean.reducedWord_nodup` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanSupport.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanSupport.lean))
- `FinitaryPerm.reducedWord_toFinset_eq` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanSupport.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanSupport.lean))
- `FinitaryPerm.IsBoolean.reducedWord_commutations` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanCommutations.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanCommutations.lean))
- `FinitaryPerm.IsBoolean.eq_lexFirst_iff` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanNormal.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanNormal.lean))
- `FinitaryPerm.IsBoolean.blockNormalForm` ([SchubertForwardStability/Permutations/Classes/Intervals/BlockAscending.lean](../SchubertForwardStability/Permutations/Classes/Intervals/BlockAscending.lean))

### Equation (5.1) (`eq:bool-cardinality`)

Status: **formalized**

Cited in the paper and proved here, from Lemma 5.4 and $\lvert\mathcal{T}\_{n-1}\rvert=F\_{2n-1}$.

- `FinitaryPerm.card_boolean_int_fib` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanCounts.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanCounts.lean))

### Remark 5.2 (`def:cont-comm-inv`)

Status: **formalized**

Stated for every permutation, not only for Boolean ones.

- `FinitaryPerm.not_hasCommutingInversion_lexFirst` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanLex.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanLex.lean))
- `FinitaryPerm.lexFirstReducedWord` ([SchubertForwardStability/Permutations/Classes/LexWord.lean](../SchubertForwardStability/Permutations/Classes/LexWord.lean))

### Definition 5.3 (`def:block-tag-word`)

Status: **stated**

- `FinitaryPerm.IsTagWord` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.GeneratorPresent` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.GeneratorContinues` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.blockTag` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.isTagWord_local_iff` ([SchubertForwardStability/Permutations/Classes/Tags/TagDefinition.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagDefinition.lean))
- `FinitaryPerm.blockTag_outside` ([SchubertForwardStability/Permutations/Classes/Tags/TagDefinition.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagDefinition.lean))
- `FinitaryPerm.tagWords` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))

### Lemma 5.4 (`lem:block-boundary-encoding`)

Status: **formalized**

The proof identifies the tags through the order of $s\_t$ and $s\_{t-1}$ in a reduced word, instead of through the lexicographically first reduced word.

- `FinitaryPerm.booleanTags_bijOn` ([SchubertForwardStability/Permutations/Classes/Tags/TagRecovery.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagRecovery.lean))

### Lemma 5.5 (`lem:chi-as-local`)

Status: **formalized**

The proof is by induction on $n$, writing $w$ as $w'$, $w's\_{n-1}$ or $s\_{n-1}w'$, instead of by a case analysis of the reduced word.

- `FinitaryPerm.boolean_nonRecord_local` ([SchubertForwardStability/Permutations/Classes/Tags/TagRecords.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagRecords.lean))

### Lemma 5.6 (`lem:bool-rec-recurrence`)

Status: **formalized**

- `FinitaryPerm.boolean_record_factor_unique` ([SchubertForwardStability/Permutations/Classes/Intervals/RecordFactors.lean](../SchubertForwardStability/Permutations/Classes/Intervals/RecordFactors.lean))
- `FinitaryPerm.booleanBoundaryOne_bijOn` ([SchubertForwardStability/Permutations/Classes/Intervals/BoundaryBijections.lean](../SchubertForwardStability/Permutations/Classes/Intervals/BoundaryBijections.lean))
- `FinitaryPerm.booleanBoundaryTwo_bijOn` ([SchubertForwardStability/Permutations/Classes/Intervals/BoundaryBijections.lean](../SchubertForwardStability/Permutations/Classes/Intervals/BoundaryBijections.lean))

### Example 5.7

Status: **formalized**

- `RecordStability.booleanBoundaryOne_five` ([SchubertForwardStability/Paper/Boolean/Examples.lean](../SchubertForwardStability/Paper/Boolean/Examples.lean))
- `RecordStability.booleanBoundaryTwo_five` ([SchubertForwardStability/Paper/Boolean/Examples.lean](../SchubertForwardStability/Paper/Boolean/Examples.lean))

### Corollary 5.8 (`cor:Nnj-fib`)

Status: **formalized**

- `FinitaryPerm.booleanRecordCount_fib_product` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibProduct.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibProduct.lean))
- `FinitaryPerm.booleanOn` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))
- `FinitaryPerm.positionInterval` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))
- `FinitaryPerm.booleanRecordFiber` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))
- `FinitaryPerm.booleanRecordCount` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))
- `FinitaryPerm.booleanBoundaryOne` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))
- `FinitaryPerm.booleanBoundaryTwo` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanRecords.lean))

### Equation (5.10) (`eq:tagiuri-vajda`)

Status: **formalized**

Cited in the paper and proved here, from Cassini's identity and the addition formula.

- `Int.fib_vajda` ([SchubertForwardStability/Permutations/ForMathlib/FibIdentities.lean](../SchubertForwardStability/Permutations/ForMathlib/FibIdentities.lean))

### Lemma 5.11 (`lem:fib-identity`)

Status: **formalized**

- `Int.fib_add_one_mul` ([SchubertForwardStability/Permutations/ForMathlib/FibIdentities.lean](../SchubertForwardStability/Permutations/ForMathlib/FibIdentities.lean))

### Proposition 5.13 (`prop:two-expressions`)

Status: **formalized**

- `FinitaryPerm.boolean_fib_expressions` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean))
- `FinitaryPerm.boolean_fib_intermediate` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean))

### Equation (5.14) (`eq:intermediateFibIdent`)

Status: **formalized**

- `FinitaryPerm.boolean_fib_intermediate` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean))

### Theorem 5.15 (`thm:Nnj-recurrence`)

Status: **formalized**

- `FinitaryPerm.booleanRecordCount_fib` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanFibSimplify.lean))

### Equation (5.16) (`eq:Nnj-exact`)

Status: **formalized**

- `FinitaryPerm.booleanRecordCount_golden` ([SchubertForwardStability/Permutations/Classes/Boolean/BooleanGolden.lean](../SchubertForwardStability/Permutations/Classes/Boolean/BooleanGolden.lean))
- `Real.signed_binet` ([SchubertForwardStability/Permutations/ForMathlib/FibGolden.lean](../SchubertForwardStability/Permutations/ForMathlib/FibGolden.lean))

### Equation (5.17) (`eq:bool-rec-prob-phi`)

Status: **formalized**

- `FinitaryPerm.boolean_record_probability_fib` ([SchubertForwardStability/Permutations/Random/BooleanRecords.lean](../SchubertForwardStability/Permutations/Random/BooleanRecords.lean))
- `FinitaryPerm.boolean_record_probability_golden` ([SchubertForwardStability/Permutations/Random/BooleanRecords.lean](../SchubertForwardStability/Permutations/Random/BooleanRecords.lean))

### Lemma 5.18 (`lem:alpha-factor`)

Status: **formalized**

Bradley's inequality, used for part (ii), is cited in the paper and proved here; parts (ii) and (iii) hold on every probability space.

- `StrongMixing.finiteMixingCoeff_comp_le` ([SchubertForwardStability/StrongMixing/Coefficients/CoefficientBounds.lean](../SchubertForwardStability/StrongMixing/Coefficients/CoefficientBounds.lean))
- `StrongMixing.finiteMixingCoeff_pair_le` ([SchubertForwardStability/StrongMixing/Coefficients/IndependentRows.lean](../SchubertForwardStability/StrongMixing/Coefficients/IndependentRows.lean))
- `StrongMixing.finiteMixingCoeff_pair_noise_eq` ([SchubertForwardStability/StrongMixing/Coefficients/IndependentRows.lean](../SchubertForwardStability/StrongMixing/Coefficients/IndependentRows.lean))

### Definition 5.19 (`def:extension-counts`)

Status: **formalized**

- `FinitaryPerm.card_tagExtensions` ([SchubertForwardStability/Permutations/Classes/Tags/TagExtensions.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagExtensions.lean))
- `FinitaryPerm.tagExtensions` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.extensionCount` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))

### Lemma 5.20 (`lem:transfer-matrix`)

Status: **formalized**

- `FinitaryPerm.extensionCount_zero` ([SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Classes/Tags/BlockTags.lean))
- `FinitaryPerm.extensionCount_false_succ` ([SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean))
- `FinitaryPerm.extensionCount_true_succ` ([SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean))
- `FinitaryPerm.extensionCount_false_fib` ([SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean))
- `FinitaryPerm.extensionCount_true_fib` ([SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean](../SchubertForwardStability/Permutations/Classes/Tags/TagCounts.lean))

### Lemma 5.21 (`lem:state-markov`)

Status: **formalized**

- `FinitaryPerm.tagLaw_conditional_next` ([SchubertForwardStability/Permutations/Random/Tags/TagMarkov.lean](../SchubertForwardStability/Permutations/Random/Tags/TagMarkov.lean))
- `FinitaryPerm.tagHistory_forced` ([SchubertForwardStability/Permutations/Random/Tags/TagResidual.lean](../SchubertForwardStability/Permutations/Random/Tags/TagResidual.lean))
- `FinitaryPerm.tagLaw_conditional_choices` ([SchubertForwardStability/Permutations/Random/Tags/TagResidual.lean](../SchubertForwardStability/Permutations/Random/Tags/TagResidual.lean))
- `FinitaryPerm.tagLaw` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.tagPresence` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.presenceHistory` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.tagKernel` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))

### Remark 5.22 (`rem:boolean-sampling`)

Status: **formalized**

The sampler is written as a program that counts its steps, where each arithmetic operation, memory access and choice among at most three outcomes with integer weights is one step, whatever the size of the numbers. Its output is uniform on $\mathcal{B}\_n$, and every run uses at most $16n$ steps.

- `RecordStability.boolean_sampler_linear` ([SchubertForwardStability/Paper/Boolean/SamplerCost.lean](../SchubertForwardStability/Paper/Boolean/SamplerCost.lean))
- `RecordStability.booleanSampler_law` ([SchubertForwardStability/Paper/Boolean/SamplerCost.lean](../SchubertForwardStability/Paper/Boolean/SamplerCost.lean))
- `RecordStability.booleanSampler_steps_le` ([SchubertForwardStability/Paper/Boolean/SamplerCost.lean](../SchubertForwardStability/Paper/Boolean/SamplerCost.lean))
- `RecordStability.booleanSampler` ([SchubertForwardStability/Paper/Boolean/SamplerCost.lean](../SchubertForwardStability/Paper/Boolean/SamplerCost.lean))
- `FinitaryPerm.tagSuffixSampler_uniform` ([SchubertForwardStability/Permutations/Random/Tags/TagSampler.lean](../SchubertForwardStability/Permutations/Random/Tags/TagSampler.lean))
- `FinitaryPerm.map_tagSuffixSampler_uniform` ([SchubertForwardStability/Permutations/Random/Tags/SamplerLaw.lean](../SchubertForwardStability/Permutations/Random/Tags/SamplerLaw.lean))
- `FinitaryPerm.freeTagPositions` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.applyTagKernels` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.tagChoicePMF` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))
- `FinitaryPerm.tagSuffixSampler` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))

### Lemma 5.23 (`lem:dobrushin`)

Status: **formalized**

- `FinitaryPerm.tagDobrushin_le` ([SchubertForwardStability/Permutations/Random/Tags/TagKernel.lean](../SchubertForwardStability/Permutations/Random/Tags/TagKernel.lean))
- `FinitaryPerm.applyTagKernels_contract` ([SchubertForwardStability/Permutations/Random/Tags/TagContraction.lean](../SchubertForwardStability/Permutations/Random/Tags/TagContraction.lean))
- `FinitaryPerm.tagDobrushin` ([SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean](../SchubertForwardStability/Permutations/Random/Tags/BlockTags.lean))

### Proposition 5.24 (`prop:boolean-strong-mixing`)

Status: **formalized**

The proof bounds the mixing coefficients of the tag sequence directly, by conditioning on its prefixes, instead of through the presence chain.

- `RecordStability.finiteMixingCoeff_boolean_le` ([SchubertForwardStability/Paper/Boolean/BooleanCoefficients.lean](../SchubertForwardStability/Paper/Boolean/BooleanCoefficients.lean))
- `RecordStability.centeredBooleanStep` ([SchubertForwardStability/Paper/Boolean/Means.lean](../SchubertForwardStability/Paper/Boolean/Means.lean))

### Lemma 5.25 (`lem:mpr-block`)

Status: **formalized**

Cited in the paper and proved here, from the Laplace-transform estimate of Merlevède, Peligrad and Rio; the same bound for the upper tail, and the two-sided bound with a factor $2$, are proved as well.

- `StrongMixing.mpr_positive_lower_tail` ([SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean))
- `StrongMixing.mpr_positive_two_sided` ([SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean))
- `StrongMixing.mpr_positive_laplace_le` ([SchubertForwardStability/StrongMixing/Bernstein/MPRPositive.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRPositive.lean))
- `StrongMixing.mpr_positive_upper_tail` ([SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean))
- `StrongMixing.mprTailConstant` ([SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean))
- `StrongMixing.mprTailConstant_pos` ([SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRTails.lean))
- `StrongMixing.peelingMprConstants_pos` ([SchubertForwardStability/StrongMixing/Bernstein/PeelingConstants.lean](../SchubertForwardStability/StrongMixing/Bernstein/PeelingConstants.lean))
- `StrongMixing.positiveSum` ([SchubertForwardStability/StrongMixing/Bernstein/MPRPositive.lean](../SchubertForwardStability/StrongMixing/Bernstein/MPRPositive.lean))

### Lemma 5.27 (`lem:bool-uniform-drift`)

Status: **formalized**

- `RecordStability.boolean_uniform_drift` ([SchubertForwardStability/Paper/Boolean/Drift.lean](../SchubertForwardStability/Paper/Boolean/Drift.lean))
- `RecordStability.boolean_drift_expression` ([SchubertForwardStability/Paper/Boolean/Drift.lean](../SchubertForwardStability/Paper/Boolean/Drift.lean))

### Equation (5.28) (`eq:bool-uniform-drift-expr`)

Status: **formalized**

- `RecordStability.boolean_drift_expression` ([SchubertForwardStability/Paper/Boolean/Drift.lean](../SchubertForwardStability/Paper/Boolean/Drift.lean))

### Lemma 5.29 (`lem:bool-terminal`)

Status: **formalized**

- `RecordStability.booleanMeanMax_eq_last` ([SchubertForwardStability/Paper/Boolean/Terminal.lean](../SchubertForwardStability/Paper/Boolean/Terminal.lean))
- `RecordStability.booleanMeanWalk_last` ([SchubertForwardStability/Paper/Boolean/Terminal.lean](../SchubertForwardStability/Paper/Boolean/Terminal.lean))
- `RecordStability.booleanMeanMax_sub_bigO` ([SchubertForwardStability/Paper/Boolean/Terminal.lean](../SchubertForwardStability/Paper/Boolean/Terminal.lean))

### Lemma 5.30 (`lem:boolean-fs-lower`)

Status: **formalized**

- `RecordStability.boolean_stability_lower` ([SchubertForwardStability/Paper/Boolean/StabilityLower.lean](../SchubertForwardStability/Paper/Boolean/StabilityLower.lean))

### Equation (6.1) (`eq:bs-fs`)

Status: **formalized**

The proof uses the $w\_0$-symmetry of the structure constants and the forward formula (1.2), instead of Hardt–Wallach's Theorem 1.3.

- `SchubertPolynomial.productBackStability_add_eq_max` ([SchubertForwardStability/SchubertPolynomials/Backward/Identity.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Identity.lean))
- `SchubertPolynomial.productBackStability_eq_sub` ([SchubertForwardStability/SchubertPolynomials/Backward/Identity.lean](../SchubertForwardStability/SchubertPolynomials/Backward/Identity.lean))

### Conjugation by $w\_0$ preserves the three families (Section 6)

Status: **formalized**

Cited in the paper and proved here.

- `FinitaryPerm.longest_class_law` ([SchubertForwardStability/Permutations/Random/LongestLaw.lean](../SchubertForwardStability/Permutations/Random/LongestLaw.lean))

### The $w\_0$-symmetry of the structure constants (Section 6)

Status: **formalized**

Proved here by the substitution $x\_i\mapsto -x\_{n+1-i}$; it gives Li's identity and the formula for $\mathrm{BS}$.

- `SchubertPolynomial.structureConst_conjugate_longest` ([SchubertForwardStability/SchubertPolynomials/Coinvariants/LongestProducts.lean](../SchubertForwardStability/SchubertPolynomials/Coinvariants/LongestProducts.lean))

### Corollary 6.2

Status: **formalized**

- `RecordStability.backward_identDistrib` ([SchubertForwardStability/Paper/Backward/Law.lean](../SchubertForwardStability/Paper/Backward/Law.lean))
- `RecordStability.backward_identDistrib_comp` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.recordWalkMaxAt_eq_max` ([SchubertForwardStability/Paper/Uniform/MaximumGap.lean](../SchubertForwardStability/Paper/Uniform/MaximumGap.lean))
- `FinitaryPerm.longest_class_law` ([SchubertForwardStability/Permutations/Random/LongestLaw.lean](../SchubertForwardStability/Permutations/Random/LongestLaw.lean))

### Equation (6.3) (`eq:bs-distribution`)

Status: **formalized**

- `RecordStability.backward_identDistrib` ([SchubertForwardStability/Paper/Backward/Law.lean](../SchubertForwardStability/Paper/Backward/Law.lean))
- `RecordStability.recordWalkMaxAt_eq_max` ([SchubertForwardStability/Paper/Uniform/MaximumGap.lean](../SchubertForwardStability/Paper/Uniform/MaximumGap.lean))

### Corollary 6.4 (`cor:backward-asymptotics`)

Status: **formalized**

- `RecordStability.backward_asymptotics` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.backward_expectation` ([SchubertForwardStability/Paper/Backward/Law.lean](../SchubertForwardStability/Paper/Backward/Law.lean))
- `RecordStability.uniform_backward_expectation` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.uniform_backward_gaussian` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.grassmannian_backward_expectation` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.grassmannian_backward_gaussian` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.boolean_backward_expectation` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))
- `RecordStability.integral_uniform_deficit_le` ([SchubertForwardStability/Paper/Backward/ClippedUniform.lean](../SchubertForwardStability/Paper/Backward/ClippedUniform.lean))
- `RecordStability.grassmannian_product_lt_tail` ([SchubertForwardStability/Paper/Backward/ClippedGrassmannian.lean](../SchubertForwardStability/Paper/Backward/ClippedGrassmannian.lean))
- `RecordStability.integral_boolean_deficit_le` ([SchubertForwardStability/Paper/Backward/ClippedBoolean.lean](../SchubertForwardStability/Paper/Backward/ClippedBoolean.lean))
- `RecordStability.integral_backward_eq` ([SchubertForwardStability/Paper/Backward/Asymptotics.lean](../SchubertForwardStability/Paper/Backward/Asymptotics.lean))

### Definition 7.1

Status: **stated**

- `PermutationPattern.Contains` ([SchubertForwardStability/Permutations/Classes/Patterns.lean](../SchubertForwardStability/Permutations/Classes/Patterns.lean))
- `PermutationPattern.avoiding` ([SchubertForwardStability/Permutations/Classes/Patterns.lean](../SchubertForwardStability/Permutations/Classes/Patterns.lean))
- `PermutationPattern.avoidingMany` ([SchubertForwardStability/Permutations/Classes/Patterns.lean](../SchubertForwardStability/Permutations/Classes/Patterns.lean))
- `PermutationPattern` ([SchubertForwardStability/Permutations/Classes/Patterns.lean](../SchubertForwardStability/Permutations/Classes/Patterns.lean))

### Definition 7.2

Status: **stated**

- `FinitaryPerm.coGrassmannian` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))
- `FinitaryPerm.mem_coGrassmannian` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))

### Definition 7.3

Status: **stated**

- `FinitaryPerm.fireworks` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))
- `FinitaryPerm.mem_fireworks` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))

### Definition 7.4

Status: **stated**

The geometric definition and its equivalence with $\mathrm{Av}\_n(3412,4231)$ are not formalized.

- `FinitaryPerm.smooth` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))

### Definition 7.5

Status: **stated**

- `FinitaryPerm.vexillary` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))
- `FinitaryPerm.covexillary` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))

### Definition 7.6

Status: **stated**

Here $\mathrm{Lev}\_n$ is defined by the criterion that $w\_0(I(w))\\,w$ is Boolean; the geometric definition is not formalized.

- `FinitaryPerm.leviSpherical` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))
- `FinitaryPerm.mem_leviSpherical` ([SchubertForwardStability/Permutations/Classes/PatternFamilies.lean](../SchubertForwardStability/Permutations/Classes/PatternFamilies.lean))

### Conjecture 7.7 (`conj:fs-rdense`)

Status: **stated**

- `RecordStability.RecordDenseRegime` ([SchubertForwardStability/Paper/Conjectures.lean](../SchubertForwardStability/Paper/Conjectures.lean))

### Conjecture 7.8 (`conj:fs-rint`)

Status: **stated**

- `RecordStability.RecordIntermediateRegime` ([SchubertForwardStability/Paper/Conjectures.lean](../SchubertForwardStability/Paper/Conjectures.lean))

### Conjecture 7.9 (`conj:fs-rsparse`)

Status: **stated**

Part (d) also includes $\mathbb{E}\[\mathrm{FS}(u,v)\]\le 2n$ for large $n$, which always holds.

- `RecordStability.RecordSparseRegime` ([SchubertForwardStability/Paper/Conjectures.lean](../SchubertForwardStability/Paper/Conjectures.lean))

### Proposition 8.1 (`prop:132-231-record-set-count`)

Status: **formalized**

- `PermutationPattern.recordFiberCard_gapProduct` ([SchubertForwardStability/Permutations/Classes/Patterns/CatalanFibers.lean](../SchubertForwardStability/Permutations/Classes/Patterns/CatalanFibers.lean))
- `PermutationPattern.recordFiber` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))
- `PermutationPattern.recordFiberCard` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))
- `PermutationPattern.nextRecord` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))
- `PermutationPattern.recordGapProduct` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))

### Equation (8.3) (`eq:231-split-rev`)

Status: **formalized**

- `PermutationPattern.avoiding231_split` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternSplit.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternSplit.lean))

### Equation (8.4) (`eq:record-recursion-rev`)

Status: **formalized**

- `PermutationPattern.recordFiber_recursion` ([SchubertForwardStability/Permutations/Classes/Patterns/RecordFiberRecursion.lean](../SchubertForwardStability/Permutations/Classes/Patterns/RecordFiberRecursion.lean))

### Catalan counts of $\mathrm{Av}\_m(231)$ and $\mathrm{Av}\_m(132)$ (Section 8)

Status: **formalized**

Cited in the paper and proved here, by splitting at the position of the maximum.

- `PermutationPattern.card_avoiding231_catalan` ([SchubertForwardStability/Permutations/Classes/Patterns/CatalanCounts.lean](../SchubertForwardStability/Permutations/Classes/Patterns/CatalanCounts.lean))
- `PermutationPattern.card_avoiding132_catalan` ([SchubertForwardStability/Permutations/Classes/Patterns/CatalanCounts.lean](../SchubertForwardStability/Permutations/Classes/Patterns/CatalanCounts.lean))
- `PermutationPattern.avoiding231_reverse_bij` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternReversal.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternReversal.lean))

### Corollary 8.5 (`cor:132-231-record-eqdist`)

Status: **formalized**

- `PermutationPattern.recordFiberCard_catalan_eq` ([SchubertForwardStability/Permutations/Classes/Patterns/CatalanEquidistribution.lean](../SchubertForwardStability/Permutations/Classes/Patterns/CatalanEquidistribution.lean))

### Corollary 8.6 (`cor:132-231-record-eqdist-prob`)

Status: **formalized**

- `RecordStability.catalan_record_law` ([SchubertForwardStability/Paper/Catalan/RecordLaws.lean](../SchubertForwardStability/Paper/Catalan/RecordLaws.lean))

### Corollary 8.7 (`cor:132-231-fs-eqdist`)

Status: **formalized**

- `RecordStability.catalan_stability_law` ([SchubertForwardStability/Paper/Catalan/Stability.lean](../SchubertForwardStability/Paper/Catalan/Stability.lean))
- `FinitaryPerm.nonRecordBound_eq` ([SchubertForwardStability/Permutations/Statistics/RecordBound.lean](../SchubertForwardStability/Permutations/Statistics/RecordBound.lean))

### Definition 8.8

Status: **stated**

- `PermutationPattern.RecordEquivalent` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))

### Definition 8.9

Status: **stated**

- `PermutationPattern.deletionMinor` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))
- `PermutationPattern.deletionMinor_lt_iff` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))
- `PermutationPattern.maximumPosition` ([SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean](../SchubertForwardStability/Permutations/Classes/Patterns/PatternRecords.lean))

### Conjecture 8.10 (`conj:record-equivalence-recursive`)

Status: **stated**

- `RecordStability.RecursiveRecordEquivalence` ([SchubertForwardStability/Paper/Conjectures.lean](../SchubertForwardStability/Paper/Conjectures.lean))
