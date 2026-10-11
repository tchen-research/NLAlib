# Coverage of Approximation Theory and Approximation Practice, Extended Edition (`trefethen19`)

Indexed from the extracted text of an ATAP PDF supplied as the 2013 SIAM edition (its pages carry the draft date January 30, 2018). The atlas source `trefethen19` is the 2019 Extended Edition, whose Chapters 1–28 have the same chapter, theorem and exercise numbering; the Extended Edition's added chapters are not indexed. Page numbers are those of this PDF and may be off by a few pages in the 2019 print. The book has 41 numbered theorems (no lemmas, corollaries or numbered definitions; Chapters 1, 2, 13, 14, 26 and 28 state no theorem). Unnumbered definitions from the prose are labelled `Def <chapter> (<name>)`. Exercises are indexed only when they state a named classical result (orthogonality, Bernstein polynomials, Fejér, Bernstein's inequality and theorem, de la Vallée Poussin, Chebyshev monic minimality, …).

Legend: ✓ in NLAlib · ◐ partially in NLAlib · M in Mathlib (not an atlas result by policy) · ○ candidate (to add) · – out of scope

| status | count |
|---|---|
| ✓ nlalib | 8 |
| ◐ partial | 8 |
| M mathlib | 11 |
| ○ candidate | 34 |
| – out-of-scope | 27 |
| total | 88 |

## Chapter 2  (✓ 2 · M 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 2 (Chebyshev points) | **Chebyshev points.** For $n\ge1$ the $(n+1)$-point Chebyshev grid is $x_j=\cos(j\pi/n)$, $0\le j\le n$ (the extrema of $T_n$; real parts of the $2n$th roots of unity). | M mathlib | `Mathlib:Polynomial.Chebyshev.node`, `Mathlib:Polynomial.Chebyshev.eval_T_real_node`, `Mathlib:Polynomial.Chebyshev.strictAntiOn_node` | NLAlib uses Mathlib's `node` for its Chebyshev interpolant. |
| Def 2 (Chebyshev interpolant) | **Chebyshev interpolant.** The Chebyshev interpolant $p_n\in\mathcal P_n$ of $f$ is the unique polynomial of degree at most $n$ agreeing with $f$ at the $n+1$ Chebyshev points. | ✓ nlalib | `chebyshev-approx-analytic` `NLAlib.chebyshevAnalyticInterpolant`, `NLAlib.eval_chebyshevAnalyticInterpolant_node`, `NLAlib.degree_chebyshevAnalyticInterpolant_le` | Defined as Mathlib `Lagrange.interpolate` on `Polynomial.Chebyshev.node`; the name says 'Analytic' but the definition takes any `F : ℂ → ℂ`. |
| Ex 2.4 | **Chebyshev points of the first kind.** The first-kind (Gauss–Chebyshev) points are $x_j=\cos((j+\tfrac12)\pi/(n+1))$, $0\le j\le n$, the zeros of $T_{n+1}$. | ✓ nlalib | `chebyshev-interpolation-error` `NLAlib.chebyshevZero`, `NLAlib.eval_T_real_chebyshevZero`, `NLAlib.chebyshevZero_injective` | Indexed as a named definition stated in an exercise. |

## Chapter 3  (◐ 2 · M 3 · ○ 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 3 (Chebyshev polynomials) | **Chebyshev polynomials.** $T_k(x)=\operatorname{Re} z^k=\cos(k\theta)$ for $x=\cos\theta=(z+z^{-1})/2$; they satisfy $T_{k+1}=2xT_k-T_{k-1}$, so $T_k$ has degree $k$ and leading coefficient $2^{k-1}$, and $|T_k|\le1$ on $[-1,1]$. | M mathlib | `Mathlib:Polynomial.Chebyshev.T`, `Mathlib:Polynomial.Chebyshev.T_real_cos`, `Mathlib:Polynomial.Chebyshev.T_add_two` |  |
| Thm 3.1 | **Chebyshev series.** A Lipschitz continuous $f$ on $[-1,1]$ has a unique absolutely and uniformly convergent expansion $f=\sum_k a_kT_k$, with $a_k=\tfrac2\pi\int_{-1}^1 f(x)T_k(x)(1-x^2)^{-1/2}dx$ for $k\ge1$ and $\tfrac1\pi$ in place of $\tfrac2\pi$ for $k=0$. | ◐ partial | `chebyshev-approx-analytic`, `chebyshev-series-convergence` `NLAlib.hasSum_chebyshevAnalyticCoeff_mul_eval_T_of_open_ellipse`, `NLAlib.chebyshevComplexCoeff_eq_fourierCoeff` | NLAlib proves pointwise convergence of the Chebyshev series only for $f$ bounded and holomorphic on an open Bernstein ellipse; the Lipschitz case, absolute/uniform convergence, uniqueness and the weighted-integral formula (3.12) are missing (atlas candidate `chebyshev-series-convergence`). |
| Def 3 (Chebyshev coefficients) | **Chebyshev coefficients and series.** The Chebyshev coefficients $a_k$ of $f$ are given by the weighted integrals (3.12), equivalently the cosine coefficients of $f(\cos\theta)$ or the Laurent coefficients of $f((z+z^{-1})/2)$ on $|z|=1$. | ◐ partial | `chebyshev-coefficients-def` `NLAlib.chebyshevComplexCoeff`, `NLAlib.chebyshevAnalyticCoeff`, `NLAlib.chebyshevComplexCoeff_eq_fourierCoeff` | The contour/Fourier definition exists (it only reads values on $[-1,1]$); the weighted-integral form, linearity, exactness on polynomials and $|a_k|\le2\|f\|$ (atlas candidate `chebyshev-coefficients-def`) are not stated. |
| Ex 3.6 | **Chebyshev series of sign(x) and |x| (Bernstein 1914).** For $\operatorname{sign}(x)$: $a_k=0$ for even $k$ and $a_k=\tfrac4\pi\tfrac{(-1)^{(k-1)/2}}{k}$ for odd $k$; for $|x|$: $a_0=2/\pi$, $a_k=0$ for odd $k$, $a_k=\tfrac4\pi\tfrac{(-1)^{k/2}}{1-k^2}$ for even $k\ge2$. | ○ candidate | `chebyshev-series-abs-sign` | Proposed candidate `chebyshev-series-abs-sign` (trefethen19.candidates.json). The extracted text reads $(-1)^{k-1}$ for the sign coefficients, which is constant for odd $k$; the correct factor is $(-1)^{(k-1)/2}$. Check the print before citing. |
| Ex 3.7 | **Orthogonality of Chebyshev polynomials.** $\int_{-1}^1 T_jT_k(1-x^2)^{-1/2}dx=0$ for $j\ne k$, $=\pi$ for $j=k=0$ and $\pi/2$ for $j=k\ge1$. | M mathlib | `Mathlib:Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`, `Mathlib:Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero`, `Mathlib:Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero` |  |
| Ex 3.12 | **Extrema and roots of Chebyshev polynomials.** $T_n$ has the $n$ simple roots $\cos((2k+1)\pi/(2n))$ and attains $\pm1$ on $[-1,1]$ exactly at $\cos(k\pi/n)$, $0\le k\le n$. | M mathlib | `Mathlib:Polynomial.Chebyshev.roots_T_real`, `Mathlib:Polynomial.Chebyshev.roots_T_real_nodup`, `Mathlib:Polynomial.Chebyshev.isExtrOn_T_real_iff` |  |
| Ex 3.15 | **Chebyshev series of e^{ax}.** $e^{ax}=2\sum_{k\ge0}{}' I_k(a)T_k(x)$ (first term halved), with $I_k$ the modified Bessel function of the first kind. | ○ candidate | `chebyshev-series-exp-bessel` | Proposed candidate `chebyshev-series-exp-bessel` (trefethen19.candidates.json). Mathlib has no modified Bessel functions $I_k$. |

## Chapter 4  (✓ 1 · ◐ 2 · ○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 4 (Chebyshev projection) | **Chebyshev projection (truncation).** The degree-$n$ Chebyshev projection of $f$ is $f_n=\sum_{k=0}^n a_kT_k$, the truncation of its Chebyshev series. | ◐ partial | `chebyshev-approx-analytic`, `chebyshev-coefficients-def` `NLAlib.chebyshevAnalyticTrunc`, `NLAlib.degree_chebyshevAnalyticTrunc_le` | The truncation is defined from the contour coefficients; its basic API (projection property $p_n=p$ for $\deg p\le n$, linearity) is part of the candidate `chebyshev-coefficients-def`. |
| Thm 4.1 | **Aliasing of Chebyshev polynomials.** For $n\ge1$, on the $(n+1)$-point Chebyshev grid $T_k$ takes the same values as $T_m$ with $m=|(k+n-1)\bmod 2n-(n-1)|\in[0,n]$; equivalently $T_m,T_{2n\pm m},T_{4n\pm m},\dots$ agree on the grid. | ✓ nlalib | `chebyshev-approx-analytic`, `chebyshev-aliasing` `NLAlib.eval_T_node_eq_eval_T_alias`, `NLAlib.chebyshevAliasIndex`, `NLAlib.chebyshevAliasIndex_le` | Proved as a helper of `chebyshev-approx-analytic` with the fold `min(k mod 2n, 2n − k mod 2n)`, which equals the book's index; the atlas entry `chebyshev-aliasing` is still marked candidate and should record this. |
| Thm 4.2 | **Aliasing formula for Chebyshev coefficients.** For Lipschitz $f$ with coefficients $a_k$ and Chebyshev interpolant $p_n$ ($n\ge1$) with coefficients $c_k$: $c_0=a_0+a_{2n}+a_{4n}+\cdots$, $c_n=a_n+a_{3n}+\cdots$, and $c_k=a_k+\sum_{\ell\ge1}(a_{2\ell n+k}+a_{2\ell n-k})$ for $1\le k\le n-1$. | ◐ partial | `chebyshev-approx-analytic`, `chebyshev-aliasing` `NLAlib.hasSum_chebyshevAnalyticCoeff_mul_eval_interpolate_T_of_open_ellipse`, `NLAlib.interpolate_eval_T_node_eq_T_alias` | NLAlib has $p_n=\sum_k a_kT_{\mathrm{alias}(k)}$ pointwise for $f$ holomorphic and bounded on a Bernstein ellipse; the Lipschitz hypothesis and the coefficient identities (4.5)–(4.7) are missing (candidate `chebyshev-aliasing`). |
| Ex 4.1 | **Node polynomial for Chebyshev points.** The monic node polynomial of the $n+1$ Chebyshev points $\cos(j\pi/n)$ is $2^{-n}(T_{n+1}-T_{n-1})$. | ○ candidate | `chebyshev-barycentric-weights` | Proposed candidate `chebyshev-barycentric-weights` (trefethen19.candidates.json). NLAlib has only the first-kind analogue `nodal_chebyshevZero` ($2^{1-q}T_q$). |

## Chapter 5  (M 2 · ○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 5 (Lagrange basis and node polynomial) | **Lagrange polynomials, node polynomial.** For distinct nodes $x_0,\dots,x_n$, $\ell_j$ is the degree-$n$ polynomial with $\ell_j(x_k)=\delta_{jk}$, $\ell_j(x)=\prod_{k\ne j}(x-x_k)/(x_j-x_k)$, and $\ell(x)=\prod_k(x-x_k)$ is the node polynomial; $p=\sum_jf_j\ell_j$ interpolates. | M mathlib | `Mathlib:Lagrange.basis`, `Mathlib:Lagrange.nodal`, `Mathlib:Lagrange.interpolate` |  |
| Thm 5.1 | **Barycentric interpolation formula.** Off the nodes the interpolant is $p(x)=\sum_j\frac{\lambda_jf_j}{x-x_j}\big/\sum_j\frac{\lambda_j}{x-x_j}$ with weights $\lambda_j=1/\prod_{k\ne j}(x_j-x_k)$, and $p(x_j)=f_j$. | M mathlib | `Mathlib:Lagrange.eval_interpolate_not_at_node'`, `Mathlib:Lagrange.nodalWeight`, `Mathlib:Lagrange.eval_interpolate_at_node` | Mathlib's second barycentric form with `nodalWeight` = the book's $\lambda_j$. |
| Thm 5.2 | **Barycentric interpolation in Chebyshev points.** At the Chebyshev points the barycentric weights may be taken as $(-1)^j$, halved for $j=0$ and $j=n$: $p(x)=\sum_j{}'\frac{(-1)^jf_j}{x-x_j}\big/\sum_j{}'\frac{(-1)^j}{x-x_j}$. | ○ candidate | `chebyshev-barycentric-weights` | Proposed candidate `chebyshev-barycentric-weights` (trefethen19.candidates.json). |

## Chapter 6  (M 2 · ○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 6.1 | **Weierstrass approximation theorem.** Every continuous $f$ on $[-1,1]$ is uniformly approximable by polynomials to any accuracy $\varepsilon>0$. | M mathlib | `Mathlib:polynomialFunctions_closure_eq_top`, `Mathlib:exists_polynomial_near_of_continuousOn` |  |
| Ex 6.4 | **Bernstein's proof (Bernstein polynomials).** For $f\in C[0,1]$ the Bernstein polynomials $B_n(x)=\sum_k f(k/n)\binom nk x^k(1-x)^{n-k}$ converge uniformly to $f$. | M mathlib | `Mathlib:bernsteinPolynomial`, `Mathlib:bernsteinApproximation`, `Mathlib:bernsteinApproximation_uniform` |  |
| Ex 6.6 | **Fejér's theorem for Chebyshev series.** For any $f\in C[-1,1]$ the Cesàro means $S_n$ of the partial sums of its Chebyshev series converge uniformly to $f$; (b) Hermite–Fejér interpolants in the zeros of $T_n$ also converge. | ○ candidate | `fejer-chebyshev-means` | Proposed candidate `fejer-chebyshev-means` (trefethen19.candidates.json). Part (a) is the target; part (b) (Hermite–Fejér) is low value. |

## Chapter 7  (M 1 · ○ 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 7 (total variation) | **Bounded variation.** The total variation of $f$ on $[-1,1]$ is the supremum over partitions of $\sum|f(x_{i+1})-f(x_i)|$ (equal to $\|f'\|_1$ for absolutely continuous $f$); $f$ has bounded variation if it is finite. | M mathlib | `Mathlib:eVariationOn`, `Mathlib:BoundedVariationOn` |  |
| Thm 7.1 | **Chebyshev coefficients of differentiable functions.** If $f,\dots,f^{(\nu-1)}$ are absolutely continuous on $[-1,1]$ and $f^{(\nu)}$ has total variation $V$, then $|a_k|\le\frac{2V}{\pi k(k-1)\cdots(k-\nu)}\le\frac{2V}{\pi(k-\nu)^{\nu+1}}$ for $k\ge\nu+1$. | ○ candidate | `chebyshev-coeff-bv-decay` |  |
| Thm 7.2 | **Convergence for differentiable functions.** Under Thm 7.1's hypotheses with $\nu\ge1$ and $n>\nu$: $\|f-f_n\|\le\frac{2V}{\pi\nu(n-\nu)^\nu}$ and $\|f-p_n\|\le\frac{4V}{\pi\nu(n-\nu)^\nu}$. | ○ candidate | `chebyshev-approx-differentiable` | NLAlib's `jackson-lipschitz` gives an $O(L/n)$ bound for Lipschitz $f$ by a different (convolution) construction; it is not a case of this theorem. |

## Chapter 8  (✓ 4 · ◐ 1 · ○ 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 8 (Bernstein ellipse) | **Bernstein ellipse.** For $\rho>1$, $E_\rho$ is the open region bounded by the image of $|z|=\rho$ under the Joukowski map $x=(z+z^{-1})/2$: an ellipse with foci $\pm1$ and semi-axis sum $\rho$. | ✓ nlalib | `chebyshev-coeff-analytic-decay`, `bernstein-ellipse-def` `NLAlib.openBernsteinEllipse`, `NLAlib.filledBernsteinEllipse`, `NLAlib.joukowski` | Defined as the Joukowski image of the annulus $\rho^{-1}<|w|<\rho$, which is the book's region; the atlas definition entry `bernstein-ellipse-def` is still candidate because its extra characterisations (foci form, $|T_n|$ bound on $E_\rho$) are not stated. |
| Thm 8.1 | **Chebyshev coefficients of analytic functions.** If $f$ extends analytically to the open Bernstein ellipse $E_\rho$ with $|f|\le M$ there, then $|a_0|\le M$ and $|a_k|\le2M\rho^{-k}$ for $k\ge1$. | ✓ nlalib | `chebyshev-coeff-analytic-decay` `NLAlib.abs_chebyshevAnalyticCoeff_le_of_open_ellipse`, `NLAlib.abs_chebyshevAnalyticCoeff_zero_le_of_open_ellipse`, `NLAlib.norm_chebyshevComplexCoeff_le_of_open_ellipse` |  |
| Thm 8.2 | **Convergence for analytic functions.** Under Thm 8.1's hypotheses, for every $n\ge0$: $\|f-f_n\|\le\frac{2M\rho^{-n}}{\rho-1}$ and $\|f-p_n\|\le\frac{4M\rho^{-n}}{\rho-1}$. | ✓ nlalib | `chebyshev-approx-analytic`, `bernstein-ellipse-approx` `NLAlib.abs_re_sub_eval_chebyshevAnalyticTrunc_le_of_open_ellipse`, `NLAlib.abs_re_sub_eval_chebyshevAnalyticInterpolant_le_of_open_ellipse`, `NLAlib.degree_le_and_abs_sub_chebyshev_approximations_le_of_open_ellipse` |  |
| Thm 8.3 | **Converse of Theorem 8.2.** If some polynomials $q_n\in\mathcal P_n$ satisfy $\|f-q_n\|\le C\rho^{-n}$ for all $n$ ($\rho>1$), then $f$ continues analytically to the open Bernstein ellipse $E_\rho$. | ○ candidate | `bernstein-converse` | Proposed candidate `bernstein-converse` (trefethen19.candidates.json). |
| Ex 8.6 | **Bernstein's inequality on the ellipse.** If $\deg p\le d$ then $\sup_{\overline{E_\rho}}|p|\le\rho^d\max_{[-1,1]}|p|$. | ◐ partial | `chebyshev-extremal`, `bernstein-walsh-ellipse` `NLAlib.abs_eval_le_mul_abs_eval_T_real_of_forall_abs_le` | NLAlib has only the real-axis case ($|p(x)|\le M|T_d(x)|\le M\rho^d$ for real $|x|\ge1$ on the ellipse); the complex bound is the candidate `bernstein-walsh-ellipse`. |
| Ex 8.10 | **Polynomial approximation of 1/x (CG convergence).** For $0<m<M$, $1/x$ is approximable on $[m,M]$ by degree-$n$ polynomials with geometric error, rate $(1+2/\sqrt\kappa)^{-n}$ in terms of the condition number $\kappa$. | ✓ nlalib | `inverse-polynomial-approx` `NLAlib.exists_degree_lt_abs_eval_sub_inv_le` | NLAlib proves the explicit bound $\frac2m\big(\frac{\sqrt\kappa-1}{\sqrt\kappa+1}\big)^n$ with $\kappa=M/m$, which is a faster rate than the exercise's. As printed ('for any $\kappa<M/m$') the exercise is too strong for small $\kappa$; with $\kappa=M/m$ it follows from the NLAlib bound. |
| Ex 8.11 | **Bernstein's theorem.** Thm 8.3 remains true under the weaker hypothesis $\limsup_n\|f-q_n\|^{1/n}\le\rho^{-1}$. | ○ candidate | `bernstein-converse` | Proposed candidate `bernstein-converse` (trefethen19.candidates.json). |

## Chapter 9  (– 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 9.1 | **Gibbs phenomenon for Chebyshev interpolants.** The Chebyshev interpolants of $\operatorname{sign}(x)$ have sup norms tending to $1.28228\ldots$ along odd $n$ and $1.06578\ldots$ along even $n$. | – out-of-scope |  | Asymptotic overshoot constants (not proved in the book); approximation of sign uses rates away from the jump (`sign-polynomial-approx`), not Gibbs constants. |
| Thm 9.2 | **Gibbs phenomenon for Chebyshev projections.** The Chebyshev projections of $\operatorname{sign}(x)$ have sup norms tending to $\tfrac2\pi\operatorname{Si}(\pi)=1.17898\ldots$. | – out-of-scope |  | Asymptotic overshoot constant; no consumer. |

## Chapter 10  (✓ 1 · ○ 5 · – 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 10 (best approximation) | **Best (minimax) approximation.** $p^*\in\mathcal P_n$ is a best approximation of $f\in C[-1,1]$ if it minimises $\|f-p\|_\infty$; its error is $E_n(f)$. | ○ candidate | `minimax-error-def` | NLAlib has `isLeast_chebyshev_minimax` / `isLeast_chebyshev_monic_minimax` for specific problems but no general $E_n(f)$. |
| Def 10 (equioscillation) | **Equioscillation, alternant.** $f-p$ equioscillates at $k$ points if there are $x_1<\dots<x_k$ in $[-1,1]$ with $f(x_j)-p(x_j)=\pm(-1)^j\|f-p\|$; $n+2$ such points form an alternant. | ○ candidate | `equioscillation` |  |
| Thm 10.1 | **Equioscillation characterization of best approximants.** Each continuous $f$ on $[-1,1]$ has a unique best approximation $p^*\in\mathcal P_n$; for real $f$, $p^*$ is real and $p\in\mathcal P_n$ equals $p^*$ iff $f-p$ equioscillates at at least $n+2$ points. | ○ candidate | `equioscillation`, `minimax-error-def` |  |
| Ex 10.3 | **de la Vallée Poussin lower bound.** If $f-p$ ($p\in\mathcal P_n$) alternates in sign at $n+2$ points with $|f-p|\ge\varepsilon$ there, then $\|f-p^*\|\ge\varepsilon$. | ○ candidate | `de-la-vallee-poussin` |  |
| Ex 10.7 | **Bernstein's lethargy theorem.** For any sequence $\varepsilon_n\downarrow0$ there is $f\in C[-1,1]$ with $\|f-p_n^*\|\ge\varepsilon_n$ for all $n$. | – out-of-scope |  | Existence of arbitrarily slowly approximable functions; no consumer (lower bounds in RandNLA are for specific functions). |
| Ex 10.11 | **Chebyshev polynomials as best approximations.** The best degree-$n$ approximation to $x^{n+1}$ is $x^{n+1}-2^{-n}T_{n+1}$; equivalently $2^{-n}T_{n+1}$ is the monic polynomial of degree $n+1$ with the least sup norm $2^{-n}$ on $[-1,1]$. | ✓ nlalib | `chebyshev-monic-minimal` `NLAlib.isLeast_chebyshev_monic_minimax`, `NLAlib.inv_two_pow_le_of_monic_of_forall_abs_eval_le`, `NLAlib.monic_inv_two_pow_mul_T` | This is where ATAP states monic minimality; atlas `chebyshev-monic-minimal` cites 'Thm 16.1', which is a different result. |
| Ex 10.12 | **Every best approximant is an interpolant.** The best approximation $p^*\in\mathcal P_n$ of a real $f\in C[-1,1]$ interpolates $f$ at some $n+1$ distinct points of $(-1,1)$. | ○ candidate | `best-approximant-interpolates` | Proposed candidate `best-approximant-interpolates` (trefethen19.candidates.json). |
| Ex 10.13 | **Marcinkiewicz's theorem.** For each fixed $f\in C[-1,1]$ there is a triangular array of nodes whose interpolants converge to $f$ (contrast with Faber's theorem). | – out-of-scope |  | Existence of $f$-dependent node arrays; no consumer. |

## Chapter 11  (○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 11.1 | **Hermite interpolation formula.** For $f$ analytic in a region containing distinct nodes $x_0,\dots,x_n$ and a contour $\Gamma$ around them, $p(x)=\frac1{2\pi i}\int_\Gamma\frac{f(t)(\ell(t)-\ell(x))}{\ell(t)(t-x)}dt$ and, for $x$ inside $\Gamma$, $f(x)-p(x)=\frac1{2\pi i}\int_\Gamma\frac{\ell(x)f(t)}{\ell(t)(t-x)}dt$. | ○ candidate | `hermite-integral-formula` | Proposed candidate `hermite-integral-formula` (trefethen19.candidates.json). The only interpolation-error formula ATAP states; the derivative (Cauchy) remainder of `interpolation-remainder` does not appear in the book. |

## Chapter 12  (– 4)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 12 (potential and equilibrium measure) | **Logarithmic potential, Chebyshev density.** Node sets define discrete potentials $u_n(s)=\sum_j\log|s-x_j|$; the continuum limit for $[-1,1]$ is the equilibrium (Chebyshev) measure $d\mu=\pi^{-1}(1-x^2)^{-1/2}dx$. | – out-of-scope |  | Potential-theoretic machinery with no NLA consumer. |
| Def 12 (uniformly distributed grids) | **Uniformly distributed node sequences.** Grids are uniformly distributed on $[-1,1]$ if their node polynomials satisfy $\lim_n(\max_{[-1,1]}|\ell_n|)^{1/n}=\tfrac12$ (the capacity of the interval). | – out-of-scope |  | Potential theory; no consumer. |
| Thm 12.1 | **Interpolation in uniformly distributed points.** If $\rho$ is the parameter of the largest Bernstein ellipse to which $f$ continues analytically, interpolants in any uniformly distributed grids satisfy $\lim_n\|f-p_n\|^{1/n}=\rho^{-1}$. | – out-of-scope |  | Potential-theoretic asymptotics (proof by reference to Gaier); the explicit Chebyshev-grid rate is Thm 8.2, already proved. |
| Def 12 (maximal convergence) | **Maximally convergent sequences.** Approximations $p_n\in\mathcal P_n$ are maximally convergent if $\limsup_n\|f-p_n\|^{1/n}=\rho^{-1}$, the smallest possible value (Ch. 16 restates this). | – out-of-scope |  | Asymptotic notion with no consumer; the quantitative lower bound is the candidate `bernstein-converse`. |

## Chapter 13  (– 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 13 (Runge phenomenon) | **Runge function and Runge region.** Equispaced interpolants of $1/(1+25x^2)$ diverge near the endpoints; convergence for equispaced nodes requires analyticity in a larger 'football' region determined by the equispaced potential. | – out-of-scope |  | Negative result about equispaced interpolation; quantified in the index by Thm 15.2 (15.9). |

## Chapter 15  (○ 4)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 15 (Lebesgue function and constant) | **Lebesgue function and Lebesgue constant.** For nodes $x_0,\dots,x_n$, $\lambda(x)=\sum_j|\ell_j(x)|$ and $\Lambda=\sup_{[-1,1]}\lambda$, the $\infty$-norm of the interpolation operator; more generally $\Lambda=\|L\|$ for a linear projection $L:C[-1,1]\to\mathcal P_n$. | ○ candidate | `lebesgue-constant-def` |  |
| Thm 15.1 | **Near-best approximation and Lebesgue constants.** If $L$ is a linear projection of $C[-1,1]$ onto $\mathcal P_n$ with Lebesgue constant $\Lambda$, then $\|f-Lf\|\le(\Lambda+1)\|f-p^*\|$. | ○ candidate | `lebesgue-constant-def` | Proposed candidate `chebyshev-projection-lebesgue-constant` (trefethen19.candidates.json). The atlas candidate states it for interpolation only; the book's statement is for any linear projection (needed for Chebyshev truncation). |
| Thm 15.2 | **Lebesgue constants for polynomial interpolation.** For any $n+1$ distinct nodes in $[-1,1]$, $\Lambda_n\ge\frac2\pi\log(n+1)+0.52125\ldots$; for Chebyshev points $\Lambda_n\le\frac2\pi\log(n+1)+1$ and $\Lambda_n\sim\frac2\pi\log n$; for equispaced points $\Lambda_n>2^{n-2}/n^2$ ($n\ge1$) and $\Lambda_n\sim2^{n+1}/(en\log n)$. | ○ candidate | `lebesgue-constant-chebyshev` | Proposed candidate `lebesgue-constant-lower-bound` (trefethen19.candidates.json). Existing candidate covers (15.8a); the general lower bound (15.7) and the equispaced bound (15.9a) are the new candidate `lebesgue-constant-lower-bound`. |
| Thm 15.3 | **Lebesgue constants for Chebyshev projection.** For $n\ge1$ the Lebesgue constant of degree-$n$ Chebyshev truncation is $\Lambda_n=\frac1{2\pi}\int_{-\pi}^{\pi}\left|\frac{\sin((n+1/2)t)}{\sin(t/2)}\right|dt$ (the Dirichlet-kernel $L^1$ norm), with $\Lambda_n\le\frac4{\pi^2}\log(n+1)+3$ and $\Lambda_n\sim\frac4{\pi^2}\log n$. | ○ candidate | `chebyshev-projection-lebesgue-constant` | Proposed candidate `chebyshev-projection-lebesgue-constant` (trefethen19.candidates.json). The extracted text of (15.10) shows no absolute value (probably lost in extraction); the Lebesgue constant is the $L^1$ norm of the Dirichlet kernel. |

## Chapter 16  (○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 16.1 | **Chebyshev projections and interpolants are near-best.** For $f\in C[-1,1]$ and $n\ge1$: $\|f-f_n\|\le(4+\frac4{\pi^2}\log(n+1))\|f-p_n^*\|$ and $\|f-p_n\|\le(2+\frac2\pi\log(n+1))\|f-p_n^*\|$. | ○ candidate | `lebesgue-constant-chebyshev` | Proposed candidate `chebyshev-projection-lebesgue-constant` (trefethen19.candidates.json). Interpolant half is in the conclusion of candidate `lebesgue-constant-chebyshev`; projection half is in the new `chebyshev-projection-lebesgue-constant`. |

## Chapter 17  (◐ 2 · M 1 · ○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 17 (orthogonal polynomials) | **Orthogonal polynomials and their three-term recurrence.** For a weight $w>0$ on $(-1,1)$ with $\int w<\infty$, $p_0,p_1,\dots$ ($\deg p_n=n$) are orthogonal for $(f,g)=\int wf\bar g$; they satisfy a three-term recurrence $p_{n+1}=(x-\alpha_n)p_n-\beta_np_{n-1}$ (17.8). | ◐ partial | `lanczos-orthogonal-polynomials` `NLAlib.LanczosDecomp.integral_poly_mul_poly`, `NLAlib.LanczosDecomp.X_mul_poly`, `NLAlib.LanczosDecomp.integral_eval_charpoly_mul_eq_zero` | NLAlib has orthonormal polynomials and their three-term recurrence for the discrete spectral measure $\mu_b$ of a symmetric matrix (Lanczos); a general weight/measure is missing (see candidates `orthogonal-polynomial-zeros`, `gauss-quadrature-general-measure`). As printed, (17.8) uses the coefficients $(xp_n,p_k)$ for monic $p_k$; the correct coefficients are $(xp_n,p_k)/(p_k,p_k)$. |
| Def 17 (Legendre polynomials) | **Legendre polynomials and points.** The orthogonal polynomials for $w\equiv1$, normalised by $P_n(1)=1$: $\int_{-1}^1P_jP_k=\frac{2}{2k+1}\delta_{jk}$ and $(k+1)P_{k+1}=(2k+1)xP_k-kP_{k-1}$; Legendre points are their zeros. | M mathlib | `Mathlib:Polynomial.shiftedLegendre`, `Mathlib:Polynomial.coeff_shiftedLegendre`, `Mathlib:Polynomial.degree_shiftedLegendre` | Mathlib has only the shifted Legendre polynomials on $[0,1]$ (definition, coefficients, degree, symmetry); orthogonality (17.5) and the recurrence (17.6) are not stated. No RandNLA consumer, so not proposed. |
| Ex 17.4 | **Zeros of orthogonal polynomials.** The zeros of each orthogonal polynomial $p_n$ for a weight on $[-1,1]$ are real, simple and lie in $(-1,1)$. | ○ candidate | `orthogonal-polynomial-zeros` | Proposed candidate `orthogonal-polynomial-zeros` (trefethen19.candidates.json). |
| Ex 17.8 | **Minimality of orthogonal polynomials.** Among monic polynomials $q$ of degree $n$, the monic orthogonal polynomial $p_n$ minimises $(q,q)$. | ◐ partial | `krylov-polynomial-exactness`, `lanczos-orthogonal-polynomials` `NLAlib.dotProduct_aeval_charpoly_mulVec_self_le`, `NLAlib.dotProduct_aeval_mulVec_self_eq_charpoly_iff` | Proved for the discrete spectral measure $\mu_b$ ($\|p(A)b\|^2=\int p^2d\mu_b$, minimiser the characteristic polynomial of the Krylov compression, with uniqueness); the statement for a general weight is missing. |

## Chapter 18  (○ 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 18 (colleague matrix) | **Colleague and comrade matrices.** The colleague matrix is the almost-tridiagonal matrix of Thm 18.1 built from Chebyshev coefficients; for other orthogonal-polynomial bases the analogue is the comrade matrix. | ○ candidate |  | Proposed candidate `colleague-matrix` (trefethen19.candidates.json). |
| Thm 18.1 | **Polynomial roots and colleague matrix eigenvalues.** The roots of $p=\sum_{k=0}^na_kT_k$ ($a_n\ne0$) are the eigenvalues of the $n\times n$ colleague matrix: tridiagonal with entries $\tfrac12$ (first row $1$) plus a last-row correction $-a_k/(2a_n)$. | ○ candidate | `colleague-matrix` | Proposed candidate `colleague-matrix` (trefethen19.candidates.json). |

## Chapter 19  (◐ 1 · ○ 5 · – 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 19 (interpolatory quadrature) | **Interpolatory, Clenshaw–Curtis and Gauss quadrature.** An $(n+1)$-point rule $I_n=\sum_kw_kf(x_k)$ is interpolatory if $w_k=\int_{-1}^1\ell_k$; Clenshaw–Curtis uses Chebyshev points, Gauss uses the zeros of $P_{n+1}$, Newton–Cotes equispaced points. | ○ candidate |  | Proposed candidate `gauss-quadrature-general-measure` (trefethen19.candidates.json). NLAlib's Gauss rule exists only for the spectral measure (`lanczos-gauss-quadrature`). |
| Thm 19.1 | **Polynomial degree of quadrature formulas.** An $(n+1)$-point interpolatory rule is exact on $\mathcal P_n$; the $(n+1)$-point Gauss rule is exact on $\mathcal P_{2n+1}$. | ◐ partial | `lanczos-gauss-quadrature` `NLAlib.dotProduct_aeval_mulVec_eq_of_degree_lt_two_mul`, `NLAlib.LanczosDecomp.dotProduct_aeval_mulVec_eq_sum`, `Mathlib:Polynomial.Chebyshev.integral_eq_sumZeroes` | Proposed candidate `gauss-quadrature-general-measure` (trefethen19.candidates.json). Gauss exactness to degree $2q-1$ is proved for the spectral measure $\mu_b$ (NLAlib) and for the Chebyshev weight (Mathlib, Gauss–Chebyshev); the Legendre-weight (Lebesgue measure) rule of the book and the interpolatory part are missing. |
| Thm 19.2 | **Integral of a Chebyshev series.** $\int_{-1}^1\sum_{k=0}^nc_kT_k(x)dx=\sum_{k\text{ even}}\frac{2c_k}{1-k^2}$; equivalently $\int_{-1}^1T_k=\frac2{1-k^2}$ for even $k$ and $0$ for odd $k$. | ○ candidate | `chebyshev-integral-formula` | Proposed candidate `chebyshev-integral-formula` (trefethen19.candidates.json). |
| Thm 19.3 | **Quadrature formulas for analytic integrands.** If $f$ is analytic and bounded by $M$ in $E_\rho$, then $(n+1)$-point Clenshaw–Curtis ($n\ge2$) has $|I-I_n|\le\frac{64}{15}\frac{M\rho^{1-n}}{\rho^2-1}$ and $(n+1)$-point Gauss ($n\ge1$) has $|I-I_n|\le\frac{64}{15}\frac{M\rho^{-2n}}{\rho^2-1}$. | ○ candidate | `lanczos-quadrature-analytic-error` | Proposed candidate `gauss-clenshaw-curtis-quadrature-error` (trefethen19.candidates.json). NLAlib's `lanczos-quadrature-analytic-error` is the Gauss analogue for a spectral measure with the weaker constant $4M\rho^{1-2q}/(\rho-1)$ per unit mass (a $q$-point rule), derived from Thm 8.2 and exactness; it is not this statement (different measure, different constant) and there is no Clenshaw–Curtis result. |
| Thm 19.4 | **Quadrature formulas for differentiable integrands.** Clenshaw–Curtis and Gauss converge for every continuous $f$; if $f^{(\nu)}$ ($\nu\ge1$) has bounded variation $V$, Clenshaw–Curtis has $|I-I_n|\le\frac{32}{15}\frac{V}{\pi\nu(n-\nu)^\nu}$ ($n>\nu$) and Gauss $|I-I_n|\le\frac{32}{15}\frac{V}{\pi\nu(n-2\nu-1)^{2\nu+1}}$ ($n>2\nu+1$). | ○ candidate | `lanczos-quadrature-lipschitz-error` | Proposed candidate `gauss-clenshaw-curtis-quadrature-error` (trefethen19.candidates.json). NLAlib's `lanczos-quadrature-lipschitz-error` is a related Gauss bound for Lipschitz $f$ and spectral measures ($\pi L(c-a)/(4q)$); not a case of this theorem. |
| Thm 19.5 | **Clenshaw–Curtis quadrature for differentiable integrands.** Under Thm 19.4's hypotheses, Clenshaw–Curtis also satisfies the Gauss-type bound $\frac{32}{15}\frac{V}{\pi\nu(n-2\nu-1)^{2\nu+1}}$ for all sufficiently large $n$ (depending on $\nu$ only). | ○ candidate | `gauss-clenshaw-curtis-quadrature-error` | Proposed candidate `gauss-clenshaw-curtis-quadrature-error` (trefethen19.candidates.json). Proof only by reference [Trefethen 2008]; priority later. |
| Thm 19.6 | **Barycentric weights for Legendre points.** With Gauss nodes $x_k$ and weights $w_k$, the numbers $\lambda_k=(-1)^k\sqrt{(1-x_k^2)w_k}$ are valid barycentric weights for interpolation in Legendre points. | – out-of-scope |  | Computational formula for Legendre barycentric weights; no consumer. |

## Chapter 20  (– 3)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 20 (CF approximation) | **Carathéodory–Fejér approximation.** The CF approximant of degree $n$ is built from the leading singular value and vector of a Hankel matrix of Chebyshev coefficients of $f$. | – out-of-scope |  | Near-best approximation algorithm via Hankel SVD; complex-analytic, no consumer. |
| Thm 20.1 | **Carathéodory–Fejér–Schur theorem.** The CF approximation problem on the unit circle has a unique solution $\tilde P$, with error $(G-\tilde P)(z)=\lambda z^{n+1}\overline{u(z)}/u(z)$ mapping the circle to a circle of radius $|\lambda|$ with winding number $\ge n+1$ ($=n+1$ if $|\lambda|$ is a simple top singular value). | – out-of-scope |  | Complex-analytic Hankel/CF theory; no consumer. |
| Thm 20.2 | **Accuracy of polynomial CF approximation.** For $f$ with Lipschitz $(3m+3)$rd derivative and $f^{(m+1)}(0)\ne0$, on $[-s,s]$ as $s\to0$: $\|f-p^*\|=\Theta(s^{m+1})$ while $\|p^{CF}-p^*\|=O(s^{3m+4})$. | – out-of-scope |  | CF asymptotics; no consumer. |

## Chapter 21  (– 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 21.1 | **Geometric convergence of derivatives.** If $f$ continues analytically to the closed ellipse $\overline{E_\rho}$, then for each $\nu\ge0$, $\|f^{(\nu)}-f_n^{(\nu)}\|=O(\rho^{-n})$ and $\|f^{(\nu)}-p_n^{(\nu)}\|=O(\rho^{-n})$. | – out-of-scope |  | Derivative accuracy for spectral methods; no consumer (Markov's inequality, already proved, covers the polynomial side). |
| Def 21 (differentiation matrix) | **Spectral differentiation matrix.** The $(n+1)\times(n+1)$ matrix mapping values of $p\in\mathcal P_n$ on a grid to values of $p'$ on the same grid. | – out-of-scope |  | Spectral collocation for ODEs; no RandNLA consumer. |

## Chapter 22  (– 3)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 22 (transplanted approximation) | **Conformally transplanted approximants.** Approximations $p(g^{-1}(x))$ for an analytic map $g:[-1,1]\to[-1,1]$ (e.g. 'sausage maps'), which are not polynomials in $x$. | – out-of-scope |  | Non-polynomial approximation spaces; no consumer. |
| Thm 22.1 | **Transformed Chebyshev series.** For $g$ analytic and increasing from $[-1,1]$ onto itself and Lipschitz $f$, $f(x)=\sum_ka_kT_k(g^{-1}(x))$ absolutely, with $a_k$ the Chebyshev coefficients of $f\circ g$. | – out-of-scope |  | Change of variables in Thm 3.1; non-polynomial approximants, no consumer. |
| Thm 22.2 | **Transformed coefficients of analytic functions.** If $g$ continues to $E_\rho$ and $f$ to $g(E_\rho)$ with $|f|\le M$ there, the transformed coefficients obey $|a_k|\le2M\rho^{-k}$ and the transformed truncations/interpolants have errors $\le2M\rho^{-n}/(\rho-1)$ and $4M\rho^{-n}/(\rho-1)$. | – out-of-scope |  | Thm 8.1–8.2 applied to $f\circ g$; non-polynomial approximants, no consumer. The extracted text of (22.4) reads $\rho^{-n}$ where $\rho^{-k}$ is meant. |

## Chapter 23  (M 1 · ○ 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 23 (rational functions of type (m,n)) | **Rational type, exact type.** $r$ is of type $(m,n)$, $r\in R_{mn}$, if $r=p/q$ with $\deg p\le m$, $\deg q\le n$; in lowest terms its exact type is $(\mu,\nu)$. | ○ candidate |  | Proposed candidate `rational-equioscillation` (trefethen19.candidates.json). Needed only for the rational best-approximation candidate; priority later. |
| Thm 23.1 | **Partial fraction representation.** Each $r\in R_{mn}$ has a unique representation $r=p_0+\sum_kp_k((x-\xi_k)^{-1})$ with $p_0$ polynomial of degree $\le m$, $p_k(0)=0$, $\deg p_k=\nu_k\ge1$, $\sum\nu_k\le n$. | M mathlib | `Mathlib:Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`, `Mathlib:Polynomial.quo_add_sum_rem_mul_pow_inverse_unique` | Mathlib states existence and uniqueness of partial fractions for products of powers of pairwise coprime monic factors (the book's case: linear factors $x-\xi_k$ over $\mathbb C$); the degree bookkeeping $\deg p_0\le m$, $\sum\nu_k\le n$ is immediate but not stated. |

## Chapter 24  (○ 3 · – 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 24 (defect) | **Defect of a rational function.** For $r\in R_{mn}$ of exact type $(\mu,\nu)$ the defect is $d=\min(m-\mu,n-\nu)$ (with $d=n$ for $r=0$). | ○ candidate |  | Proposed candidate `rational-equioscillation` (trefethen19.candidates.json). |
| Thm 24.1 | **Equioscillation characterization of rational best approximants.** A real $f\in C[-1,1]$ has a unique best real approximation $r^*\in R_{mn}$, and real $r\in R_{mn}$ equals $r^*$ iff $f-r$ equioscillates at at least $m+n+2-d$ points, $d$ the defect of $r$. | ○ candidate | `rational-equioscillation` | Proposed candidate `rational-equioscillation` (trefethen19.candidates.json). |
| Def 24 (Walsh table) | **Walsh table.** The array of best real rational approximants $r^*_{mn}$ of $f$ indexed by $m,n\ge0$. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Thm 24.2 | **Square blocks in the Walsh table.** The Walsh table of a real $f\in C[-1,1]$ splits into exactly square blocks of identical entries (one infinite if $f$ is rational), except that an entry $r=0$ fills all columns left of some index. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Ex 24.5 | **de la Vallée Poussin lower bound (rational).** If $f-r$ ($r\in R_{mn}$ real, defect $d$) alternates in sign at $m+n+2-d$ points with $|f-r|\ge\varepsilon$ there, then $\|f-r^*\|\ge\varepsilon$. | ○ candidate | `rational-equioscillation` | Proposed candidate `rational-equioscillation` (trefethen19.candidates.json). |

## Chapter 25  (○ 2)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Thm 25.1 | **Approximation of |x| on [−1,1].** The best errors satisfy $E_{n,0}(|x|)\sim\beta/n$ with $\beta=0.2801\ldots$ (Bernstein's constant; Varga–Carpenter) and $E_{n,n}(|x|)\sim8e^{-\pi\sqrt n}$ (Stahl). | ○ candidate | `abs-best-approx-asymptotics` | Proposed candidate `abs-best-approx-asymptotics` (trefethen19.candidates.json). Assume only; deep asymptotics. |
| Thm 25.2 | **Approximation of e^x on (−∞,0].** Best type-$(0,n)$ rational approximations of $e^x$ on $(-\infty,0]$ satisfy $\lim_nE_{0n}^{1/n}=1/3$ (Schönhage), and type $(n,n)$ satisfy $E_{nn}\sim2H^{n+1/2}$, $H=1/9.2890\ldots$ (Halphen's constant; Aptekarev). | ○ candidate | `exp-rational-halfline` | Proposed candidate `exp-rational-halfline` (trefethen19.candidates.json). Assume only; deep asymptotics. |

## Chapter 26  (– 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 26 (rational interpolation) | **Cauchy (rational) interpolation problem.** Find $r\in R_{mn}$ with $r(x_j)=f_j$ at $m+n+1$ points; solutions need not exist (unattainable points), and the linearized form $p(x_j)=f_jq(x_j)$ is solved via an SVD. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |

## Chapter 27  (– 5)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 27 (Padé approximant) | **Padé approximant.** The type-$(m,n)$ Padé approximant $r_{mn}$ of a Taylor series $f$ is the $r\in R_{mn}$ making $(f-r)(z)=O(z^{k})$ with $k$ maximal. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Thm 27.1 | **Characterization of Padé approximants.** For each $m,n\ge0$, $f$ has a unique Padé approximant $r_{mn}\in R_{mn}$, and $r\in R_{mn}$ equals it iff $(f-r)(z)=O(z^{m+n+1-d})$, $d$ the defect of $r$. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Thm 27.2 | **Square blocks in the Padé table.** The Padé table of any $f$ splits into exactly square blocks of identical entries, with the same exception for $r=0$ as Thm 24.2. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Thm 27.3 | **Linear algebra solution of Padé problem.** Any nonzero null vector $b$ of the Toeplitz matrix $C$ of (27.8), with $a$ from (27.6), gives $p/q=r_{mn}$, the unique Padé approximant. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |
| Thm 27.4 | **Structure of a Padé approximant.** If $r_{mn}=\hat p/\hat q$ has exact type $(\mu,\nu)$, defect $d$, deficiency $\lambda$ and $\chi=d-\lambda$, then $C$ has rank $n-\chi$ and $(p,q)$ solve (27.5) iff $p=\pi\hat p$, $q=\pi\hat q$ for some $\pi\in\mathcal P_d$ divisible by $z^\lambda$. | – out-of-scope |  | rational-function theory (Walsh/Padé structure) with no consumer in randomized NLA |

## Chapter 28  (– 1)

| label | statement | status | atlas / declarations | note |
|---|---|---|---|---|
| Def 28 (convergence acceleration) | **Richardson, Aitken Δ², Shanks/epsilon extrapolation.** Sequence-acceleration methods obtained from polynomial (Richardson) or Padé-type rational (Aitken $\Delta^2$, Shanks, epsilon, eta) extrapolation of partial sums. | – out-of-scope |  | Extrapolation algorithms with no theorem stated and no consumer. |

## Atlas labels for this source not found in the index (verify)

- `Thm 11.1 (contour-integral form; the Rolle/derivative form is not stated in ATAP)` ← interpolation-remainder
- `Ch. 3 (Thm 3.1 coefficient formula)` ← chebyshev-coefficients-def
- `Ch. 8` ← bernstein-ellipse-def
- `Ch. 10` ← minimax-error-def
- `Thm 8.2 (transplanted to [a,b])` ← slit-plane-analytic-approx
- `Def 23 (rational functions of type (m,n))` ← rational-equioscillation
