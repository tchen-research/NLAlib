# Round 5: the polynomial module

Read `docs/STANDARDS.md` and `docs/ROUND1_BRIEF.md` (working rules: single-file checks with
`lake env lean NLAlib/Polynomial/<File>.lean`, build an olean you depend on with
`lake build NLAlib.Polynomial.<Module>`, wait and retry on a Lake lock, no full `lake build`, no
atlas edits, every file warning-free, `sorry` only in a named `SCAFFOLD: <atlas id>` lemma).

New module `NLAlib/Polynomial/` (layer 0, imports Mathlib and `NLAlib.ForMathlib` only; NO
matrices). `NLAlib/Polynomial/Basic.lean` is written and built: it defines `chebyshevResidual a b q`
(= `T_q((b+a−2X)/(b−a)) / T_q((b+a)/(b−a))`, value 1 at 0) and `chebyshevAmplifier α γ q`
(= `T_q(X/α) / T_q(1+γ)`). Everything is a real polynomial `ℝ[X]`; use Mathlib's
`Polynomial.Chebyshev.T ℝ n` / `U ℝ n` (index `ℤ`; write `(q : ℤ)` or let coercion do it).

What Mathlib already has (use it, do not re-prove): `Mathlib/RingTheory/Polynomial/Chebyshev.lean`
(recurrences, `degree_T`, `leadingCoeff_T` = 2^(n−1), `T_derivative_eq_U : derivative (T R n) =
n * U R (n−1)`, `U_eq_two_mul_T_add_U`, `U_mem_span_T`, `T_eval_neg`);
`Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Basic.lean` (`T_real_cos`,
`T_real_cosh : (T ℝ n).eval (cosh θ) = cosh (n*θ)`, `U_real_cos`, `U_real_cosh`);
`…/Chebyshev/RootsExtrema.lean` (`abs_eval_T_real_le_one`, `one_le_eval_T_real`,
`one_lt_eval_T_real`, `roots_T_real : roots = image (k ↦ cos((2k+1)π/(2n))) (range n)`,
`roots_T_real_nodup`, `abs_iterate_derivative_T_real_le`);
`…/Chebyshev/Extremal.lean` (`node n i = cos(iπ/n)`, `eval_T_real_node`,
`leadingCoeff_le_of_forall_abs_le_one : P.degree ≤ n → (∀ x ∈ Icc (−1) 1, |P.eval x| ≤ 1) →
P.coeff n ≤ 2^(n−1)`, `eval_iterate_derivative_le_of_forall_abs_le_one : 1 ≤ x → P.degree ≤ n →
(∀ x ∈ Icc (−1) 1, |P.eval x| ≤ 1) → (derivative^[k] P).eval x ≤ (derivative^[k] (T ℝ n)).eval x`,
and the `_eq_iff` equality cases); `Mathlib/LinearAlgebra/Lagrange.lean` (`Lagrange.interpolate s v r`,
`eval_interpolate_at_node`, `degree_interpolate_lt`, `eq_interpolate`, `Lagrange.nodal s v =
∏ (X − C (v i))`, `natDegree_nodal`); `Real.cosh_log : cosh (log x) = (x + x⁻¹)/2`;
`Mathlib/Analysis/Calculus/LocalExtr/Rolle.lean` (`exists_deriv_eq_zero`,
`exists_hasDerivAt_eq_zero`).

Statement conventions for this module: bounds on an interval are stated as
`∀ x ∈ Set.Icc a b, |p.eval x| ≤ M` (hypothesis) or `∃ x ∈ Set.Icc a b, M ≤ |p.eval x|`
(conclusion); no sup-norm definition. Degrees as `p.degree ≤ q` (`WithBot ℕ`, works for `p = 0`)
unless `natDegree` is genuinely needed. Condition numbers appear as `√b` and `√a`, never as a
separate `κ` variable: the CG rate is `(√b − √a)/(√b + √a)`.

## Groups (exclusive file ownership)

**P1 — `NLAlib/Polynomial/Chebyshev.lean` then `NLAlib/Polynomial/Approximation.lean`**

`Chebyshev.lean` (imports Mathlib only), atlas `chebyshev-growth` and `chebyshev-second-kind`:
1. `eval_T_real_eq_of_one_le : 1 ≤ x → (T ℝ q).eval x = ((x + √(x²−1))^q + (x − √(x²−1))^q)/2`
   (via `T_real_cosh` with `θ = log (x + √(x²−1))` and `cosh_log`; note `(x−√(x²−1)) = (x+√(x²−1))⁻¹`).
2. `pow_div_two_le_eval_T_real : 1 ≤ x → (x + √(x²−1))^q / 2 ≤ (T ℝ q).eval x` and the upper
   bound `eval_T_real_le_pow : 1 ≤ x → (T ℝ q).eval x ≤ (x + √(x²−1))^q`.
3. `monotoneOn_eval_T_real : MonotoneOn (fun x => (T ℝ q).eval x) (Set.Ici 1)`.
4. The gap form `one_add_sqrt_two_mul_pow_div_two_le_eval_T_real : 0 ≤ γ →
   (1 + √(2γ))^q / 2 ≤ (T ℝ q).eval (1 + γ)` (Musco–Musco 2015, proof of Lem. 4), and the
   condition-number form: for `0 < a < b`,
   `((√b + √a)/(√b − √a))^q / 2 ≤ (T ℝ q).eval ((b + a)/(b − a))` (the identity
   `(b+a)/(b−a) + √(((b+a)/(b−a))² − 1) = (√b+√a)/(√b−√a)` is worth its own lemma).
5. Second kind: `abs_eval_U_real_le : |x| ≤ 1 → |(U ℝ q).eval x| ≤ q + 1` (induction on `q` by
   two via `U_eq_two_mul_T_add_U` and `abs_eval_T_real_le_one`), and
   `abs_eval_derivative_T_real_le : |x| ≤ 1 → |(derivative (T ℝ q)).eval x| ≤ q^2`
   (from `T_derivative_eq_U` and the previous, or `abs_iterate_derivative_T_real_le` with `k = 1`).
   Also `eval_derivative_T_real_one : (derivative (T ℝ q)).eval 1 = q^2` if it falls out.

`Approximation.lean` (imports `NLAlib.Polynomial.Basic`, `.Chebyshev`, `.Minimax`): wait for
group P2's `Minimax.lean` olean (`lake build NLAlib.Polynomial.Minimax`; poll every few minutes,
start on the amplifier items meanwhile, which need only `Chebyshev.lean`), atlas
`chebyshev-amplifier`, `inverse-polynomial-approx`, and the κ-form of `chebyshev-minimax`:
6. `chebyshevAmplifier` API: `degree_chebyshevAmplifier_le`, `eval_chebyshevAmplifier_self :
   0 < α → 0 ≤ γ → (chebyshevAmplifier α γ q).eval (α*(1+γ)) = 1`,
   `one_le_eval_chebyshevAmplifier : 0 < α → 0 ≤ γ → α*(1+γ) ≤ x → 1 ≤ eval x` (monotonicity),
   `abs_eval_chebyshevAmplifier_le : 0 < α → 0 ≤ γ → x ∈ Icc (−α) α → |eval x| ≤ 2/(1+√(2γ))^q`.
   (Musco–Musco 2015 [`mm15`], Lem. 4 and Lem. 5 = the same polynomial with `γ = ε`.)
7. κ-form of the residual bound: for `0 < a < b`, `x ∈ Icc a b →
   |(chebyshevResidual a b q).eval x| ≤ 2 * ((√b − √a)/(√b + √a))^q` (from P2's
   `abs_eval_chebyshevResidual_le` and item 4).
8. Approximation of `1/x`: `0 < a < b → ∃ p : ℝ[X], p.degree < q ∧ ∀ x ∈ Icc a b,
   |p.eval x − 1/x| ≤ (2/a) * ((√b − √a)/(√b + √a))^q` (take `r = chebyshevResidual a b q`, write
   `r − 1 = X * (−p)` via `X ∣ r − 1` from `r.eval 0 = 1`, and `|1/x − p x| = |r x|/x ≤ |r x|/a`).
   Golub–Meurant (2010) [`gm10`], Ch. 8; the CG bound in the form consumers want.

**P2 — `NLAlib/Polynomial/Minimax.lean`** (imports `NLAlib.Polynomial.Basic` and Mathlib),
atlas `chebyshev-extremal`, `chebyshev-minimax`, `chebyshev-monic-minimal`. Do items 1–3 FIRST and
build the olean (`lake build NLAlib.Polynomial.Minimax`) as soon as they compile, since P1 polls
for it; item 4 may land in a second build.
1. `abs_eval_le_abs_eval_T_real_of_forall_abs_le_one : P.degree ≤ q → (∀ x ∈ Icc (−1) 1,
   |P.eval x| ≤ 1) → 1 ≤ |x| → |P.eval x| ≤ |(T ℝ q).eval x|` (Mathlib's
   `eval_iterate_derivative_le_of_forall_abs_le_one` with `k = 0` applied to `P` and `−P` for
   `1 ≤ x`; for `x ≤ −1` apply it to `P.comp (−X)` and use `T_eval_neg`). Also the scaled form
   `abs_eval_le_mul_abs_eval_T_real_of_forall_abs_le : P.degree ≤ q → (∀ x ∈ Icc (−1) 1,
   |P.eval x| ≤ M) → 1 ≤ |x| → |P.eval x| ≤ M * |(T ℝ q).eval x|` (for `M = 0` the polynomial
   vanishes on `[−1,1]` hence is `0`; handle it, do not assume `0 < M`).
2. `chebyshevResidual` API: `eval_chebyshevResidual_zero : a < b → (chebyshevResidual a b q).eval 0
   = 1` (needs `(T ℝ q).eval ((b+a)/(b−a)) ≠ 0`, true since the argument is `> 1` when `0 < a`, or
   `≥ 1`… state the hypothesis you need, `0 < a → a < b` is fine), `degree_chebyshevResidual_le :
   degree ≤ q`, `abs_eval_chebyshevResidual_le : 0 < a → a < b → x ∈ Icc a b →
   |(chebyshevResidual a b q).eval x| ≤ 1 / (T ℝ q).eval ((b+a)/(b−a))` (the affine map sends
   `[a,b]` into `[−1,1]`, then `abs_eval_T_real_le_one`).
3. The minimax lower bound (Golub–Meurant [`gm10`] App.; Trefethen–Bau Thm 38.5):
   `inv_eval_T_real_le_of_forall_abs_eval_le : 0 < a → a < b → p.degree ≤ q → p.eval 0 = 1 →
   (∀ x ∈ Icc a b, |p.eval x| ≤ M) → 1 / (T ℝ q).eval ((b+a)/(b−a)) ≤ M`
   (compose `p` with the inverse affine map `t ↦ (b+a − (b−a) t)/2` to get `P` with `|P| ≤ M` on
   `[−1,1]` and `P.eval ((b+a)/(b−a)) = 1`, then item 1), and the packaged form
   `isLeast_chebyshev_minimax : 0 < a → a < b → IsLeast {M | ∃ p : ℝ[X], p.degree ≤ q ∧ p.eval 0 = 1
   ∧ ∀ x ∈ Icc a b, |p.eval x| ≤ M} (1 / (T ℝ q).eval ((b+a)/(b−a)))`.
4. Monic minimality: `inv_two_pow_le_of_monic_of_forall_abs_eval_le : p.Monic → p.natDegree = q →
   0 < q → (∀ x ∈ Icc (−1) 1, |p.eval x| ≤ M) → 1 / 2^(q−1) ≤ M` (from
   `leadingCoeff_le_of_forall_abs_le_one` applied to `C M⁻¹ * p`; `M > 0` because a monic polynomial
   is not identically zero on `[−1,1]`), attained by `C (1/2^(q−1)) * T ℝ q` (state
   `monic_inv_two_pow_mul_T` and `abs_eval_inv_two_pow_mul_T_le`).

**P3 — `NLAlib/Polynomial/Markov.lean`** (imports Mathlib; may import
`NLAlib.Polynomial.Chebyshev` once P1 has built it, but do not wait for it), atlas
`markov-brothers`, `bernstein-polynomial-inequality`.
1. Markov brothers' inequality: `abs_eval_derivative_le_sq_mul_of_forall_abs_eval_le :
   p.degree ≤ q → (∀ x ∈ Icc (−1) 1, |p.eval x| ≤ M) → x ∈ Icc (−1) 1 →
   |(derivative p).eval x| ≤ q^2 * M`, and the interval version on `[a, b]` with constant
   `2 q^2/(b − a)`. Suggested route (Cheney, *Introduction to Approximation Theory*, Ch. 3, or
   Rivlin, *Chebyshev Polynomials*, §2.7): Bernstein's inequality for `|x| < 1` by Lagrange
   interpolation of `p` at the zeros `cos((2k+1)π/(2q))` of `T_q` (Mathlib `roots_T_real`) with
   `p = Σ p(x_k) ℓ_k`, and the Chebyshev-node interpolation of `p'` for `x` near `±1`; or any
   proof you can close. Equality case not required.
2. Bernstein's inequality: `abs_eval_derivative_le_div_sqrt_of_forall_abs_eval_le : p.degree ≤ q →
   (∀ x ∈ Icc (−1) 1, |p.eval x| ≤ M) → |x| < 1 → |(derivative p).eval x| ≤ q * M / √(1 − x^2)`.
3. Either may end as a named scaffold if it does not close; prefer a fully proved Markov with
   a worse explicit constant over a scaffold (say what constant you got). Report any general
   lemma (e.g. about Lagrange basis polynomials at Chebyshev zeros) that belongs in `Interpolation`.

**P4 — `NLAlib/Polynomial/Interpolation.lean`** (imports Mathlib), atlas
`interpolation-remainder`, `chebyshev-interpolation-error`.
1. Generalised Rolle: `exists_iteratedDeriv_eq_zero_of_eval_eq_zero`-style: `f : ℝ → ℝ`,
   `ContDiffOn ℝ q f (Icc a b)` (or `∀ k < q, DifferentiableOn` as you prefer, state the weakest
   you can manage), `v : Fin (q+1) → ℝ` strictly monotone with values in `[a, b]`, `f (v i) = 0`
   for all `i` → `∃ ξ ∈ Ioo a b, iteratedDeriv q f ξ = 0`. (Induction on `q` using
   `exists_deriv_eq_zero` between consecutive nodes.)
2. Lagrange remainder: with `v` injective in `[a, b]`, `f` `(q+1)`-times differentiable on
   `[a, b]`, `x ∈ Icc a b`: `∃ ξ ∈ Icc a b, f x − (Lagrange.interpolate Finset.univ v (f ∘ v)).eval x
   = iteratedDeriv (q+1) f ξ / (q+1)! * (Lagrange.nodal Finset.univ v).eval x`. (Standard
   auxiliary function `g(t) = f t − L t − K ω(t)` with `K` chosen so `g x = 0`, then item 1 with
   `q + 2` zeros.)
3. Chebyshev zeros: define `chebyshevZero q k = cos ((2k+1)π/(2q))` (name per STANDARDS; this is
   a definition, report it for `Basic.lean`) and prove `nodal_chebyshevZero :
   Lagrange.nodal Finset.univ (chebyshevZero q) = C (1/2^(q−1)) * T ℝ q` for `0 < q` (both monic
   of degree `q` with the same roots, `roots_T_real`, `roots_T_real_nodup`, `leadingCoeff_T`), hence
   `abs_eval_nodal_chebyshevZero_le : x ∈ Icc (−1) 1 → |nodal.eval x| ≤ 1/2^(q−1)`.
4. Chebyshev interpolation error: for `f` `(q+1)`-times differentiable on `[−1, 1]` with
   `∀ ξ ∈ Icc (−1) 1, |iteratedDeriv (q+1) f ξ| ≤ M`, interpolation at the `q+1` zeros of `T_{q+1}`
   satisfies `∀ x ∈ Icc (−1) 1, |f x − L.eval x| ≤ M / (2^q * (q+1)!)`.
5. Items 1–2 are the core; 3–4 are the payoff. Scaffold what does not close.

## Report
Per the Round 1 brief: files, every public declaration with status and atlas id, the exact check
commands with final output, helpers that belong in `Basic.lean`, Mathlib names found or missing.
