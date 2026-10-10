import NLAlib.Estimation.HutchinsonTail
import NLAlib.Krylov.GaussQuadrature
import NLAlib.Polynomial.Approximation

/-!
# Stochastic Lanczos quadrature for `tr f(A)`, and the case `f(x) = 1/x`

Stochastic Lanczos quadrature (SLQ) estimates `tr f(A)` by averaging, over test vectors `g_k`,
the Gauss-quadrature values `(Q_kᵀ g_k)ᵀ f(Q_kᵀ A Q_k) (Q_kᵀ g_k)`, where `Q_k` is an orthonormal
basis of (a space containing) the Krylov space `K_q(A, g_k)` (`NLAlib.slqEstimate`).

* `NLAlib.abs_slqEstimate_sub_hutchinsonEstimate_le`: deterministic quadrature error,
  `|SLQ − tr_m f(A)| ≤ 2E · (1/m) ∑ₖ ‖g_k‖²` when `|f − p| ≤ E` on the spectral interval for some
  `p` of degree `≤ 2q − 1`.
* `NLAlib.abs_slqEstimate_inv_sub_hutchinsonEstimate_le`: the same for `f(x) = 1/x` with the
  proved Chebyshev rate `E = (2/a)((√b − √a)/(√b + √a))^{2q}` on `[a, b]`.
* `NLAlib.measure_le_abs_slqEstimate_inv_sub_trace_le_of_standardGaussian`: with Gaussian test
  vectors, `|SLQ − tr A⁻¹| ≥ t + 2E(n + s)` has probability at most the sum of the Hutchinson tail
  for `A⁻¹` at `t` and for `I` at `s`.

Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1 (constants differ); Golub–Meurant (2010)
[`gm10`], Ch. 6–7. Atlas: `slq-error` (the case `f = 1/x`); uses `lanczos-gauss-quadrature`,
`hutchinson-tail`, `inverse-polynomial-approx`.
-/

noncomputable section

open scoped Matrix
open MeasureTheory ProbabilityTheory Real
open scoped Matrix.Norms.L2Operator

namespace NLAlib

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]
variable {r : Type*} [Fintype r] [DecidableEq r]

/-- The stochastic Lanczos quadrature estimate
`(1/m) ∑ₖ (Q_kᵀ g_k)ᵀ f(Q_kᵀ A Q_k) (Q_kᵀ g_k)` with test vectors `g_k = G(·, k)` and bases
`Q_k`. With the Lanczos basis, `Q_kᵀ g_k = ‖g_k‖ e₁` and the summand is `‖g_k‖² f(T_k)₁₁`.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], eq. (5). Atlas: `slq-error`.
Deviation: any bases `Q_k` (the error theorems require `K_q(A, g_k) ⊆ range Q_k`). -/
def slqEstimate (A : Matrix n n ℝ) (f : ℝ → ℝ) (Q : κ → Matrix n r ℝ) (G : n → κ → ℝ) : ℝ :=
  (∑ k, ((Q k)ᵀ *ᵥ fun i => G i k) ⬝ᵥ
    (cfc f ((Q k)ᵀ * A * Q k) *ᵥ ((Q k)ᵀ *ᵥ fun i => G i k))) / Fintype.card κ

omit [DecidableEq n] in
/-- `tr_m(I) = (1/m) ∑ₖ ‖g_k‖²`. Atlas: `slq-error` (helper). -/
theorem hutchinsonEstimate_one [DecidableEq n] (G : n → κ → ℝ) :
    hutchinsonEstimate (1 : Matrix n n ℝ) G =
      (∑ k, (fun i => G i k) ⬝ᵥ (fun i => G i k)) / Fintype.card κ := by
  simp [hutchinsonEstimate, quadForm]

/-- **SLQ quadrature error, deterministic.** If `A` is symmetric with spectrum in `[a, c]`,
each `Q_k` has orthonormal columns with `K_q(A, g_k) ⊆ range Q_k` (`q ≥ 1`), and
`|f − p| ≤ E` on `[a, c]` for a polynomial `p` of degree at most `2q − 1`, then
`|SLQ − tr_m f(A)| ≤ 2E · tr_m(I)`, where `tr_m` is the Hutchinson estimator with the same
test vectors and `tr_m(I) = (1/m) ∑ₖ ‖g_k‖²`.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], proof of Thm 4.1 (Lemma 4.2). Atlas: `slq-error`;
uses `lanczos-gauss-quadrature`. -/
theorem abs_slqEstimate_sub_hutchinsonEstimate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {Q : κ → Matrix n r ℝ} (hQ : ∀ k, HasOrthonormalCols (Q k)) (G : n → κ → ℝ) {q : ℕ}
    (hq : 0 < q) (hK : ∀ k, krylovSpace A (fun i => G i k) q ≤ LinearMap.range (Q k).mulVecLin)
    {f : ℝ → ℝ} {p : Polynomial ℝ} (hp : p.natDegree ≤ 2 * q - 1) {a c E : ℝ}
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a c)
    (hfp : ∀ x ∈ Set.Icc a c, |f x - p.eval x| ≤ E) :
    |slqEstimate A f Q G - hutchinsonEstimate (cfc f A) G| ≤
      2 * E * hutchinsonEstimate (1 : Matrix n n ℝ) G := by
  rw [hutchinsonEstimate_one, slqEstimate, hutchinsonEstimate, ← sub_div, abs_div,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card κ)), mul_div_assoc', Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun k _ => ?_)) (Nat.cast_nonneg _)
  rw [abs_sub_comm]
  exact abs_dotProduct_cfc_mulVec_sub_le_of_krylovSpace_le hA (hQ k) _ hq (hK k) hp hspec hfp

/-- **SLQ quadrature error for `f(x) = 1/x`.** If `A` is symmetric with spectrum in `[a, b]`,
`0 < a < b`, each `Q_k` has orthonormal columns with `K_q(A, g_k) ⊆ range Q_k` (`q ≥ 1`), then
`|SLQ(1/x) − tr_m(f(A))| ≤ 2 (2/a) ((√b − √a)/(√b + √a))^{2q} · tr_m(I)` with `f(A) = cfc (1/x) A`
(`= A⁻¹`). Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1 and §4.2 (inverse); the rate is the
CG/Chebyshev rate of `inverse-polynomial-approx`. Atlas: `slq-error`; uses
`lanczos-gauss-quadrature`, `inverse-polynomial-approx`. -/
theorem abs_slqEstimate_inv_sub_hutchinsonEstimate_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b)
    {Q : κ → Matrix n r ℝ} (hQ : ∀ k, HasOrthonormalCols (Q k)) (G : n → κ → ℝ) {q : ℕ}
    (hq : 0 < q) (hK : ∀ k, krylovSpace A (fun i => G i k) q ≤ LinearMap.range (Q k).mulVecLin) :
    |slqEstimate A (fun x : ℝ => 1 / x) Q G - hutchinsonEstimate (cfc (fun x : ℝ => 1 / x) A) G| ≤
      2 * ((2 / a) * ((√b - √a) / (√b + √a)) ^ (2 * q)) *
        hutchinsonEstimate (1 : Matrix n n ℝ) G := by
  obtain ⟨p, hpdeg, hpE⟩ := exists_degree_lt_abs_eval_sub_inv_le (2 * q) ha hab
  have hp : p.natDegree ≤ 2 * q - 1 := by
    rcases eq_or_ne p 0 with h0 | h0
    · simp [h0]
    · have := (Polynomial.natDegree_lt_iff_degree_lt h0).2 hpdeg
      omega
  exact abs_slqEstimate_sub_hutchinsonEstimate_le hA hQ G hq hK hp hspec
    (fun x hx => by rw [abs_sub_comm]; exact hpE x hx)

/-- `‖I‖_F² = n`. Atlas: `slq-error` (helper). -/
theorem frobNorm_one_sq : frobNorm (1 : Matrix n n ℝ) ^ 2 = Fintype.card n := by
  rw [frobNorm_sq, frobSq_eq_sum_sq]
  simp [Matrix.one_apply]

/-- **SLQ for `tr A⁻¹`, Gaussian test vectors.** Let `A` be symmetric with spectrum in `[a, b]`,
`0 < a < b`, `G : n → κ → ℝ` with independent standard Gaussian entries (`m = |κ|` test
vectors), and `Q(ω)_k` orthonormal with `K_q(A, g_k) ⊆ range Q(ω)_k`, `q ≥ 1`. With
`E = (2/a)((√b − √a)/(√b + √a))^{2q}` and `c = 1/(256e²)`, for `t, s ≥ 0`:
`P(|SLQ − tr f(A)| ≥ t + 2E(n + s)) ≤ 2exp(−c min(m t²/‖f(A)‖_F², m t/‖f(A)‖))
  + 2exp(−c min(m s²/n, m s))`, where `f(A) = cfc (1/x) A = A⁻¹`.
Source: Ubaru–Chen–Saad (2017) [`ucs17`], Thm 4.1 (with Hanson–Wright in place of their
Rademacher tail; constants differ). Atlas: `slq-error` (case `f = 1/x`); uses
`lanczos-gauss-quadrature`, `hutchinson-tail`, `inverse-polynomial-approx`. -/
theorem measure_le_abs_slqEstimate_inv_sub_trace_le_of_standardGaussian [Nonempty n]
    [Nonempty κ] [DecidableEq κ] {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc a b) {G : Ω → n → κ → ℝ}
    (hind : iIndepFun (fun (e : n × κ) ω => G ω e.1 e.2) μ)
    (hlaw : ∀ e : n × κ, IsStandardGaussian μ (fun ω => G ω e.1 e.2))
    {Q : Ω → κ → Matrix n r ℝ} (hQ : ∀ ω k, HasOrthonormalCols (Q ω k)) {q : ℕ} (hq : 0 < q)
    (hK : ∀ ω k, krylovSpace A (fun i => G ω i k) q ≤ LinearMap.range (Q ω k).mulVecLin)
    {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    (μ {ω | t + 2 * ((2 / a) * ((√b - √a) / (√b + √a)) ^ (2 * q)) * (Fintype.card n + s) ≤
        |slqEstimate A (fun x : ℝ => 1 / x) (Q ω) (G ω) - (cfc (fun x : ℝ => 1 / x) A).trace|}).toReal ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
          min (Fintype.card κ * t ^ 2 / frobNorm (cfc (fun x : ℝ => 1 / x) A) ^ 2)
            (Fintype.card κ * t / specNorm (cfc (fun x : ℝ => 1 / x) A))) +
        2 * exp (-(1 / (256 * exp 1 ^ 2)) *
          min (Fintype.card κ * s ^ 2 / Fintype.card n) (Fintype.card κ * s)) := by
  set E := (2 / a) * ((√b - √a) / (√b + √a)) ^ (2 * q)
  set F := cfc (fun x : ℝ => 1 / x) A
  have hE : 0 ≤ E := by
    have h1 : 0 ≤ √b - √a := sub_nonneg.2 (Real.sqrt_le_sqrt hab.le)
    have h2 : 0 < √b + √a := by positivity
    positivity
  -- the two good events
  have hsub : {ω | t + 2 * E * (Fintype.card n + s) ≤
      |slqEstimate A (fun x : ℝ => 1 / x) (Q ω) (G ω) - F.trace|} ⊆
      {ω | t ≤ |hutchinsonEstimate F (G ω) - F.trace|} ∪
        {ω | s ≤ |hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) - (1 : Matrix n n ℝ).trace|} := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le] at hnot hω
    have hdet := abs_slqEstimate_inv_sub_hutchinsonEstimate_le hA ha hab hspec (hQ ω) (G ω) hq
      (hK ω)
    have htr : (1 : Matrix n n ℝ).trace = Fintype.card n := by simp
    rw [htr] at hnot
    have h1 : hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) < Fintype.card n + s := by
      have := (abs_lt.1 hnot.2).2; linarith
    have h2 : 2 * E * hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) ≤
        2 * E * (Fintype.card n + s) :=
      mul_le_mul_of_nonneg_left h1.le (by positivity)
    have h3 : |slqEstimate A (fun x : ℝ => 1 / x) (Q ω) (G ω) - F.trace| ≤
        |slqEstimate A (fun x : ℝ => 1 / x) (Q ω) (G ω) - hutchinsonEstimate F (G ω)| +
          |hutchinsonEstimate F (G ω) - F.trace| := abs_sub_le _ _ _
    linarith [hnot.1]
  have hF := measure_le_abs_hutchinsonEstimate_sub_trace_le_of_standardGaussian F hind hlaw t ht
  have hI := measure_le_abs_hutchinsonEstimate_sub_trace_le_of_standardGaussian
    (1 : Matrix n n ℝ) hind hlaw s hs
  -- simplify the identity tail
  have hspec1 : 0 < specNorm (1 : Matrix n n ℝ) := by
    rw [specNorm_eq_norm]; exact norm_pos_iff.2 one_ne_zero
  have hI' : 2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * s ^ 2 / frobNorm (1 : Matrix n n ℝ) ^ 2)
          (Fintype.card κ * s / specNorm (1 : Matrix n n ℝ))) ≤
      2 * exp (-(1 / (256 * exp 1 ^ 2)) *
        min (Fintype.card κ * s ^ 2 / Fintype.card n) (Fintype.card κ * s)) := by
    rw [frobNorm_one_sq]
    gcongr 2 * exp ?_
    rw [neg_mul, neg_mul, neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_left (min_le_min le_rfl ?_) (by positivity)
    calc (Fintype.card κ : ℝ) * s = Fintype.card κ * s / 1 := (div_one _).symm
      _ ≤ Fintype.card κ * s / specNorm (1 : Matrix n n ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hspec1 specNorm_one_le
  calc (μ {ω | t + 2 * E * (Fintype.card n + s) ≤
        |slqEstimate A (fun x : ℝ => 1 / x) (Q ω) (G ω) - F.trace|}).toReal
      ≤ (μ ({ω | t ≤ |hutchinsonEstimate F (G ω) - F.trace|} ∪
          {ω | s ≤ |hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) -
            (1 : Matrix n n ℝ).trace|})).toReal := measureReal_mono hsub
    _ ≤ (μ {ω | t ≤ |hutchinsonEstimate F (G ω) - F.trace|}).toReal +
          (μ {ω | s ≤ |hutchinsonEstimate (1 : Matrix n n ℝ) (G ω) -
            (1 : Matrix n n ℝ).trace|}).toReal := measureReal_union_le _ _
    _ ≤ _ := add_le_add hF (hI.trans hI')

end NLAlib
