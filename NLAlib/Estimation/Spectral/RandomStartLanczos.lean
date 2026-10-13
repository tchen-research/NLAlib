import NLAlib.Estimation.Spectral.RandomStartPower
import NLAlib.Polynomial.Chebyshev.EvenChebyshevFilter
/-!
# Expected error of Gaussian random-start Lanczos

For a positive semidefinite `A` and a standard Gaussian start `b` (`gaussianVector ι`), the
relative error `(λ_max − θ_max)/λ_max` of the largest Ritz value of `K_{q+1}(A, b)` (`q`
matvecs, `lanczosRitzValue A b (q + 1)`) has expectation at most
`min(1, 4((log(2n) + 2 + log 2)² + 4)/((log 2)² q²))`, gap-free: Kuczyński–Woźniakowski's
random-start Lanczos bound. The deterministic step compares the Ritz value with the Rayleigh
quotient of a power of the even Chebyshev filter applied to `b` (the finite filter means
`one_sub_filter_mean_le_four_div_sq`, `exists_polynomial_filter_mean_le_log_sq`); the
probabilistic step is the logarithmic Gaussian overlap of `RandomStartPower`.

Source: Kuczyński–Woźniakowski (1992) [`kw92`], Thm 4.2 and §3. Atlas: `random-start-power`
(the Lanczos clause; a separate id `random-start-lanczos` is requested).
-/

noncomputable section
open Polynomial MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib

/-! ### Finite filter means (deterministic part) -/

section FilterMeans

variable {ι : Type*} [Fintype ι]

/-- **Finite filter means of a power of the even Chebyshev filter.** Let `d i ∈ [0, 1]` be
scaled eigenvalues with weights `g i ^ 2`, and let `H > 0` be at most the weight carried by the
positions with `d i = 1` (the top eigenvalue). If `ℓ log 2` dominates the logarithmic ratio
`log(∑ g_i²/H)`, then the relative deficiency of the filtered mean
`∑ d_i f_k(d_i)^{2ℓ} g_i² / ∑ f_k(d_i)^{2ℓ} g_i²` is at most `4/(2k+1)²`.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3 (deterministic part).
Deviation: the top weight `H` is any lower bound on the mass at the top eigenvalue (the source
takes one eigenvector coordinate). Helper for `random-start-power`. -/
theorem one_sub_filter_mean_le_four_div_sq (d g : ι → ℝ) {H : ℝ}
    (hd : ∀ i, d i ∈ Set.Icc 0 1) (hH : 0 < H)
    (hHtop : H ≤ ∑ i ∈ Finset.univ.filter (fun i => d i = 1), g i ^ 2) (k : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hLog : Real.log ((∑ i, g i ^ 2) / H) ≤ (ℓ : ℝ) * Real.log 2) :
    1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) /
      (∑ i, ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
        4 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  classical
  set D := ∑ i, ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2 with hDdef
  set G := ∑ i, g i ^ 2 with hGdef
  set δ := 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) with hδdef
  have hHD : H ≤ D := by
    refine hHtop.trans ?_
    calc ∑ i ∈ Finset.univ.filter (fun i => d i = 1), g i ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i => d i = 1),
            ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.1 hi).2, eval_evenChebyshevFilter_one, one_pow, one_pow, one_mul]
      _ ≤ D := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
  have hHG : H ≤ G :=
    hHtop.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _))
  have hD : 0 < D := hH.trans_le hHD
  have hG : 0 < G := hH.trans_le hHG
  have hδ : 0 ≤ δ := by rw [hδdef]; positivity
  have hRatio : G / H ≤ (2 : ℝ) ^ ℓ := by
    apply (Real.log_le_log_iff (div_pos hG hH) (by positivity)).mp
    rw [Real.log_pow]
    exact hLog
  have hEnergy : (1 / 2 : ℝ) ^ ℓ * G ≤ H := by
    have ht := (div_le_iff₀ hH).mp hRatio
    apply (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ ℓ)).mp
    calc
      (2 : ℝ) ^ ℓ * ((1 / 2 : ℝ) ^ ℓ * G) = G := by
        rw [← mul_assoc, ← mul_pow]
        norm_num
      _ ≤ (2 : ℝ) ^ ℓ * H := ht
  have hNum : D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
      δ * D + δ * (1 / 2 : ℝ) ^ ℓ * G := by
    rw [hDdef, hGdef]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_right
      (one_sub_mul_eval_evenChebyshevFilter_pow_sq_le (hd i) k hℓ) (sq_nonneg (g i))
    rw [hδdef]
    nlinarith
  have hNum' : D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) ≤
      2 * δ * D := by
    have h1 := mul_le_mul_of_nonneg_left hEnergy hδ
    have h2 := mul_le_mul_of_nonneg_left hHD hδ
    nlinarith
  have hResult : 1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) / D ≤
      2 * δ := by
    rw [show 1 - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2) / D =
      (D - (∑ i, d i * ((evenChebyshevFilter k).eval (d i) ^ ℓ) ^ 2 * g i ^ 2)) / D by
        rw [sub_div, div_self hD.ne']]
    apply (div_le_iff₀ hD).mpr
    nlinarith [hNum']
  rw [hδdef] at hResult
  convert hResult using 1
  ring

/-- **A filter polynomial with the gap-free squared-logarithmic rate.** Under the hypotheses of
`one_sub_filter_mean_le_four_div_sq`, for every `q ≥ 1` there is a polynomial `p` of degree at
most `q` with `p(1) = 1` whose filtered mean has relative deficiency at most
`4 (1 + log(∑ g_i²/H)/log 2)²/q²` (a power of the even Chebyshev filter, with the number of
factors chosen from the logarithmic ratio). Source: Kuczyński–Woźniakowski (1992) [`kw92`], §3.
Deviation: indexed by the degree `q` (matvecs); the polynomial may depend on the data. Helper for
`random-start-power`. -/
theorem exists_polynomial_filter_mean_le_log_sq (d g : ι → ℝ) {H : ℝ}
    (hd : ∀ i, d i ∈ Set.Icc 0 1) (hH : 0 < H)
    (hHtop : H ≤ ∑ i ∈ Finset.univ.filter (fun i => d i = 1), g i ^ 2) {q : ℕ} (hq : 1 ≤ q) :
    ∃ p : ℝ[X], p.natDegree ≤ q ∧ p.eval 1 = 1 ∧
      1 - (∑ i, d i * p.eval (d i) ^ 2 * g i ^ 2) / (∑ i, p.eval (d i) ^ 2 * g i ^ 2) ≤
        4 * (1 + Real.log ((∑ i, g i ^ 2) / H) / Real.log 2) ^ 2 / (q : ℝ) ^ 2 := by
  classical
  set L := Real.log ((∑ i, g i ^ 2) / H) with hLdef
  set ℓ := max 1 ⌈L / Real.log 2⌉₊ with hℓdef
  set k := q / ℓ with hkdef
  have hh : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hEnergy : H ≤ ∑ i, g i ^ 2 :=
    hHtop.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => sq_nonneg _))
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ hH).mpr (by simpa only [one_mul] using hEnergy))
  have hℓ : 1 ≤ ℓ := le_max_left _ _
  have hℓ0 : 0 < ℓ := by omega
  have hLog : L ≤ (ℓ : ℝ) * Real.log 2 := by
    have hc := Nat.le_ceil (L / Real.log 2)
    have hm : (⌈L / Real.log 2⌉₊ : ℝ) ≤ ℓ := by exact_mod_cast (le_max_right 1 _)
    exact (div_le_iff₀ hh).mp (hc.trans hm)
  have hℓUpper : (ℓ : ℝ) ≤ 1 + L / Real.log 2 := by
    rw [hℓdef, Nat.cast_max]
    apply max_le
    · linarith [div_nonneg hL hh.le]
    · have h := Nat.ceil_lt_add_one (div_nonneg hL hh.le)
      linarith
  have hDegree : ℓ * k ≤ q := by rw [hkdef]; exact Nat.mul_div_le _ _
  have hWidth : q ≤ ℓ * (2 * k + 1) := by
    have ht : q < (k + 1) * ℓ := (Nat.div_lt_iff_lt_mul hℓ0).mp (Nat.lt_succ_self k)
    have hu : (k + 1) * ℓ ≤ (2 * k + 1) * ℓ := Nat.mul_le_mul_right ℓ (by omega)
    exact ht.le.trans (hu.trans_eq (Nat.mul_comm _ _))
  refine ⟨evenChebyshevFilter k ^ ℓ,
    (natDegree_pow_le_of_le ℓ (natDegree_evenChebyshevFilter_le k)).trans hDegree,
    by simp only [eval_pow, eval_evenChebyshevFilter_one, one_pow], ?_⟩
  have h := one_sub_filter_mean_le_four_div_sq d g hd hH hHtop k hℓ hLog
  simp only [eval_pow]
  refine h.trans ?_
  have hm : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hC : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hw : (q : ℝ) ≤ (ℓ : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by exact_mod_cast hWidth
  have hs := pow_le_pow_left₀ hm.le hw 2
  rw [mul_pow] at hs
  calc
    4 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) ≤ 4 * (ℓ : ℝ) ^ 2 / (q : ℝ) ^ 2 := by
      apply (div_le_div_iff₀ (sq_pos_of_pos hC) (sq_pos_of_pos hm)).mpr
      nlinarith
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact pow_le_pow_left₀ (Nat.cast_nonneg ℓ) hℓUpper 2

end FilterMeans

/-! ### The Lanczos relative error -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The relative error of the largest Ritz value of `K_{q+1}(A, b)` (`q` matvecs) against the
spectral norm: `(‖A‖₂ − θ_max(K_{q+1}))/‖A‖₂` (`= (λ_max − θ_max)/λ_max` for positive
semidefinite `A`; junk value `0` at `A = 0`).
Source: Kuczyński–Woźniakowski (1992) [`kw92`], §2.
atlas: random-start-power -/
def lanczosRayleighRelativeError (A : Matrix ι ι ℝ) (b : ι → ℝ) (q : ℕ) : ℝ :=
  (specNorm A - lanczosRitzValue A b (q + 1)) / specNorm A

/-- The relative error of the zero matrix is `0`. Helper for `random-start-power`. -/
@[simp] theorem lanczosRayleighRelativeError_zero (b : ι → ℝ) (q : ℕ) :
    lanczosRayleighRelativeError (0 : Matrix ι ι ℝ) b q = 0 := by
  simp only [lanczosRayleighRelativeError, specNorm_zero, div_zero]

/-- The Lanczos relative error is nonnegative. Helper for `random-start-power`. -/
theorem lanczosRayleighRelativeError_nonneg (A : Matrix ι ι ℝ) (b : ι → ℝ) (q : ℕ) :
    0 ≤ lanczosRayleighRelativeError A b q :=
  div_nonneg (sub_nonneg.mpr (lanczosRitzValue_le_specNorm A b _)) (specNorm_nonneg A)

/-- The Lanczos relative error is at most `1`. Helper for `random-start-power`. -/
theorem lanczosRayleighRelativeError_le_one {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (b : ι → ℝ) (q : ℕ) :
    lanczosRayleighRelativeError A b q ≤ 1 := by
  by_cases hL : specNorm A = 0
  · simp only [lanczosRayleighRelativeError, hL, div_zero, zero_le_one]
  · have hLp : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hL)
    rw [lanczosRayleighRelativeError, div_le_one hLp]
    linarith [lanczosRitzValue_nonneg hA b (q + 1)]

/-- The Lanczos relative error is measurable in the start. Helper for `random-start-power`. -/
theorem measurable_lanczosRayleighRelativeError {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (q : ℕ) :
    Measurable (fun b : ι → ℝ => lanczosRayleighRelativeError A b q) :=
  (measurable_const.sub (measurable_lanczosRitzValue hA (q + 1))).div_const _

/-- **Random-start Lanczos, deterministic bound.** Let `A` be positive semidefinite with
`‖A‖₂ > 0`, `u` a unit eigenvector of the top eigenvalue `λ₀(A)`, and `u ⬝ b ≠ 0`. Then after
`q ≥ 1` matvecs the relative error of the largest Ritz value obeys the squared logarithmic-overlap
bound `(λ_max − θ_max)/λ_max ≤ 4 (1 + log(‖b‖²/(u ⬝ b)²)/log 2)²/q²`. No spectral gap or
simplicity of the top eigenvalue is required.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], Thm 4.2 (deterministic step, §3).
atlas: random-start-power (partial) -/
theorem lanczosRayleighRelativeError_le_log_sq [Nonempty ι] {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hL : 0 < specNorm A) {u : ι → ℝ}
    (hu : A *ᵥ u = hA.isHermitian.eigenvalues₀ 0 • u) (hu1 : ‖WithLp.toLp 2 u‖ = 1)
    {b : ι → ℝ} (hb : u ⬝ᵥ b ≠ 0) {q : ℕ} (hq : 1 ≤ q) :
    lanczosRayleighRelativeError A b q ≤
      4 * (1 + Real.log (‖WithLp.toLp 2 b‖ ^ 2 / (u ⬝ᵥ b) ^ 2) / Real.log 2) ^ 2 /
        (q : ℝ) ^ 2 := by
  have hH := hA.isHermitian
  set L := specNorm A with hLdef
  have hL0 : hH.eigenvalues₀ 0 = L := hA.specNorm_eq_eigenvalues₀_zero.symm
  let c := fun i => (hH.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b
  let a := fun i => (hH.eigenvectorBasis i : ι → ℝ) ⬝ᵥ u
  let d := fun i => hH.eigenvalues i / L
  have hd : ∀ i, d i ∈ Set.Icc 0 1 := fun i => by
    constructor
    · exact div_nonneg (hA.eigenvalues_nonneg i) hL.le
    · apply (div_le_one hL).mpr
      rw [← hL0]; exact hH.eigenvalues_le_eigenvalues₀_zero i
  -- the mass of `b` at the top eigenvalue dominates `(u ⬝ b)²`
  have hHtop : (u ⬝ᵥ b) ^ 2 ≤ ∑ i ∈ Finset.univ.filter (fun i => d i = 1), c i ^ 2 := by
    have huu : u ⬝ᵥ u = 1 := by rw [← norm_toLp_sq_eq_dotProduct_self, hu1, one_pow]
    have haa : ∑ i, a i ^ 2 = 1 := by
      show ∑ i, ((hH.eigenvectorBasis i : ι → ℝ) ⬝ᵥ u) ^ 2 = 1
      rw [sum_sq_eigenvectorBasis_dotProduct hH u, huu]
    have hub : u ⬝ᵥ b = ∑ i, a i * c i :=
      dotProduct_eq_sum_eigenvectorBasis_dotProduct_mul hH u b
    have hzero : ∀ i, d i ≠ 1 → a i = 0 := fun i hi => by
      rcases mul_eq_zero.1
        (eigenvalues_sub_mul_eigenvectorBasis_dotProduct_eq_zero hH hu i) with h | h
      · exact absurd (show d i = 1 by
          show hH.eigenvalues i / L = 1
          rw [sub_eq_zero.1 h, hL0]; exact div_self hL.ne') hi
      · exact h
    have hsum : ∑ i, a i * c i = ∑ i ∈ Finset.univ.filter (fun i => d i = 1), a i * c i := by
      have hz : ∑ i ∈ Finset.univ.filter (fun i => d i ≠ 1), a i * c i = 0 :=
        Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_filter.1 hi).2, zero_mul]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => d i = 1), hz, add_zero]
    rw [hub, hsum]
    refine (Finset.sum_mul_sq_le_sq_mul_sq _ _ _).trans ?_
    refine mul_le_of_le_one_left (Finset.sum_nonneg fun i _ => sq_nonneg _) ?_
    rw [← haa]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
  have hHpos : 0 < (u ⬝ᵥ b) ^ 2 := by positivity
  obtain ⟨p, hpDegree, hpOne, hpMean⟩ :=
    exists_polynomial_filter_mean_le_log_sq d c hd hHpos hHtop hq
  let P := p.comp (C (L⁻¹) * X)
  have hpEval : ∀ i, P.eval (hH.eigenvalues i) = p.eval (d i) := by
    intro i
    simp only [P, eval_comp, eval_mul, eval_C, eval_X, d, div_eq_mul_inv]
    rw [mul_comm L⁻¹]
  have hPDegree : P.natDegree ≤ q := by
    have hX : (C (L⁻¹) * X : ℝ[X]).natDegree ≤ 1 :=
      natDegree_C_mul_le _ _ |>.trans natDegree_X_le
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left p.natDegree hX).trans
      (by simpa only [mul_one] using hpDegree))
  let y := aeval A P *ᵥ b
  have hy : y ∈ krylovSpace A b (q + 1) := (mem_krylovSpace_iff A b (q + 1) _).mpr
    ⟨P, (degree_le_of_natDegree_le hPDegree).trans_lt
      (by exact_mod_cast Nat.lt_succ_self q), rfl⟩
  have hD : y ⬝ᵥ y = ∑ i, p.eval (d i) ^ 2 * c i ^ 2 := by
    simpa only [y, hpEval] using dotProduct_aeval_mulVec_self_eq_sum hH P b
  have hN : y ⬝ᵥ (A *ᵥ y) = L * (∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) := by
    have h := quadForm_aeval_mulVec_eq_sum hH P b
    change y ⬝ᵥ (A *ᵥ y) =
      ∑ i, hH.eigenvalues i * P.eval (hH.eigenvalues i) ^ 2 * c i ^ 2 at h
    rw [h, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hpEval]
    simp only [d]
    field_simp
  have hDp : 0 < ∑ i, p.eval (d i) ^ 2 * c i ^ 2 := by
    refine hHpos.trans_le (hHtop.trans ?_)
    calc ∑ i ∈ Finset.univ.filter (fun i => d i = 1), c i ^ 2
        = ∑ i ∈ Finset.univ.filter (fun i => d i = 1), p.eval (d i) ^ 2 * c i ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [(Finset.mem_filter.1 hi).2, hpOne, one_pow, one_mul]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun i _ _ => by positivity)
  have hRQ : rayleighQuotient A y =
      L * ((∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) / (∑ i, p.eval (d i) ^ 2 * c i ^ 2)) := by
    rw [rayleighQuotient_eq_div, hN, hD, mul_div_assoc]
  have hCompare := rayleighQuotient_le_lanczosRitzValue_of_mem hA b (q + 1) hy
  have hError : lanczosRayleighRelativeError A b q ≤
      1 - (∑ i, d i * p.eval (d i) ^ 2 * c i ^ 2) / (∑ i, p.eval (d i) ^ 2 * c i ^ 2) := by
    rw [hRQ] at hCompare
    rw [lanczosRayleighRelativeError, ← hLdef]
    apply (div_le_iff₀ hL).mpr
    nlinarith
  have hParseval : (∑ i, c i ^ 2) = ‖WithLp.toLp 2 b‖ ^ 2 := by
    rw [norm_toLp_sq_eq_dotProduct_self]
    exact sum_sq_eigenvectorBasis_dotProduct hH b
  rw [hParseval] at hpMean
  exact hError.trans hpMean

/-- **Random-start Lanczos, expected relative error.** For a positive semidefinite
`A : Matrix ι ι ℝ` and a standard Gaussian start `b`, after `q ≥ 1` matvecs
`𝔼[(λ_max − θ_max(K_{q+1}(A, b)))/λ_max] ≤ min(1, 4((log(2|ι|) + 2 + log 2)² + 4)/((log 2)² q²))`.
Every dimension, repeated top eigenvalues and the zero matrix are included.
Source: Kuczyński–Woźniakowski (1992) [`kw92`], Thm 4.2 (the gap-free bound).
Deviation: indexed by matvecs (`K_{q+1}`, `/q²`).
atlas: random-start-power -/
theorem integral_lanczosRayleighRelativeError_gaussianVector_le {A : Matrix ι ι ℝ}
    (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) :
    (∫ b, lanczosRayleighRelativeError A b q ∂(gaussianVector ι)) ≤
      min 1 (4 * ((Real.log (2 * (Fintype.card ι : ℝ)) + 2 + Real.log 2) ^ 2 + 4) /
        ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by
  let μ := gaussianVector ι
  let T := Real.log (2 * (Fintype.card ι : ℝ))
  let h := Real.log 2
  let m := (q : ℝ)
  have hh : 0 < h := Real.log_pos (by norm_num)
  have hm : 0 < m := by dsimp only [m]; exact_mod_cast (by omega : 0 < q)
  have hfm := measurable_lanczosRayleighRelativeError hA.isHermitian q
  have hfi : Integrable (fun b => lanczosRayleighRelativeError A b q) μ := by
    refine (integrable_const (1 : ℝ)).mono' hfm.aestronglyMeasurable ?_
    exact ae_of_all _ fun b => by
      rw [Real.norm_of_nonneg (lanczosRayleighRelativeError_nonneg A b q)]
      exact lanczosRayleighRelativeError_le_one hA b q
  have hOne : (∫ b, lanczosRayleighRelativeError A b q ∂μ) ≤ 1 := by
    have hBound := integral_mono hfi (integrable_const (1 : ℝ))
      (fun b => lanczosRayleighRelativeError_le_one hA b q)
    simpa only [integral_const, probReal_univ, one_smul] using hBound
  apply le_min hOne
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hzero : A = 0 := Subsingleton.elim _ _
    rw [hzero]
    simp only [lanczosRayleighRelativeError_zero, integral_zero]
    positivity
  by_cases hZero : specNorm A = 0
  · simp only [lanczosRayleighRelativeError, hZero, div_zero, integral_zero]
    positivity
  · have hL : 0 < specNorm A := (specNorm_nonneg A).lt_of_ne (Ne.symm hZero)
    have hH := hA.isHermitian
    set i₀ : ι := Fintype.equivOfCardEq (Fintype.card_fin _) (0 : Fin (Fintype.card ι))
    set u : ι → ℝ := (hH.eigenvectorBasis i₀ : ι → ℝ)
    have hu : A *ᵥ u = hH.eigenvalues₀ 0 • u := by
      rw [← hH.eigenvalues_equivOfCardEq]
      exact hH.mulVec_eigenvectorBasis i₀
    have hu1 : ‖WithLp.toLp 2 u‖ = 1 := by
      have := hH.eigenvectorBasis.orthonormal.1 i₀
      simpa [u] using this
    let C := fun b : ι → ℝ => fun i => (hH.eigenvectorBasis i : ι → ℝ) ⬝ᵥ b
    let Lf := fun c : ι → ℝ => Real.log ((∑ i, c i ^ 2) / (c i₀) ^ 2)
    have hMP : MeasurePreserving C μ μ :=
      measurePreserving_eigenvectorBasis_dotProduct_gaussianVector hH
    have hLm : Measurable Lf := by dsimp only [Lf]; fun_prop
    have hL2m : Measurable (fun c => Lf c ^ 2) := hLm.pow_const 2
    obtain ⟨hLI, hLV, hLI2, hLV2⟩ := log_overlap_moments_gaussianVector (ι := ι) i₀
    have hLCI : Integrable (fun b => Lf (C b)) μ := by
      apply (integrable_map_measure hLm.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCI2 : Integrable (fun b => Lf (C b) ^ 2) μ := by
      apply (integrable_map_measure hL2m.aestronglyMeasurable hMP.measurable.aemeasurable).mp
      rwa [hMP.map_eq]
    have hLCV : (∫ b, Lf (C b) ∂μ) ≤ T + 2 := by
      have he := integral_map (μ := μ) hMP.measurable.aemeasurable hLm.aestronglyMeasurable
      rw [hMP.map_eq] at he
      exact he.symm.trans_le hLV
    have hLCV2 : (∫ b, Lf (C b) ^ 2 ∂μ) ≤ T ^ 2 + 4 * T + 8 := by
      have he := integral_map (μ := μ) hMP.measurable.aemeasurable hL2m.aestronglyMeasurable
      rw [hMP.map_eq] at he
      exact he.symm.trans_le hLV2
    let F := fun b : ι → ℝ => (1 + Lf (C b) / h) ^ 2
    have hFEq : ∀ b, F b = (Lf (C b) ^ 2 + 2 * h * Lf (C b) + h ^ 2) / h ^ 2 := by
      intro b
      dsimp only [F]
      field_simp [hh.ne']
      ring
    have hFI : Integrable F μ := by
      have hsum : Integrable (fun b => Lf (C b) ^ 2 + 2 * h * Lf (C b) + h ^ 2) μ :=
        (hLCI2.add (hLCI.const_mul (2 * h))).add (integrable_const _)
      exact (hsum.div_const (h ^ 2)).congr (ae_of_all _ fun b => (hFEq b).symm)
    have hFV : (∫ b, F b ∂μ) ≤ ((T + 2 + h) ^ 2 + 4) / h ^ 2 := by
      have he : (∫ b, F b ∂μ) =
          ((∫ b, Lf (C b) ^ 2 ∂μ) + 2 * h * (∫ b, Lf (C b) ∂μ) + h ^ 2) / h ^ 2 := by
        have hsI : Integrable (fun b => Lf (C b) ^ 2 + 2 * h * Lf (C b)) μ :=
          hLCI2.add (hLCI.const_mul (2 * h))
        have hAdd : (∫ b, Lf (C b) ^ 2 + 2 * h * Lf (C b) + h ^ 2 ∂μ) =
            (∫ b, Lf (C b) ^ 2 + 2 * h * Lf (C b) ∂μ) + ∫ _ : ι → ℝ, h ^ 2 ∂μ :=
          integral_add hsI (integrable_const (h ^ 2))
        have hAdd2 : (∫ b, Lf (C b) ^ 2 + 2 * h * Lf (C b) ∂μ) =
            (∫ b, Lf (C b) ^ 2 ∂μ) + ∫ b, 2 * h * Lf (C b) ∂μ :=
          integral_add hLCI2 (hLCI.const_mul (2 * h))
        rw [integral_congr_ae (ae_of_all _ hFEq), integral_div, hAdd, hAdd2, integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul]
      rw [he]
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      have hc := mul_le_mul_of_nonneg_left hLCV (by positivity : (0 : ℝ) ≤ 2 * h)
      nlinarith
    have hNZ := ae_eigenvectorBasis_dotProduct_ne_zero_gaussianVector hH i₀
    have hPoint : (fun b => lanczosRayleighRelativeError A b q) ≤ᵐ[μ]
        fun b => 4 * F b / m ^ 2 := by
      filter_upwards [hNZ] with b hb
      have hs := lanczosRayleighRelativeError_le_log_sq hA hL hu hu1 hb hq
      rw [norm_toLp_sq_eq_dotProduct_self, ← sum_sq_eigenvectorBasis_dotProduct hH b] at hs
      exact hs
    have hBound := integral_mono_ae hfi ((hFI.const_mul 4).div_const (m ^ 2)) hPoint
    rw [integral_div, integral_const_mul] at hBound
    refine hBound.trans ?_
    have hb := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFV (by norm_num : (0 : ℝ) ≤ 4)) (sq_nonneg m)
    refine hb.trans_eq ?_
    dsimp only [T, h, m]
    ring

/-- `integral_lanczosRayleighRelativeError_gaussianVector_le` for a random start with the
standard Gaussian law on an abstract probability space. Source: Kuczyński–Woźniakowski (1992)
[`kw92`], Thm 4.2.
atlas: random-start-power -/
theorem integral_lanczosRayleighRelativeError_le_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {q : ℕ} (hq : 1 ≤ q) {G : Ω → ι → ℝ}
    (hG : HasLaw G (gaussianVector ι) μ) :
    (∫ ω, lanczosRayleighRelativeError A (G ω) q ∂μ) ≤
      min 1 (4 * ((Real.log (2 * (Fintype.card ι : ℝ)) + 2 + Real.log 2) ^ 2 + 4) /
        ((Real.log 2) ^ 2 * (q : ℝ) ^ 2)) := by
  have he : (∫ ω, lanczosRayleighRelativeError A (G ω) q ∂μ) = _ :=
    hG.integral_comp (measurable_lanczosRayleighRelativeError hA.isHermitian q).aestronglyMeasurable
  exact he.trans_le (integral_lanczosRayleighRelativeError_gaussianVector_le hA hq)

end NLAlib
