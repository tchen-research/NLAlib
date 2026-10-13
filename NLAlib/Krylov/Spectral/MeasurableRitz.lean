import NLAlib.Krylov.Spaces.Polynomial
import NLAlib.Matrix.Spectral.PowerRayleigh
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The largest Ritz value of a Krylov space, and its measurability

`lanczosRitzValue A b q` is the largest Ritz value of `K_q(A, b)`: the supremum of the Rayleigh
quotients `xᵀAx/xᵀx` over `x ∈ K_q(A, b)` (for `Q` an orthonormal basis of `K_q` this is the
largest eigenvalue of `QᵀAQ`, the Lanczos estimate of `λ_max(A)`). The countable form
`lanczosRitzValue_eq_iSup_rat` (a supremum over rational coefficient vectors, by density) gives
measurability in the starting vector `b` (`measurable_lanczosRitzValue`), which the random-start
Lanczos bounds (`NLAlib.Estimation.Spectral.RandomStartLanczos`) need.

Source: Kuczyński–Woźniakowski (1992) [`kw92`], §2 (the Lanczos estimate as a Rayleigh
supremum). Atlas: `random-start-lanczos` (definition and measurability).
-/

noncomputable section
open scoped Matrix
open MeasureTheory
namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The vector of `K_q(A, b)` with coefficients `c` in the Krylov generators, `∑ⱼ cⱼ Aʲ b`.
Helper for `random-start-lanczos`. -/
def krylovCoefficientVector (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    (c : Fin q → ℝ) : n → ℝ := ∑ j : Fin q, c j • ((A ^ (j : ℕ)) *ᵥ b)

/-- `K_q(A, b)` is the set of coefficient vectors (including `q = 0`). Helper for
`random-start-lanczos`. -/
theorem mem_krylovSpace_iff_exists_coefficients (A : Matrix n n ℝ) (b : n → ℝ)
    (q : ℕ) (y : n → ℝ) :
    y ∈ krylovSpace A b q ↔ ∃ c : Fin q → ℝ, krylovCoefficientVector A b c = y := by
  exact Submodule.mem_span_range_iff_exists_fun ℝ

/-- Every coefficient vector lies in `K_q(A, b)`. Helper for `random-start-lanczos`. -/
theorem krylovCoefficientVector_mem (A : Matrix n n ℝ) (b : n → ℝ) {q : ℕ}
    (c : Fin q → ℝ) : krylovCoefficientVector A b c ∈ krylovSpace A b q :=
  (mem_krylovSpace_iff_exists_coefficients A b q _).mpr ⟨c, rfl⟩

/-- **The largest Ritz value of `K_q(A, b)`**: the supremum of the Rayleigh quotients
`rayleighQuotient A x = xᵀAx/xᵀx` over `x ∈ K_q(A, b)` (junk value `0` of the Rayleigh quotient
at `x = 0`, so the supremum is at least `0`). Source: Kuczyński–Woźniakowski (1992) [`kw92`],
§2; Parlett (1998), Thm 11.4.1 (Rayleigh–Ritz).
atlas: random-start-lanczos -/
def lanczosRitzValue (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) : ℝ :=
  sSup (rayleighQuotient A '' (krylovSpace A b q : Set (n → ℝ)))

omit [DecidableEq n] in
/-- The real Rayleigh quotient as a quotient of dot products. Helper. -/
theorem rayleighQuotient_eq_div (A : Matrix n n ℝ) (x : n → ℝ) :
    rayleighQuotient A x = x ⬝ᵥ (A *ᵥ x) / (x ⬝ᵥ x) := by
  rw [rayleighQuotient_def, quadForm_def, star_trivial, RCLike.re_to_real, RCLike.re_to_real]

/-- A Rayleigh quotient is at most the spectral norm: `xᵀAx/xᵀx ≤ ‖A‖₂` (any real `A`, including
`x = 0`). Helper for `random-start-lanczos`. -/
theorem rayleighQuotient_le_specNorm (A : Matrix n n ℝ) (x : n → ℝ) :
    rayleighQuotient A x ≤ specNorm A := by
  rw [rayleighQuotient_eq_div]
  rcases eq_or_lt_of_le (dotProduct_self_nonneg x) with h0 | hpos
  · rw [← h0, div_zero]; exact specNorm_nonneg A
  · rw [div_le_iff₀ hpos]
    have h := abs_re_star_dotProduct_mulVec_le_specNorm A x
    rw [star_trivial, RCLike.re_to_real, norm_toLp_sq_eq_dotProduct_self] at h
    exact (le_abs_self _).trans h

/-- The Rayleigh quotients over a Krylov space are bounded above. Helper. -/
private lemma bddAbove_image (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    BddAbove (rayleighQuotient A '' (krylovSpace A b q : Set (n → ℝ))) :=
  ⟨specNorm A, by rintro _ ⟨y, _, rfl⟩; exact rayleighQuotient_le_specNorm A y⟩

/-- **Every Krylov vector has Rayleigh quotient at most the largest Ritz value.** Source:
Parlett (1998), Thm 11.4.1. Helper for `random-start-lanczos`. -/
theorem rayleighQuotient_le_lanczosRitzValue_of_mem (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ)
    {y : n → ℝ} (hy : y ∈ krylovSpace A b q) :
    rayleighQuotient A y ≤ lanczosRitzValue A b q :=
  le_csSup (bddAbove_image A b q) ⟨y, hy, rfl⟩

/-- The largest Ritz value is at most the spectral norm. Helper for `random-start-lanczos`. -/
theorem lanczosRitzValue_le_specNorm (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q ≤ specNorm A :=
  csSup_le ⟨_, 0, (krylovSpace A b q).zero_mem, rfl⟩
    (by rintro _ ⟨y, _, rfl⟩; exact rayleighQuotient_le_specNorm A y)

/-- The largest Ritz value is nonnegative (`0 ∈ K_q` has Rayleigh quotient `0`). Helper for
`random-start-lanczos`. -/
theorem lanczosRitzValue_nonneg (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    0 ≤ lanczosRitzValue A b q := by
  have h := rayleighQuotient_le_lanczosRitzValue_of_mem A b q (krylovSpace A b q).zero_mem
  rwa [rayleighQuotient_eq_div, Matrix.mulVec_zero, dotProduct_zero, zero_div] at h

/-- **The countable form of the largest Ritz value**: by density of rational coefficients,
`lanczosRitzValue A b q = ⨆ c : Fin q → ℚ, ρ(∑ⱼ cⱼ Aʲ b)`. Helper for
`random-start-lanczos` (measurability). -/
theorem lanczosRitzValue_eq_iSup_rat (A : Matrix n n ℝ) (b : n → ℝ) (q : ℕ) :
    lanczosRitzValue A b q = ⨆ c : Fin q → ℚ,
      rayleighQuotient A (krylovCoefficientVector A b (fun j => (c j : ℝ))) := by
  have hB : BddAbove (Set.range (fun c : Fin q → ℚ =>
      rayleighQuotient A (krylovCoefficientVector A b (fun j => (c j : ℝ))))) :=
    ⟨specNorm A, by rintro _ ⟨c, rfl⟩; exact rayleighQuotient_le_specNorm A _⟩
  set θ := ⨆ c : Fin q → ℚ, rayleighQuotient A (krylovCoefficientVector A b (fun j => (c j : ℝ)))
  apply le_antisymm
  · -- every Krylov vector is a limit of rational coefficient vectors
    refine csSup_le ⟨_, 0, (krylovSpace A b q).zero_mem, rfl⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    have hθ : 0 ≤ θ := by
      have h := le_ciSup hB (0 : Fin q → ℚ)
      simp only [Pi.zero_apply, Rat.cast_zero, krylovCoefficientVector, zero_smul,
        Finset.sum_const_zero, rayleighQuotient_eq_div, Matrix.mulVec_zero, dotProduct_zero,
        zero_div] at h
      exact h
    have hRat : ∀ c : Fin q → ℚ,
        let v := krylovCoefficientVector A b (fun j => (c j : ℝ))
        v ⬝ᵥ (A *ᵥ v) ≤ θ * (v ⬝ᵥ v) := by
      intro c
      dsimp only
      set v := krylovCoefficientVector A b (fun j => (c j : ℝ))
      by_cases hv : v = 0
      · simp only [hv, Matrix.mulVec_zero, dotProduct_zero, mul_zero, le_refl]
      · have hp : 0 < v ⬝ᵥ v := lt_of_le_of_ne (dotProduct_self_nonneg _)
          (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
        have h := le_ciSup hB c
        rw [rayleighQuotient_eq_div] at h
        exact (div_le_iff₀ hp).mp h
    have hDense : DenseRange (fun c : Fin q → ℚ => fun j => (c j : ℝ)) :=
      DenseRange.piMap (fun _ => Rat.denseRange_cast)
    obtain ⟨c, rfl⟩ := (mem_krylovSpace_iff_exists_coefficients A b q y).mp hy
    have hAll : (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
        θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c) := by
      refine hDense.induction_on (p := fun c =>
        (krylovCoefficientVector A b c) ⬝ᵥ (A *ᵥ krylovCoefficientVector A b c) ≤
          θ * (krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c)) c ?_ hRat
      apply isClosed_le
      · simp only [krylovCoefficientVector, Matrix.mulVec, dotProduct, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
        fun_prop
      · simp only [krylovCoefficientVector, dotProduct, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul]
        fun_prop
    rw [rayleighQuotient_eq_div]
    by_cases hv : krylovCoefficientVector A b c = 0
    · simpa only [hv, Matrix.mulVec_zero, dotProduct_zero, div_zero] using hθ
    · have hp : 0 < krylovCoefficientVector A b c ⬝ᵥ krylovCoefficientVector A b c :=
        lt_of_le_of_ne (dotProduct_self_nonneg _)
          (Ne.symm fun h => hv (dotProduct_self_eq_zero.mp h))
      exact (div_le_iff₀ hp).mpr hAll
  · exact ciSup_le fun c =>
      rayleighQuotient_le_lanczosRitzValue_of_mem A b q (krylovCoefficientVector_mem A b _)

/-- **The largest Ritz value is measurable in the starting vector** (through the countable
form `lanczosRitzValue_eq_iSup_rat`). Helper for `random-start-lanczos`. -/
theorem measurable_lanczosRitzValue (A : Matrix n n ℝ) (q : ℕ) :
    Measurable (fun b : n → ℝ => lanczosRitzValue A b q) := by
  simp_rw [lanczosRitzValue_eq_iSup_rat]
  apply Measurable.iSup
  intro c
  simp only [rayleighQuotient_eq_div, krylovCoefficientVector, Matrix.mulVec, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

end NLAlib
