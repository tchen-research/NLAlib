import NLAlib.Krylov.Solvers.GMRES
import NLAlib.Matrix.Functions.NearestPSD
import NLAlib.Matrix.Spectral.HermitianMinimum

/-! # Positive-real GMRES and restarted cycles

The smallest eigenvalue of the positive definite symmetric part yields
a contractive Richardson polynomial. GMRES minimizes over all residual
polynomials, and successive restarted cycles multiply the same rate.
Source: Eisenstat--Elman--Schultz (1983), Theorem 3.3;
Saad (2003), §6.11.4. Atlas: `gmres-elman`.
-/

noncomputable section

open Matrix Polynomial
open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

omit [DecidableEq n] in
private theorem dotProduct_hermitianPart_mulVec (r : n → ℝ) :
    r ⬝ᵥ (matrixHermitianPart A *ᵥ r) = r ⬝ᵥ (A *ᵥ r) := by
  have ht : r ⬝ᵥ (Aᵀ *ᵥ r) = r ⬝ᵥ (A *ᵥ r) := by
    calc
      _ = (Aᵀ *ᵥ r) ⬝ᵥ r := dotProduct_comm _ _
      _ = _ := by rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec]
  simp only [matrixHermitianPart, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.conjTranspose_eq_transpose_of_trivial, dotProduct_smul,
    dotProduct_add, smul_eq_mul, ht]
  ring

private theorem positive_real_parameters [Nonempty n]
    (hM : (matrixHermitianPart A).PosDef) :
    0 < lambdaMin (matrixHermitianPart A) ∧
      lambdaMin (matrixHermitianPart A) ≤ specNorm A ∧
      ∀ r : n → ℝ, lambdaMin (matrixHermitianPart A) * (r ⬝ᵥ r) ≤
        r ⬝ᵥ (A *ᵥ r) := by
  have hco (r : n → ℝ) :
      lambdaMin (matrixHermitianPart A) * (r ⬝ᵥ r) ≤ r ⬝ᵥ (A *ᵥ r) := by
    have hp := hM.isHermitian.posSemidef_sub_lambdaMin_smul_one
    have hr := hp.quadForm_nonneg r
    simp only [quadForm, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      RCLike.ofReal_real_eq_id, id_eq] at hr
    rw [dotProduct_hermitianPart_mulVec] at hr
    linarith
  obtain ⟨v, hv, he⟩ := hM.isHermitian.exists_unit_lambdaMin_eigenvector
  have hvv : v ⬝ᵥ v = 1 := by
    rw [← norm_toLp_sq_eq_dotProduct_self, hv, one_pow]
  have hv0 : v ≠ 0 := by
    intro hzero
    simp only [hzero, WithLp.toLp_zero, norm_zero] at hv
    norm_num at hv
  have hα : 0 < lambdaMin (matrixHermitianPart A) := by
    have h := hM.dotProduct_mulVec_pos hv0
    simpa only [star_trivial, he, dotProduct_smul, smul_eq_mul, hvv, mul_one,
      RCLike.ofReal_real_eq_id, id_eq] using h
  refine ⟨hα, ?_, hco⟩
  have hl := hco v
  have hu := (le_abs_self (v ⬝ᵥ (A *ᵥ v))).trans (abs_dotProduct_mulVec_le_specNorm A v)
  simpa only [hvv, mul_one] using hl.trans hu

private theorem dotProduct_sub_smul_mulVec_self_le {α ω : ℝ}
    (hω : 0 ≤ ω) (hco : ∀ r : n → ℝ, α * (r ⬝ᵥ r) ≤ r ⬝ᵥ (A *ᵥ r))
    (r : n → ℝ) :
    (r - ω • (A *ᵥ r)) ⬝ᵥ (r - ω • (A *ᵥ r)) ≤
      (1 - 2 * ω * α + ω ^ 2 * specNorm A ^ 2) * (r ⬝ᵥ r) := by
  have hb : (A *ᵥ r) ⬝ᵥ (A *ᵥ r) ≤ specNorm A ^ 2 * (r ⬝ᵥ r) := by
    simpa only [dotProduct, sq] using sum_sq_mulVec_le_specNorm_sq A r
  have hl := mul_le_mul_of_nonneg_left (hco r) hω
  have hu := mul_le_mul_of_nonneg_left hb (sq_nonneg ω)
  have he : (r - ω • (A *ᵥ r)) ⬝ᵥ (r - ω • (A *ᵥ r)) =
      r ⬝ᵥ r - 2 * ω * (r ⬝ᵥ (A *ᵥ r)) +
        ω ^ 2 * ((A *ᵥ r) ⬝ᵥ (A *ᵥ r)) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, dotProduct_comm (A *ᵥ r) r]
    ring
  rw [he]
  nlinarith

private theorem norm_residual_le_sqrt_pow {α : ℝ} (hα : 0 < α)
    (hαβ : α ≤ specNorm A)
    (hco : ∀ r : n → ℝ, α * (r ⬝ᵥ r) ≤ r ⬝ᵥ (A *ᵥ r))
    {c x₀ x : n → ℝ} {k : ℕ} (hx : IsGMRESIterate A c x₀ k x) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      Real.sqrt (1 - α ^ 2 / specNorm A ^ 2) ^ k * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have hβ : 0 < specNorm A := hα.trans_le hαβ
  let ω := α / specNorm A ^ 2
  let δ := 1 - α ^ 2 / specNorm A ^ 2
  let B : Matrix n n ℝ := 1 - ω • A
  have hω : 0 ≤ ω := div_nonneg hα.le (sq_nonneg _)
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hβ)).mpr
      (pow_le_pow_left₀ hα.le hαβ 2))
  have hcoeff : 1 - 2 * ω * α + ω ^ 2 * specNorm A ^ 2 = δ := by
    dsimp [ω, δ]
    field_simp
    ring
  have hB (r : n → ℝ) :
      (B *ᵥ r) ⬝ᵥ (B *ᵥ r) ≤ δ * (r ⬝ᵥ r) := by
    have h := dotProduct_sub_smul_mulVec_self_le hω hco r
    simpa only [B, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hcoeff] using h
  have hpow (j : ℕ) (r : n → ℝ) :
      ((B ^ j) *ᵥ r) ⬝ᵥ ((B ^ j) *ᵥ r) ≤ δ ^ j * (r ⬝ᵥ r) := by
    induction j with
    | zero => simp
    | succ j ih =>
      simp only [pow_succ', ← Matrix.mulVec_mulVec]
      calc
        (B *ᵥ ((B ^ j) *ᵥ r)) ⬝ᵥ (B *ᵥ ((B ^ j) *ᵥ r)) ≤
            δ * (((B ^ j) *ᵥ r) ⬝ᵥ ((B ^ j) *ᵥ r)) := hB _
        _ ≤ δ * (δ ^ j * (r ⬝ᵥ r)) := mul_le_mul_of_nonneg_left ih hδ
        _ = δ * δ ^ j * (r ⬝ᵥ r) := by ring
  let p : ℝ[X] := (1 - C ω * X) ^ k
  have hp : p.degree ≤ k := by
    apply degree_le_of_natDegree_le
    dsimp [p]
    compute_degree
  have hp0 : p.eval 0 = 1 := by simp [p]
  have heval : aeval A p = B ^ k := by
    simp only [p, B, map_pow, map_sub, map_one, map_mul, aeval_C, aeval_X,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
  have hs : (c - A *ᵥ x) ⬝ᵥ (c - A *ᵥ x) ≤
      δ ^ k * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
    refine (hx.le_aeval hp hp0).trans ?_
    rw [heval]
    exact hpow _ _
  have hroot : (Real.sqrt δ ^ k) ^ 2 = δ ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hδ]
  have hnorm : ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ^ 2 ≤
      (Real.sqrt δ ^ k * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖) ^ 2 := by
    simpa only [mul_pow, hroot, norm_toLp_sq_eq_dotProduct_self] using hs
  exact le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (norm_nonneg _)) hnorm

/-- Positive definiteness of the symmetric part gives the positive-real
GMRES estimate, with the square-root factor raised to the step count.
Source: Eisenstat--Elman--Schultz (1983), Theorem 3.3; Saad (2003),
§6.11.4. Empty dimensions and step zero are included.
atlas: gmres-elman (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_sqrt_pow_of_posDef_hermitianPart
    {c x₀ x : n → ℝ} {k : ℕ} (hx : IsGMRESIterate A c x₀ k x)
    (hM : (matrixHermitianPart A).PosDef) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      Real.sqrt (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ k *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Subsingleton.elim (c - A *ᵥ x) 0,
      Subsingleton.elim (c - A *ᵥ x₀) 0, WithLp.toLp_zero, norm_zero, mul_zero, le_refl]
  · have := hn
    obtain ⟨hα, hαβ, hco⟩ := positive_real_parameters hM
    exact norm_residual_le_sqrt_pow hα hαβ hco hx

private theorem sqrt_pow_eq_rpow_half {δ : ℝ} (hδ : 0 ≤ δ) (k : ℕ) :
    Real.sqrt δ ^ k = δ ^ ((k : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hδ]
  congr 1
  ring

/-- The positive-real GMRES estimate with the exact half-step exponent
of the standard statement. Source: Eisenstat--Elman--Schultz (1983),
Theorem 3.3; Saad (2003), §6.11.4.
atlas: gmres-elman (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_posDef_hermitianPart
    {c x₀ x : n → ℝ} {k : ℕ} (hx : IsGMRESIterate A c x₀ k x)
    (hM : (matrixHermitianPart A).PosDef) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ ((k : ℝ) / 2) *
        ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Subsingleton.elim (c - A *ᵥ x) 0,
      Subsingleton.elim (c - A *ᵥ x₀) 0, WithLp.toLp_zero, norm_zero, mul_zero, le_refl]
  · have := hn
    obtain ⟨hα, hαβ, -⟩ := positive_real_parameters hM
    have hβ := hα.trans_le hαβ
    have hδ : 0 ≤ 1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2 :=
      sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hβ)).mpr
        (pow_le_pow_left₀ hα.le hαβ 2))
    simpa only [sqrt_pow_eq_rpow_half hδ] using
      hx.norm_sub_mulVec_le_sqrt_pow_of_posDef_hermitianPart hM

/-- Each realized restarted GMRES cycle contributes its full step
count to the positive-real contraction exponent. The cycle hypotheses
refer to the native GMRES minimizer at every restart, rather than to an
assumed norm contraction. Source: Saad (2003), §6.11.4.
atlas: gmres-elman (partial) -/
theorem norm_sub_mulVec_le_sqrt_pow_of_restarted_gmres
    {c : n → ℝ} (hM : (matrixHermitianPart A).PosDef)
    (xs : ℕ → n → ℝ) (m : ℕ)
    (hcycle : ∀ j, IsGMRESIterate A c (xs j) m (xs (j + 1))) (j : ℕ) :
    ‖WithLp.toLp 2 (c - A *ᵥ xs j)‖ ≤
      Real.sqrt (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ (j * m) *
        ‖WithLp.toLp 2 (c - A *ᵥ xs 0)‖ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have he : m + j * m = (j + 1) * m := by ring
    calc
      ‖WithLp.toLp 2 (c - A *ᵥ xs (j + 1))‖ ≤
          Real.sqrt (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ m *
            ‖WithLp.toLp 2 (c - A *ᵥ xs j)‖ :=
        (hcycle j).norm_sub_mulVec_le_sqrt_pow_of_posDef_hermitianPart hM
      _ ≤ Real.sqrt (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ m *
          (Real.sqrt (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ (j * m) *
            ‖WithLp.toLp 2 (c - A *ᵥ xs 0)‖) :=
        mul_le_mul_of_nonneg_left ih (pow_nonneg (Real.sqrt_nonneg _) _)
      _ = _ := by rw [← mul_assoc, ← pow_add, he]

/-- Restarted GMRES with cycle length `m` satisfies the positive-real
bound after `j*m` total steps. This includes zero cycles and cycle
length zero. Source: Saad (2003), §6.11.4.
atlas: gmres-elman (partial) -/
theorem norm_sub_mulVec_le_of_restarted_gmres
    {c : n → ℝ} (hM : (matrixHermitianPart A).PosDef)
    (xs : ℕ → n → ℝ) (m : ℕ)
    (hcycle : ∀ j, IsGMRESIterate A c (xs j) m (xs (j + 1))) (j : ℕ) :
    ‖WithLp.toLp 2 (c - A *ᵥ xs j)‖ ≤
      (1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2) ^ (((j * m : ℕ) : ℝ) / 2) *
        ‖WithLp.toLp 2 (c - A *ᵥ xs 0)‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Subsingleton.elim (c - A *ᵥ xs j) 0,
      Subsingleton.elim (c - A *ᵥ xs 0) 0, WithLp.toLp_zero, norm_zero, mul_zero, le_refl]
  · have := hn
    obtain ⟨hα, hαβ, -⟩ := positive_real_parameters hM
    have hβ := hα.trans_le hαβ
    have hδ : 0 ≤ 1 - lambdaMin (matrixHermitianPart A) ^ 2 / specNorm A ^ 2 :=
      sub_nonneg.mpr ((div_le_one (sq_pos_of_pos hβ)).mpr
        (pow_le_pow_left₀ hα.le hαβ 2))
    simpa only [sqrt_pow_eq_rpow_half hδ] using
      norm_sub_mulVec_le_sqrt_pow_of_restarted_gmres hM xs m hcycle j

end NLAlib
