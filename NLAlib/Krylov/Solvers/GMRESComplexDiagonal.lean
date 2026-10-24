/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Krylov.Solvers.GMRES
import NLAlib.Matrix.Functions.PolynomialSimilarity

/-! # Real GMRES bounds from complex spectral data

Complexifying the actual real residual polynomial preserves its spectral
norm. The polynomial-similarity bound therefore applies directly to the
backend's real GMRES iterates, and normality removes the condition factor.
Source: Saad (2003), Proposition 6.32; source polynomial bound ported from
NLA-lib/NLAlib commit 6a845a2ec27f37c1a98118c107a06a13ce45273d.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ} {c x₀ x : n → ℝ} {q : ℕ}

private theorem residual_norm_le_of_specNorm_aeval_le
    (hx : IsGMRESIterate A c x₀ q x) {p : ℝ[X]} (hp : p.degree ≤ q)
    (hp0 : p.eval 0 = 1) {M : ℝ} (hbound : specNorm (aeval A p) ≤ M) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤ M * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  have hM0 : 0 ≤ M := (specNorm_nonneg _).trans hbound
  have hv : 0 ≤ (c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀) :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hprobe : (aeval A p *ᵥ (c - A *ᵥ x₀)) ⬝ᵥ (aeval A p *ᵥ (c - A *ᵥ x₀)) ≤
      specNorm (aeval A p) ^ 2 * ((c - A *ᵥ x₀) ⬝ᵥ (c - A *ᵥ x₀)) := by
    simpa only [dotProduct, sq] using sum_sq_mulVec_le_specNorm_sq (aeval A p) (c - A *ᵥ x₀)
  have hs := ((hx.le_aeval hp hp0).trans hprobe).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (specNorm_nonneg _) hbound 2) hv)
  have hnorm : ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ^ 2 ≤
      (M * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖) ^ 2 := by
    simpa only [mul_pow, norm_toLp_sq_eq_dotProduct_self] using hs
  exact le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hM0 (norm_nonneg _)) hnorm

/-- A real GMRES iterate satisfies the full complex-diagonalization
residual bound for every real residual polynomial. The real matrix and
its residual remain the original backend objects; the eigenvector matrix
and eigenvalues may be complex. Empty dimensions are included.
Source: Saad (2003), Proposition 6.32; Trefethen--Bau (1997), Theorem 35.2.
atlas: gmres-diagonalizable (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_complex_diagonalization
    (hx : IsGMRESIterate A c x₀ q x) {V : Matrix n n ℂ} {d : n → ℂ}
    (hV : IsUnit V)
    (hA : A.map (algebraMap ℝ ℂ) = V * Matrix.diagonal d * V⁻¹)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ i, ‖p.eval₂ (algebraMap ℝ ℂ) (d i)‖ ≤ M) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤
      (specNorm V * specNorm V⁻¹ * M) * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  apply residual_norm_le_of_specNorm_aeval_le hx hp hp0
  rw [← specNorm_map_ofReal (𝕜 := ℂ) (aeval A p), map_ofReal_aeval]
  exact specNorm_aeval_le_of_eq_mul_diagonal_mul
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hV)) hA p hM

/-- A real normal matrix has the sharp condition-factor-one GMRES
bound, using its actual complex spectrum. This includes real normal
matrices with nonreal eigenvalues, as well as empty dimensions.
Source: Saad (2003), Proposition 6.32, normal specialization.
atlas: gmres-diagonalizable (partial) -/
theorem IsGMRESIterate.norm_sub_mulVec_le_of_normal
    (hx : IsGMRESIterate A c x₀ q x) (hA : A * Aᵀ = Aᵀ * A)
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp0 : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)),
      ‖p.eval₂ (algebraMap ℝ ℂ) z‖ ≤ M) :
    ‖WithLp.toLp 2 (c - A *ᵥ x)‖ ≤ M * ‖WithLp.toLp 2 (c - A *ᵥ x₀)‖ := by
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Subsingleton.elim (c - A *ᵥ x) 0, Subsingleton.elim (c - A *ᵥ x₀) 0,
      WithLp.toLp_zero, norm_zero, mul_zero, le_refl]
  · have ht : (A.map (algebraMap ℝ ℂ))ᴴ = Aᵀ.map (algebraMap ℝ ℂ) := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    have hAc : A.map (algebraMap ℝ ℂ) * (A.map (algebraMap ℝ ℂ))ᴴ =
        (A.map (algebraMap ℝ ℂ))ᴴ * A.map (algebraMap ℝ ℂ) := by
      rw [ht]
      change (algebraMap ℝ ℂ).mapMatrix A * (algebraMap ℝ ℂ).mapMatrix Aᵀ =
        (algebraMap ℝ ℂ).mapMatrix Aᵀ * (algebraMap ℝ ℂ).mapMatrix A
      rw [← map_mul, ← map_mul, hA]
    obtain ⟨U, d, hd⟩ := exists_unitary_diagonalization_of_normal hAc
    have hs : spectrum ℂ (A.map (algebraMap ℝ ℂ)) = Set.range d := by
      rw [hd]
      simpa only [← Matrix.star_eq_conjTranspose, Unitary.coe_star, spectrum_diagonal]
        using Unitary.spectrum_star_right_conjugate (R := ℂ) (a := Matrix.diagonal d) (U := U)
    obtain ⟨i⟩ := hn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (d i) (hs.symm ▸ ⟨i, rfl⟩))
    apply residual_norm_le_of_specNorm_aeval_le hx hp hp0
    rw [← specNorm_map_ofReal (𝕜 := ℂ) (aeval A p), map_ofReal_aeval]
    exact specNorm_aeval_le_of_normal hAc p hM0 hM

end NLAlib
