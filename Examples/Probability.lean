import NLAlib.Probability.ChiSquare.DirectionalSquaredNorm
import NLAlib.Probability.Rademacher.RademacherSymmetry
import NLAlib.RandomMatrix.Gaussian.Comparison.IndependentEntryExtremum

/-! A continuous Gaussian sample space uses the native directional sub-Gaussian tail
theorem directly. No finite-support model or discrete sample-space instance is needed. -/

open MeasureTheory ProbabilityTheory NLAlib
open scoped NNReal

-- The squared standard Gaussian has the one-dimensional Laurent–Massart upper tail.
example {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 1).real {g : ℝ | 1 + 2 * Real.sqrt x + 2 * x ≤ g ^ 2} ≤
      Real.exp (-x) := by
  have hmgf : ∀ u : Fin 1 → ℝ,
      HasSubgaussianMGF (fun g : ℝ => (fun _ : Fin 1 => g) ⬝ᵥ u)
        (‖WithLp.toLp 2 u‖₊ ^ 2) (gaussianReal 0 1) := by
    intro u
    have hvar : (⟨(u 0) ^ 2, sq_nonneg _⟩ : ℝ≥0) = ‖WithLp.toLp 2 u‖₊ ^ 2 := by
      apply NNReal.eq
      change (u 0) ^ 2 = ((‖WithLp.toLp 2 u‖₊ ^ 2 : ℝ≥0) : ℝ)
      rw [NNReal.coe_pow, coe_nnnorm, norm_toLp_sq_eq_dotProduct_self]
      simp [dotProduct, pow_two]
    have hscaled := (hasSubgaussianMGF_id_gaussianReal 1).const_mul (u 0)
    have hproxy : NNReal.mk ((u 0) ^ 2) (sq_nonneg _) * (1 : NNReal) =
        ‖WithLp.toLp 2 u‖₊ ^ 2 := by
      exact (_root_.mul_one _).trans hvar
    convert hscaled using 1
    · ext g
      simp [dotProduct, mul_comm]
    · exact hproxy.symm
  simpa only [norm_toLp_sq_eq_dotProduct_self, dotProduct, Fin.sum_univ_one,
    Nat.cast_one, one_mul, ← sq] using
    measureReal_sq_norm_ge_add_two_sqrt_mul_add_le
      (gaussianReal 0 1) (fun g : ℝ => fun _ : Fin 1 => g) hmgf hx

-- Every normalized Gram moment of a 2 × 3 independent sign matrix is bounded
-- by that of a 2 × 3 iid Gaussian matrix, with no enlargement depending on p.
open scoped Matrix in
example (p : ℕ) (hp : 0 < p) :
    (∫ r : Fin 2 × Fin 3 → ℝ,
      normalizedTrace (((Matrix.of (fun i j => r (i, j))) *
        (Matrix.of (fun i j => r (i, j)))ᴴ) ^ p)
      ∂rademacherVector (Fin 2 × Fin 3)) ≤
    (∫ G : Matrix (Fin 2) (Fin 3) ℝ,
      normalizedTrace ((G * Gᴴ) ^ p) ∂gaussianMatrix (Fin 2) (Fin 3)) := by
  have hsym (e : Fin 2 × Fin 3) :
      IdentDistrib (fun r : Fin 2 × Fin 3 → ℝ => r e) (fun r => -r e)
        (rademacherVector (Fin 2 × Fin 3)) (rademacherVector (Fin 2 × Fin 3)) :=
    (hasLaw_eval_rademacherVector e).identDistrib
      (measurePreserving_neg_rademacherMeasure.fun_comp_hasLaw
        (hasLaw_eval_rademacherVector e))
  have hmom (e : Fin 2 × Fin 3) (q : ℕ) (_hq : 0 < q) :
      Integrable (fun r : Fin 2 × Fin 3 → ℝ => r e ^ (2 * q))
        (rademacherVector (Fin 2 × Fin 3)) ∧
      (∫ r : Fin 2 × Fin 3 → ℝ, r e ^ (2 * q)
        ∂rademacherVector (Fin 2 × Fin 3)) ≤ gaussianEvenMoment q := by
    have hpow : (fun r : Fin 2 × Fin 3 → ℝ => r e ^ (2 * q)) =ᵐ[
        rademacherVector (Fin 2 × Fin 3)] fun _ => 1 := by
      filter_upwards [ae_forall_sq_eq_one_rademacherVector] with r hr
      rw [pow_mul, hr e, one_pow]
    refine ⟨(integrable_const (1 : ℝ)).congr hpow.symm, ?_⟩
    rw [integral_congr_ae hpow]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact (show (1 : ℝ) ≤ (q.factorial : ℝ) by
      exact_mod_cast Nat.factorial_pos q).trans (factorial_le_gaussianEvenMoment q)
  have h := integral_normalizedTrace_gram_pow_le_integral_gaussianMatrix
    (X := fun i j (r : Fin 2 × Fin 3 → ℝ) => r (i, j))
    (iIndepFun_eval_rademacherVector (Fin 2 × Fin 3)) hsym hmom
    (fun (_ : Fin 2) (_ : Fin 3) => (1 : ℝ))
    (by intro e; norm_num) (by simp) p hp
  have hrows : Nat.ceil ((Finset.univ : Finset (Fin 3)).sup' Finset.univ_nonempty
      (fun _ => ∑ _ : Fin 2, (1 : ℝ) ^ 2)) = 2 := by norm_num
  have hcols : Nat.ceil ((Finset.univ : Finset (Fin 2)).sup' Finset.univ_nonempty
      (fun _ => ∑ _ : Fin 3, (1 : ℝ) ^ 2)) = 3 := by norm_num
  rw [hrows, hcols] at h
  simpa using h
