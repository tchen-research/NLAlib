import NLAlib.Gaussian.Moments.FourthMoment

/-!
# Gaussian approximate matrix multiplication

For matrices `M : a × n`, `N : b × n` and a standard Gaussian `n × t` test matrix `Ω`, the
sketched product `M (Ω Ωᵀ / t) Nᵀ` is an unbiased estimator of `M Nᵀ` with mean squared
Frobenius error
`E ‖M (Ω Ωᵀ / t) Nᵀ − M Nᵀ‖_F² = (‖M‖_F² ‖N‖_F² + ‖M Nᵀ‖_F²) / t ≤ 2 ‖M‖_F² ‖N‖_F² / t`
(`integral_frobSq_mul_gram_mul_transpose_sub`, atlas `gaussian-amm`).

The proof applies the Isserlis formula of `NLAlib.Gaussian.Moments.FourthMoment` entrywise.
Proof source: Prove2me workspace, Gaussian Random Matrices series (solution
`approx_multiplication`, namespace `GaussianMatrix.ApproxMultAux`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {n t : ℕ}

/-- The linear form `G ↦ ∑ₑ u e * G e`. -/
private def L {p m : ℕ} (u : Fin p × Fin m → ℝ) (G : Fin p → Fin m → ℝ) : ℝ :=
  ∑ e, u e * G e.1 e.2

/-- Euclidean inner product of coefficient vectors. -/
private def ip {p m : ℕ} (u v : Fin p × Fin m → ℝ) : ℝ := ∑ e, u e * v e

private lemma integrable_L2 (u v : Fin n × Fin t → ℝ) :
    Integrable (fun G => L u G * L v G) (gaussianMatrix n t) :=
  integrable_linear_mul_two_gaussianMatrix u v

private lemma integrable_L4 (u v w z : Fin n × Fin t → ℝ) :
    Integrable (fun G => L u G * L v G * L w G * L z G) (gaussianMatrix n t) :=
  integrable_linear_mul_four_gaussianMatrix u v w z

private lemma integral_L2 (u v : Fin n × Fin t → ℝ) :
    ∫ G, L u G * L v G ∂(gaussianMatrix n t) = ip u v :=
  integral_linear_mul_two_gaussianMatrix u v

private lemma integral_L4 (u v w z : Fin n × Fin t → ℝ) :
    ∫ G, L u G * L v G * L w G * L z G ∂(gaussianMatrix n t)
      = ip u v * ip w z + ip u w * ip v z + ip u z * ip v w :=
  integral_linear_mul_four_gaussianMatrix u v w z

/-- Coefficient vector of `Ω ↦ ∑ₖ f k Ω k ℓ` (a linear form in column `ℓ`). -/
private def col (f : Fin n → ℝ) (ℓ : Fin t) : Fin n × Fin t → ℝ :=
  fun e => if e.2 = ℓ then f e.1 else 0

private lemma L_col (f : Fin n → ℝ) (ℓ : Fin t) (Ω : Fin n → Fin t → ℝ) :
    L (col f ℓ) Ω = ∑ k, f k * Ω k ℓ := by
  simp [L, col, Fintype.sum_prod_type, ite_mul]

private lemma ip_col (f g : Fin n → ℝ) (ℓ ℓ' : Fin t) :
    ip (col f ℓ) (col g ℓ') = if ℓ = ℓ' then ∑ k, f k * g k else 0 := by
  by_cases h : ℓ = ℓ'
  · subst h; simp [ip, col, Fintype.sum_prod_type]
  · simp [ip, col, Fintype.sum_prod_type, h]
    intro h'; exact absurd h'.symm h

private lemma entry_sq_expand (f g : Fin n → ℝ) (r : ℝ) (Ω : Fin n → Fin t → ℝ) :
    (r * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2
      = r ^ 2 * (∑ ℓ, ∑ ℓ', L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω)
        - 2 * r * (∑ k, f k * g k) * (∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω)
        + (∑ k, f k * g k) ^ 2 := by
  have : (∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω) ^ 2
      = ∑ ℓ, ∑ ℓ', L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← this]; ring

private lemma integrable_entry_sq (f g : Fin n → ℝ) (r : ℝ) :
    Integrable (fun Ω => (r * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2)
      (gaussianMatrix n t) := by
  simp_rw [entry_sq_expand]
  refine ((Integrable.const_mul ?_ _).sub (Integrable.const_mul ?_ _)).add (integrable_const _)
  · exact integrable_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun ℓ' _ =>
      integrable_L4 _ _ _ _
  · exact integrable_finsetSum _ fun ℓ _ => integrable_L2 _ _

private lemma integral_entry_sq (ht : 1 ≤ t) (f g : Fin n → ℝ) :
    ∫ Ω, ((1 / (t : ℝ)) * ∑ ℓ, L (col f ℓ) Ω * L (col g ℓ) Ω - ∑ k, f k * g k) ^ 2
        ∂(gaussianMatrix n t)
      = ((∑ k, f k ^ 2) * (∑ k, g k ^ 2) + (∑ k, f k * g k) ^ 2) / t := by
  simp_rw [entry_sq_expand]
  have i4 := integrable_finsetSum (μ := gaussianMatrix n t) Finset.univ fun ℓ _ =>
    integrable_finsetSum Finset.univ fun ℓ' _ =>
      integrable_L4 (col f ℓ) (col g ℓ) (col f ℓ') (col g ℓ')
  have i2 := integrable_finsetSum (μ := gaussianMatrix n t) Finset.univ fun ℓ _ =>
      integrable_L2 (col f ℓ) (col g ℓ)
  rw [integral_add (by exact (i4.const_mul _).sub (i2.const_mul _)) (integrable_const _),
    integral_sub (by exact i4.const_mul _) (by exact i2.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ fun ℓ _ => integrable_finsetSum _ fun ℓ' _ =>
      integrable_L4 _ _ _ _,
    integral_finsetSum _ fun ℓ _ => integrable_L2 _ _]
  have h4 : ∀ ℓ : Fin t, ∫ Ω, ∑ ℓ' : Fin t,
      L (col f ℓ) Ω * L (col g ℓ) Ω * L (col f ℓ') Ω * L (col g ℓ') Ω ∂(gaussianMatrix n t)
      = ∑ ℓ' : Fin t, ((∑ k, f k * g k) ^ 2 + (if ℓ = ℓ' then
          (∑ k, f k * f k) * (∑ k, g k * g k) + (∑ k, f k * g k) ^ 2 else 0)) := by
    intro ℓ
    rw [integral_finsetSum _ fun ℓ' _ => integrable_L4 _ _ _ _]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    rw [integral_L4, ip_col, ip_col, ip_col, ip_col, ip_col, ip_col]
    by_cases h : ℓ = ℓ'
    · simp [h, mul_comm (g _) (f _)]; ring
    · simp [h]; ring
  simp_rw [h4, integral_L2, ip_col]
  simp [Finset.sum_add_distrib, Finset.sum_ite_eq]
  have : (t : ℝ) ≠ 0 := by positivity
  field_simp
  simp only [sq]
  ring

private lemma entry_sub_eq {a b : ℕ} (M : Matrix (Fin a) (Fin n) ℝ)
    (N : Matrix (Fin b) (Fin n) ℝ) (Ω : Fin n → Fin t → ℝ) (i : Fin a) (j : Fin b) :
    (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ) i j
      = (1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω - ∑ k, M i k * N j k := by
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_mul, L_col]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ k', ∑ ℓ, ∑ k, M i k * (1 / (t : ℝ) * (Ω k ℓ * Ω k' ℓ)) * N j k' :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ ℓ, ∑ k', ∑ k, M i k * (1 / (t : ℝ) * (Ω k ℓ * Ω k' ℓ)) * N j k' := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ring

/-- **Gaussian approximate matrix multiplication.** For `M : a × n`, `N : b × n` and a standard
Gaussian `n × t` matrix `Ω` (`t ≥ 1`), the sketched product `M (Ω Ωᵀ / t) Nᵀ` has mean squared
error `E ‖M (Ω Ωᵀ / t) Nᵀ − M Nᵀ‖_F² = (‖M‖_F² ‖N‖_F² + ‖M Nᵀ‖_F²) / t`, and this is at most
`(2/t) ‖M‖_F² ‖N‖_F²`.

Drineas–Kannan–Mahoney 2006 / Sarlós 2006 (approximate matrix multiplication); Gaussian case
via the Isserlis formula, e.g. Martinsson–Tropp 2020, §6.3 / Woodruff 2014, Lemma 2.2.
Atlas: `gaussian-amm`. Ported from Prove2me solution `GaussianMatrix.approx_multiplication`.
atlas: gaussian-amm -/
theorem integral_frobSq_mul_gram_mul_transpose_sub {a b n t : ℕ} (ht : 1 ≤ t)
    (M : Matrix (Fin a) (Fin n) ℝ) (N : Matrix (Fin b) (Fin n) ℝ) :
    ∫ Ω, frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        ∂(gaussianMatrix n t)
      = (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ∧
    (frobSq M * frobSq N + frobSq (M * Nᵀ)) / t ≤ 2 / t * (frobSq M * frobSq N) := by
  have hMN : frobSq (M * Nᵀ) = ∑ i, ∑ j, (∑ k, M i k * N j k) ^ 2 := by
    simp [frobSq_eq_sum_sq, Matrix.mul_apply]
  have hMN' : frobSq M * frobSq N = ∑ i, ∑ j, (∑ k, M i k ^ 2) * (∑ k, N j k ^ 2) := by
    simp only [frobSq_eq_sum_sq, Finset.sum_mul_sum]
  constructor
  · have hX : ∀ Ω : Fin n → Fin t → ℝ,
        frobSq (M * ((1 / (t : ℝ)) • (Matrix.of Ω * (Matrix.of Ω)ᵀ)) * Nᵀ - M * Nᵀ)
        = ∑ i, ∑ j, ((1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω
            - ∑ k, M i k * N j k) ^ 2 := by
      intro Ω; simp only [frobSq_eq_sum_sq, entry_sub_eq]
    simp_rw [hX]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_entry_sq (M i) (N j) _]
    have hij : ∀ i, ∫ Ω, ∑ j, ((1 / (t : ℝ)) * ∑ ℓ, L (col (M i) ℓ) Ω * L (col (N j) ℓ) Ω
            - ∑ k, M i k * N j k) ^ 2 ∂(gaussianMatrix n t)
        = ∑ j, ((∑ k, M i k ^ 2) * (∑ k, N j k ^ 2) + (∑ k, M i k * N j k) ^ 2) / t := by
      intro i
      rw [integral_finsetSum _ fun j _ => integrable_entry_sq (M i) (N j) _]
      exact Finset.sum_congr rfl fun j _ => integral_entry_sq ht (M i) (N j)
    simp_rw [hij, hMN, hMN', ← Finset.sum_div, ← Finset.sum_add_distrib]
  · have hle : frobSq (M * Nᵀ) ≤ frobSq M * frobSq N := by
      rw [hMN, hMN']
      gcongr with i _ j _
      exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [show 2 / (t : ℝ) * (frobSq M * frobSq N)
      = (frobSq M * frobSq N + frobSq M * frobSq N) / t by ring]
    gcongr

end NLAlib
