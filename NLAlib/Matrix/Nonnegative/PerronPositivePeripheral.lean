import NLAlib.Matrix.Nonnegative.PerronIrreducible
import NLAlib.ForMathlib.Analysis.ComplexWeightedAverage
import NLAlib.Matrix.Spectral.MatrixPowerReal

/-! # Peripheral eigenvector rigidity for positive matrices

A row of a positive matrix becomes a strictly positive probability vector
after Perron diagonal scaling. Equality in its complex norm bound forces all
scaled coordinates to coincide. Source: Horn–Johnson, Chapter 8.
-/
noncomputable section
open Matrix Finset
open scoped Matrix
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- Every peripheral eigenvector of a strictly positive matrix lies on its
positive Perron line. The proof uses the exact finite complex variance identity.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem peripheral_eigenvector_eq_smul_of_pos {B : Matrix ι ι ℝ}
    (hB : ∀ i j, 0 < B i j) {p : ι → ℝ} {r : ℝ}
    (hp : ∀ i, 0 < p i) (hr : 0 < r) (hBp : B *ᵥ p = r • p)
    {z : ι → ℂ} {μ : ℂ} (hBz : B.map Complex.ofReal *ᵥ z = μ • z) (hμ : ‖μ‖ = r) :
    ∃ c : ℂ, z = c • (fun i => (p i : ℂ)) := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖ / p j)
    Finset.univ_nonempty
  let t : ℝ := ‖z i‖ / p i
  have ht : 0 ≤ t := div_nonneg (norm_nonneg _) (hp i).le
  let w : ι → ℝ := fun j => B i j * p j / (r * p i)
  let u : ι → ℂ := fun j => z j / (p j : ℂ)
  have hden : 0 < r * p i := mul_pos hr (hp i)
  have hw (j : ι) : 0 < w j := div_pos (mul_pos (hB i j) (hp j)) hden
  have hws : ∑ j, w j = 1 := by
    simp only [w, ← Finset.sum_div]
    change (B *ᵥ p) i / (r * p i) = 1
    rw [hBp]
    exact div_self hden.ne'
  have hu (j : ι) : ‖u j‖ ≤ t := by
    simpa only [u, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp j)]
      using hi j (mem_univ j)
  have havg : (∑ j, (w j : ℂ) * u j) = μ * z i / ((r * p i : ℝ) : ℂ) := by
    calc
      _ = (∑ j, (B i j : ℂ) * z j) / ((r * p i : ℝ) : ℂ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [w, u]
        push_cast
        field_simp [(hp j).ne', hr.ne', (hp i).ne']
      _ = _ := by
        have h := congrFun hBz i
        simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] using
          congrArg (· / ((r * p i : ℝ) : ℂ)) h
  have havgnorm : ‖∑ j, (w j : ℂ) * u j‖ = t := by
    rw [havg, norm_div, norm_mul, hμ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
    dsimp [t]
    field_simp [hr.ne', (hp i).ne']
  have hrigid := Complex.eq_average_of_norm_average_eq_bound w u hw hws ht hu havgnorm
  refine ⟨∑ j, (w j : ℂ) * u j, funext fun j => ?_⟩
  have hpC : (p j : ℂ) ≠ 0 := by exact_mod_cast (hp j).ne'
  exact (div_eq_iff hpC).mp (hrigid j)

/-- A positive power forces the Perron root to be the only peripheral eigenvalue.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsPrimitive.peripheral_eigenvalue_eq_perron {A : Matrix ι ι ℝ}
    (hA : A.IsPrimitive) (hAne : A ≠ 0) {μ : ℂ}
    (hμ : μ ∈ spectrum ℂ (A.map Complex.ofReal))
    (hμnorm : ‖μ‖ = (spectralRadius ℂ (A.map Complex.ofReal)).toReal) :
    μ = ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ) := by
  obtain ⟨p, _, hr, hp, _, _, _, hAp, _⟩ := hA.isIrreducible.exists_positive_perron_pair hAne
  obtain ⟨z, hz, hAz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
  obtain ⟨k, _, hk⟩ := hA.exists_pos_pow
  have hpPower := pow_mulVec_eq_pow_smul_of_mulVec_eq_smul hAp k
  have hzPower : (A ^ k).map Complex.ofReal *ᵥ z = μ ^ k • z := by
    rw [NLAlib.map_ofReal_matrix_pow]
    exact pow_mulVec_eq_pow_smul_of_mulVec_eq_smul hAz k
  obtain ⟨c, hc⟩ := peripheral_eigenvector_eq_smul_of_pos hk hp (pow_pos hr k)
    hpPower hzPower (by simp only [norm_pow, hμnorm])
  have hpC : A.map Complex.ofReal *ᵥ (fun i => (p i : ℂ)) =
      ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ) • (fun i => (p i : ℂ)) := by
    funext i
    have h := congrArg Complex.ofReal (congrFun hAp i)
    simpa only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  have hzr : A.map Complex.ofReal *ᵥ z =
      ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ) • z := by
    rw [hc, Matrix.mulVec_smul, hpC, smul_smul, smul_smul, mul_comm c]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz
  have hEq := congrFun (hAz.symm.trans hzr) j
  exact mul_right_cancel₀ hj hEq

end Matrix
