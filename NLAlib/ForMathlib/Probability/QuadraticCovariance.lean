import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.Moments.Covariance
import Mathlib.Algebra.BigOperators.Pi

/-!
# Quadratic expectations from full covariance

Every real continuous bilinear quadratic form on a finite coordinate space
contracts with its full second-moment matrix. Equal means and covariance
therefore identify the expectation of every quadratic form.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLAlib
variable {κ Ω Ω' : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- A bilinear quadratic form is the contraction of all coordinate products
with its values on coordinate basis pairs. -/
theorem bilin_quadratic_eq_sum_coordinates
    (B : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ) (x : κ → ℝ) :
    B x x = ∑ i, ∑ j, (x i * x j) * B (Pi.single i 1) (Pi.single j 1) := by
  have hx : B x x = ∑ i, x i • B (Pi.single i 1) x := by
    simpa only [map_sum, map_smul, sum_apply, smul_apply] using
      congrArg (fun v : κ → ℝ => B v x) (pi_eq_sum_univ' x)
  have hsecond : ∀ i, B (Pi.single i 1) x =
      ∑ j, x j • B (Pi.single i 1) (Pi.single j 1) := by
    intro i
    conv_lhs => rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul]
  rw [hx]
  simp_rw [hsecond, Finset.smul_sum, smul_smul, smul_eq_mul]

omit [IsProbabilityMeasure μ] in
/-- Square integrability suffices for integrability of every actual continuous
bilinear quadratic form. -/
theorem integrable_bilin_quadratic_of_memLp_two
    (B : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ)
    {X : Ω → κ → ℝ} (hX : MemLp X 2 μ) :
    Integrable (fun ω => B (X ω) (X ω)) μ := by
  have hi (i j : κ) : Integrable
      (fun ω => (X ω i * X ω j) * B (Pi.single i 1) (Pi.single j 1)) μ :=
    ((hX.eval i).integrable_mul (hX.eval j)).mul_const _
  simpa only [bilin_quadratic_eq_sum_coordinates] using
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ => hi i j))

omit [IsProbabilityMeasure μ] in
/-- The quadratic expectation is the exact contraction with every entry of
the second-moment matrix; diagonal variances alone do not suffice. -/
theorem integral_bilin_quadratic_eq_sum_second_moments
    (B : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ)
    {X : Ω → κ → ℝ} (hX : MemLp X 2 μ) :
    (∫ ω, B (X ω) (X ω) ∂μ) =
      ∑ i, ∑ j, (∫ ω, X ω i * X ω j ∂μ) *
        B (Pi.single i 1) (Pi.single j 1) := by
  have hi (i j : κ) : Integrable
      (fun ω => (X ω i * X ω j) * B (Pi.single i 1) (Pi.single j 1)) μ :=
    ((hX.eval i).integrable_mul (hX.eval j)).mul_const _
  simp_rw [bilin_quadratic_eq_sum_coordinates]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_mul_const _ _

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] in
/-- Matching every real coordinate second moment preserves the expectation
of every continuous bilinear quadratic form. -/
theorem integral_bilin_quadratic_eq_of_second_moments_eq
    (B : (κ → ℝ) →L[ℝ] (κ → ℝ) →L[ℝ] ℝ)
    {X : Ω → κ → ℝ} {Z : Ω' → κ → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 ν)
    (hmatch : ∀ i j, (∫ ω, X ω i * X ω j ∂μ) = ∫ ω, Z ω i * Z ω j ∂ν) :
    (∫ ω, B (X ω) (X ω) ∂μ) = ∫ ω, B (Z ω) (Z ω) ∂ν := by
  simp_rw [integral_bilin_quadratic_eq_sum_second_moments B hX,
    integral_bilin_quadratic_eq_sum_second_moments B hZ, hmatch]

omit [DecidableEq κ] in
/-- Equal coordinate means and full covariances give equal second moments.
Centeredness is sufficient but not necessary. -/
theorem integral_mul_coordinates_eq_of_mean_covariance_eq
    {X : Ω → κ → ℝ} {Z : Ω' → κ → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 ν)
    (hmean : ∀ i, (∫ ω, X ω i ∂μ) = ∫ ω, Z ω i ∂ν)
    (hcov : ∀ i j, cov[fun ω => X ω i, fun ω => X ω j; μ] =
      cov[fun ω => Z ω i, fun ω => Z ω j; ν]) (i j : κ) :
    (∫ ω, X ω i * X ω j ∂μ) = ∫ ω, Z ω i * Z ω j ∂ν := by
  have hc := hcov i j
  rw [covariance_eq_sub (hX.eval i) (hX.eval j),
    covariance_eq_sub (hZ.eval i) (hZ.eval j),
    hmean i, hmean j] at hc
  simp only [Pi.mul_apply] at hc
  linarith

set_option backward.isDefEq.respectTransparency false in
/-- Full coordinate means and covariances identify covariances after any two
continuous real linear observations of the actual random vectors. -/
theorem covariance_comp_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    {X : Ω → κ → ℝ} {Z : Ω' → κ → ℝ}
    (hX : MemLp X 2 μ) (hZ : MemLp Z 2 ν)
    (hmean : (∫ ω, X ω ∂μ) = ∫ ω, Z ω ∂ν)
    (hcov : ∀ i j, cov[(fun ω => X ω i), (fun ω => X ω j); μ] =
      cov[(fun ω => Z ω i), (fun ω => Z ω j); ν])
    (L K : (κ → ℝ) →L[ℝ] ℝ) :
    cov[(fun ω => L (X ω)), (fun ω => K (X ω)); μ] =
      cov[(fun ω => L (Z ω)), (fun ω => K (Z ω)); ν] := by
  have hXi : Integrable X μ := hX.integrable (by norm_num)
  have hZi : Integrable Z ν := hZ.integrable (by norm_num)
  have hmeans (i : κ) : (∫ ω, X ω i ∂μ) = ∫ ω, Z ω i ∂ν := by
    let P : (κ → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
    calc
      (∫ ω, X ω i ∂μ) = P (∫ ω, X ω ∂μ) := P.integral_comp_comm hXi
      _ = P (∫ ω, Z ω ∂ν) := congrArg P hmean
      _ = ∫ ω, Z ω i ∂ν := (P.integral_comp_comm hZi).symm
  have hsecond := integral_mul_coordinates_eq_of_mean_covariance_eq hX hZ hmeans hcov
  let B := (ContinuousLinearMap.mul ℝ ℝ).bilinearComp L K
  have hprod := integral_bilin_quadratic_eq_of_second_moments_eq B hX hZ hsecond
  change (∫ ω, L (X ω) * K (X ω) ∂μ) = (∫ ω, L (Z ω) * K (Z ω) ∂ν) at hprod
  have hiX : MemLp (fun ω => L (X ω)) 2 μ := L.comp_memLp' hX
  have hkX : MemLp (fun ω => K (X ω)) 2 μ := K.comp_memLp' hX
  have hiZ : MemLp (fun ω => L (Z ω)) 2 ν := L.comp_memLp' hZ
  have hkZ : MemLp (fun ω => K (Z ω)) 2 ν := K.comp_memLp' hZ
  rw [covariance_eq_sub hiX hkX, covariance_eq_sub hiZ hkZ]
  simp only [Pi.mul_apply]
  rw [hprod, L.integral_comp_comm hXi, K.integral_comp_comm hXi,
    L.integral_comp_comm hZi, K.integral_comp_comm hZi, hmean]

set_option backward.isDefEq.respectTransparency false in
/-- Matching full coordinate means and covariances preserves the covariance of
every pair of continuous real linear functionals, rather than only coordinate
projections. Finite second moments justify all products and expectations. -/
theorem covariance_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    (ρ σ : Measure (κ → ℝ)) [IsProbabilityMeasure ρ] [IsProbabilityMeasure σ]
    (hρ : MemLp id 2 ρ) (hσ : MemLp id 2 σ)
    (hmean : (∫ x, x ∂ρ) = ∫ x, x ∂σ)
    (hcov : ∀ i j, cov[(fun x => x i), (fun x => x j); ρ] =
      cov[(fun x => x i), (fun x => x j); σ])
    (L K : (κ → ℝ) →L[ℝ] ℝ) : cov[L, K; ρ] = cov[L, K; σ] := by
  exact covariance_comp_continuousLinearMap_eq_of_coordinate_mean_covariance_eq
    hρ hσ hmean hcov L K

end NLAlib
