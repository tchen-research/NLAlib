import NLAlib.Matrix.Nonnegative.PerronIrreducible
import NLAlib.Matrix.Spectral.DeflatedPeripheral
import NLAlib.Matrix.Spectral.ProjectorDeflationPowers

/-! # Normalized Perron deflation and quantitative power convergence

Once the Perron root is the unique peripheral eigenvalue, the positive
left–right projector removes it and leaves a strict spectral gap. Real
matrix powers then converge to that projector at every rate above the
deflated spectral radius. Source: Horn–Johnson, Chapter 8.
-/
noncomputable section
open Matrix Finset Filter
open scoped Matrix Topology
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
/-- Normalizing a paired Perron eigenvalue makes its projector fixed on both sides. -/
theorem perron_normalization_projector_identities {A : Matrix ι ι ℝ}
    {p q : ι → ℝ} {r : ℝ} (hr : 0 < r) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hAp : A *ᵥ p = r • p) (hqA : q ᵥ* A = r • q) :
    let P := (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q
    P * P = P ∧ (r⁻¹ • A) * P = P ∧ P * (r⁻¹ • A) = P := by
  have hpair : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  have h := NLAlib.mul_normalized_vecMulVec_eq_smul hAp hqA
  refine ⟨NLAlib.normalized_vecMulVec_mul_self hpair.ne', ?_, ?_⟩
  · rw [Matrix.smul_mul, h.1, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  · rw [Matrix.mul_smul, h.2, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

open scoped Matrix.Norms.L2Operator in
/-- Irreducible Perron deflation has subunit spectral radius exactly under
the unique-peripheral hypothesis. This direction constructs the gap.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsIrreducible.deflated_perron_spectralRadius_lt_one
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (hAne : A ≠ 0)
    {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hAp : A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p)
    (hqA : q ᵥ* A = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • q)
    (hperipheral : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal),
      ‖μ‖ = (spectralRadius ℂ (A.map Complex.ofReal)).toReal →
        μ = ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ)) :
    spectralRadius ℂ ((((spectralRadius ℂ (A.map Complex.ofReal)).toReal)⁻¹ • A -
      (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q).map Complex.ofReal) < 1 := by
  let r := (spectralRadius ℂ (A.map Complex.ofReal)).toReal
  obtain ⟨_, _, hr, _, _, _, _, _, _⟩ := hA.exists_positive_perron_pair hAne
  let pc : ι → ℂ := fun i => (p i : ℂ)
  let qc : ι → ℂ := fun i => (q i : ℂ)
  have hpc : pc ≠ 0 := by
    intro hz
    let i : ι := Classical.choice ‹Nonempty ι›
    have hp0 : (p i : ℂ) = 0 := congrFun hz i
    have hp0R : p i = 0 := Complex.ofReal_injective hp0
    exact (hp i).ne' hp0R
  have hpairReal : 0 < q ⬝ᵥ p := Finset.sum_pos (fun i _ => mul_pos (hq i) (hp i)) Finset.univ_nonempty
  have hpairCast : qc ⬝ᵥ pc = ((q ⬝ᵥ p : ℝ) : ℂ) := by
    simp only [pc, qc, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul]
  have hpair : qc ⬝ᵥ pc ≠ 0 := by rw [hpairCast]; exact_mod_cast hpairReal.ne'
  have hAc : A.map Complex.ofReal *ᵥ pc = (r : ℂ) • pc := by
    funext i
    have h := congrArg Complex.ofReal (congrFun hAp i)
    simpa only [r, pc, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  have hqc : qc ᵥ* A.map Complex.ofReal = (r : ℂ) • qc := by
    funext i
    have h := congrArg Complex.ofReal (congrFun hqA i)
    simpa only [r, qc, Matrix.vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  have hbound (μ : ℂ) (hμ : μ ∈ spectrum ℂ (A.map Complex.ofReal)) : ‖μ‖ ≤ r := by
    obtain ⟨z, hz, hAz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
    exact norm_eigenvalue_le_of_abs_le_of_positive_subsolution
      (A := A) (fun i j => by
        simp only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hA.nonneg i j), le_refl]) hp
      (fun i => by rw [hAp]; exact le_rfl) hz hAz
  have hgap := NLAlib.deflated_spectralRadius_lt_one_of_simple_unique_peripheral
    (A.map Complex.ofReal) hr hpc hpair hAc hqc
    (hA.rootMultiplicity_perron_complexification_eq_one hAne) hbound hperipheral
  have hmap : (r⁻¹ • A - (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q).map Complex.ofReal =
      (r : ℂ)⁻¹ • A.map Complex.ofReal - (qc ⬝ᵥ pc)⁻¹ • Matrix.vecMulVec pc qc := by
    rw [hpairCast]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      pc, qc, smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [hmap]
  exact hgap

open scoped Matrix.Norms.L2Operator in
/-- Unique peripheral spectrum gives the normalized Perron projector limit,
and every strictly larger geometric rate bounds all errors including exponent zero.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsIrreducible.perron_power_limit_and_rate
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (hAne : A ≠ 0)
    {p q : ι → ℝ} (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (hAp : A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p)
    (hqA : q ᵥ* A = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • q)
    (hperipheral : ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal),
      ‖μ‖ = (spectralRadius ℂ (A.map Complex.ofReal)).toReal →
        μ = ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ)) :
    let T := ((spectralRadius ℂ (A.map Complex.ofReal)).toReal)⁻¹ • A
    let P := (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q
    Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 P) ∧
      ∀ θ : ℝ, (spectralRadius ℂ ((T - P).map Complex.ofReal)).toReal < θ → θ < 1 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, NLAlib.specNorm (T ^ k - P) ≤ C * θ ^ k := by
  obtain ⟨_, _, hr, _, _, _, _, _, _⟩ := hA.exists_positive_perron_pair hAne
  have hid := perron_normalization_projector_identities hr hp hq hAp hqA
  have hgap := hA.deflated_perron_spectralRadius_lt_one hAne hp hq hAp hqA hperipheral
  exact ⟨NLAlib.tendsto_matrix_pow_projector_of_deflated_spectralRadius_lt_one _ _ hid.1 hid.2.1 hid.2.2 hgap,
    fun θ hθ _ => NLAlib.exists_specNorm_matrix_pow_sub_projector_le_geometric _ _ hid.1 hid.2.1 hid.2.2 hθ⟩

end Matrix
