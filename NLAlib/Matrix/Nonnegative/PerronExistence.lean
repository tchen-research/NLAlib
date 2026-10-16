import NLAlib.Matrix.Nonnegative.PerronPositive
import NLAlib.Matrix.Nonnegative.PositiveSubsolutionSpectrum
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Perron eigenvectors for every nonnegative matrix

Positive perturbations have normalized positive eigenvectors by compact
minimization. A convergent subsequence in the simplex gives a nonnegative
eigenvector of the original matrix. The complex weighted-coordinate bound
identifies its eigenvalue with the full complex spectral radius, including
the reducible and zero-spectral-radius cases.
Source: Horn–Johnson, Matrix Analysis, Theorem 8.3.1.
-/

noncomputable section
open Matrix Finset Filter
open scoped Matrix Topology ENNReal

namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Every entrywise nonnegative real matrix on a nonempty finite index set has
a nonnegative unit-sum right eigenvector at its complex spectral radius.
No irreducibility, invertibility, or positive-radius hypothesis is needed.
Source: Horn–Johnson, Theorem 8.3.1.
atlas: nonnegative-perron-eigenpair (partial) -/
theorem exists_nonnegative_perron_eigenvector_and_comparison {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p ∧
      (∀ B : Matrix ι ι ℂ, (∀ i j, norm (B i j) ≤ A i j) →
        spectralRadius ℂ B ≤ spectralRadius ℂ (A.map Complex.ofReal)) ∧
      ∀ t : ℝ, (spectralRadius ℂ (A.map Complex.ofReal)).toReal < t →
        ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ ∀ i, (A *ᵥ x) i < t * x i := by
  classical
  let ε : ℕ → ℝ := fun k => ((k : ℝ) + 1)⁻¹
  have hε (k : ℕ) : 0 < ε k := by dsimp [ε]; positivity
  let C : ℕ → Matrix ι ι ℝ := fun k i j => A i j + ε k
  have hCpos (k : ℕ) (i j : ι) : 0 < C k i j := add_pos_of_nonneg_of_pos (hA i j) (hε k)
  choose r p hr hp hpsum heig using fun k => exists_positive_eigenpair_of_pos (hCpos k)
  let S : Set (ι → ℝ) := Set.Icc 0 (fun _ => 1) ∩ {x | ∑ i, x i = 1}
  have hS : IsCompact S := isCompact_Icc.inter_right
    (isClosed_eq (by fun_prop) continuous_const)
  have hpS (k : ℕ) : p k ∈ S := by
    refine ⟨⟨fun i => (hp k i).le, fun i => ?_⟩, hpsum k⟩
    exact (Finset.single_le_sum (fun j _ => (hp k j).le) (mem_univ i)).trans_eq (hpsum k)
  obtain ⟨p₀, hp₀, φ, hφ, hplim⟩ := hS.tendsto_subseq hpS
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  have hClim : Tendsto C atTop (𝓝 A) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    simpa only [C, add_zero] using tendsto_const_nhds.add hεlim
  have hCsub := hClim.comp hφ.tendsto_atTop
  have hmulcont : Continuous (fun z : Matrix ι ι ℝ × (ι → ℝ) => z.1 *ᵥ z.2) := by fun_prop
  have hAP := hmulcont.continuousAt.tendsto.comp (hCsub.prodMk_nhds hplim)
  let ρ : ℝ := ∑ i, (A *ᵥ p₀) i
  have hrdef (k : ℕ) : r k = ∑ i, (C k *ᵥ p k) i := by
    rw [heig k]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hpsum, mul_one]
  have hrcont : Continuous (fun x : ι → ℝ => ∑ i, x i) := by fun_prop
  have hrlim : Tendsto (fun k => r (φ k)) atTop (𝓝 ρ) := by
    simpa only [ρ, Function.comp_def, ← hrdef] using hrcont.continuousAt.tendsto.comp hAP
  have hsmulcont : Continuous (fun z : ℝ × (ι → ℝ) => z.1 • z.2) := by fun_prop
  have hRP := hsmulcont.continuousAt.tendsto.comp (hrlim.prodMk_nhds hplim)
  have hlimEig : A *ᵥ p₀ = ρ • p₀ := by
    exact tendsto_nhds_unique hAP (by simpa only [Function.comp_def, heig] using hRP)
  have hρ : 0 ≤ ρ := ge_of_tendsto hrlim (Eventually.of_forall fun k => (hr (φ k)).le)
  have hρupper (B : Matrix ι ι ℂ) (hBA : ∀ i j, norm (B i j) ≤ A i j) :
      spectralRadius ℂ B ≤ ENNReal.ofReal ρ := by
    unfold spectralRadius
    apply iSup₂_le
    intro μ hμ
    obtain ⟨z, hz, hAz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
    have hμr (k : ℕ) : ‖μ‖ ≤ r k := by
      apply norm_eigenvalue_le_of_abs_le_of_positive_subsolution (A := C k) (p := p k)
        (fun i j => ?_) (hp k) (fun i => ?_) hz hAz
      · exact (hBA i j).trans (le_add_of_nonneg_right (hε k).le)
      · rw [heig k]
        exact le_rfl
    have hμρ : ‖μ‖ ≤ ρ := ge_of_tendsto hrlim (Eventually.of_forall fun k => hμr (φ k))
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hμρ
  have hpne : p₀ ≠ 0 := by
    intro hz
    have hsum := hp₀.2
    rw [hz] at hsum
    simp at hsum
  have hcpne : (fun i => (p₀ i : ℂ)) ≠ 0 := by
    intro hz
    apply hpne
    funext i
    apply Complex.ofReal_injective
    simpa only [Pi.zero_apply, Complex.ofReal_zero] using congrFun hz i
  have hceig : A.map Complex.ofReal *ᵥ (fun i => (p₀ i : ℂ)) =
      (ρ : ℂ) • (fun i => (p₀ i : ℂ)) := by
    funext i
    have h := congrArg Complex.ofReal (congrFun hlimEig i)
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Matrix.map_apply] using h
  have hmem := mem_spectrum_of_mulVec_eq_smul hcpne hceig
  have hρlower : ENNReal.ofReal ρ ≤ spectralRadius ℂ (A.map Complex.ofReal) := by
    have hnorm : (‖(ρ : ℂ)‖₊ : ℝ≥0∞) ≤ spectralRadius ℂ (A.map Complex.ofReal) :=
      le_iSup_of_le (ρ : ℂ) (le_iSup_of_le hmem le_rfl)
    rw [← ENNReal.ofReal_coe_nnreal] at hnorm
    simpa only [coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ] using hnorm
  have hAA : ∀ i j, ‖A.map Complex.ofReal i j‖ ≤ A i j := by
    intro i j
    simp only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j), le_refl]
  have hρeq := le_antisymm (hρupper _ hAA) hρlower
  refine ⟨p₀, fun i => hp₀.1.1 i, hp₀.2, ?_, (fun B hBA => ?_), ?_⟩
  · rw [hρeq, ENNReal.toReal_ofReal hρ]
    exact hlimEig
  · rw [hρeq]
    exact hρupper B hBA
  · intro t ht
    have htρ : ρ < t := by simpa only [hρeq, ENNReal.toReal_ofReal hρ] using ht
    obtain ⟨k, hk⟩ := (hrlim.eventually (gt_mem_nhds htρ)).exists
    refine ⟨p (φ k), hp (φ k), fun i => ?_⟩
    have hcomp : (A *ᵥ p (φ k)) i ≤ (C (φ k) *ᵥ p (φ k)) i :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (hε (φ k)).le) (hp (φ k) j).le
    rw [heig] at hcomp
    exact hcomp.trans_lt (mul_lt_mul_of_pos_right hk (hp (φ k) i))

/-- Every nonnegative finite real matrix has a nonnegative unit-sum Perron
eigenvector, including reducible matrices and zero spectral radius.
Source: Horn–Johnson, Theorem 8.3.1.
atlas: nonnegative-perron-eigenpair (partial) -/
theorem exists_nonnegative_perron_eigenvector {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) :
    ∃ p : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p := by
  obtain ⟨p, hp, hs, he, _, _⟩ := exists_nonnegative_perron_eigenvector_and_comparison hA
  exact ⟨p, hp, hs, he⟩

/-- Complex entrywise domination by a nonnegative real matrix implies spectral
radius domination. Reducibility and zero spectral radius are included.
Source: Horn–Johnson, Chapter 8.
atlas: nonnegative-spectral-radius-comparison (partial) -/
theorem spectralRadius_le_of_abs_le_nonnegative {A : Matrix ι ι ℝ} {B : Matrix ι ι ℂ}
    (hA : ∀ i j, 0 ≤ A i j) (hBA : ∀ i j, norm (B i j) ≤ A i j) :
    spectralRadius ℂ B ≤ spectralRadius ℂ (A.map Complex.ofReal) := by
  obtain ⟨_, _, _, _, hcomp, _⟩ := exists_nonnegative_perron_eigenvector_and_comparison hA
  exact hcomp B hBA

/-- Above the spectral radius there always exists a strictly positive strict
subsolution, even when the Perron eigenvector itself has zero coordinates.
This gives the unattained infimum case of Collatz–Wielandt.
Source: Horn–Johnson, Chapter 8.
atlas: collatz-wielandt-certificates (partial) -/
theorem exists_positive_strict_subsolution_of_spectralRadius_lt
    {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) {t : ℝ}
    (ht : (spectralRadius ℂ (A.map Complex.ofReal)).toReal < t) :
    ∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ ∀ i, (A *ᵥ x) i < t * x i := by
  obtain ⟨_, _, _, _, _, hsub⟩ := exists_nonnegative_perron_eigenvector_and_comparison hA
  exact hsub t ht

omit [Nonempty ι] in
/-- The complex spectral radius of a real matrix is unchanged by transposition. -/
theorem spectralRadius_complexification_transpose (A : Matrix ι ι ℝ) :
    spectralRadius ℂ (Aᵀ.map Complex.ofReal) = spectralRadius ℂ (A.map Complex.ofReal) := by
  have hspec : spectrum ℂ (Aᵀ.map Complex.ofReal) = spectrum ℂ (A.map Complex.ofReal) := by
    ext μ
    change μ ∈ spectrum ℂ (A.map Complex.ofReal)ᵀ ↔ _
    simp only [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose]
  simp only [spectralRadius, hspec]

/-- Every nonnegative real matrix has both normalized nonnegative right and
left Perron eigenvectors, at the same complex spectral radius.
Source: Horn–Johnson, Theorem 8.3.1.
atlas: nonnegative-perron-eigenpair (partial) -/
theorem exists_nonnegative_perron_pair {A : Matrix ι ι ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    ∃ p q : ι → ℝ, (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ q i) ∧
      (∑ i, p i = 1) ∧ (∑ i, q i = 1) ∧
      A *ᵥ p = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • p ∧
      q ᵥ* A = (spectralRadius ℂ (A.map Complex.ofReal)).toReal • q := by
  obtain ⟨p, hp, hs, he⟩ := exists_nonnegative_perron_eigenvector hA
  obtain ⟨q, hq, hqs, hqe⟩ := exists_nonnegative_perron_eigenvector (A := Aᵀ) (fun i j => hA j i)
  rw [spectralRadius_complexification_transpose, Matrix.mulVec_transpose] at hqe
  exact ⟨p, q, hp, hq, hs, hqs, he, hqe⟩

end Matrix
