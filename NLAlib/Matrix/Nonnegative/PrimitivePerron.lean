import NLAlib.Matrix.Nonnegative.PerronPositivePeripheral
import NLAlib.Matrix.Nonnegative.PerronDeflation
import NLAlib.Matrix.Spectral.ConvergentPeripheral

/-! # Primitive Perron equivalences and the rank-one power limit

Positive powers, unique peripheral spectrum, and convergence of normalized
powers are equivalent. The positive rank-one projector is the actual limit.
Source: Horn–Johnson, Matrix Analysis, Chapter 8.
-/
noncomputable section
open Matrix Finset Filter
open scoped Matrix Topology
namespace Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

open scoped Matrix.Norms.L2Operator in
omit [Nonempty ι] in
/-- Convergence of normalized powers to a strictly positive matrix forces a
strictly positive finite power. -/
theorem isPrimitive_of_tendsto_normalized_pow_pos {A P : Matrix ι ι ℝ} {r : ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hr : 0 < r) (hP : ∀ i j, 0 < P i j)
    (hlim : Tendsto (fun k : ℕ => (r⁻¹ • A) ^ k) atTop (𝓝 P)) : A.IsPrimitive := by
  have hij (i j : ι) : ∀ᶠ k : ℕ in atTop, 0 < ((r⁻¹ • A) ^ k) i j :=
    (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim i) j).eventually (lt_mem_nhds (hP i j))
  have hall : ∀ᶠ k : ℕ in atTop, ∀ i j, 0 < ((r⁻¹ • A) ^ k) i j :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hij i)
  obtain ⟨k, hk, hkpos⟩ := ((eventually_ge_atTop 1).and hall).exists
  refine ⟨hA, k, by omega, fun i j => ?_⟩
  have h := hkpos i j
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul] at h
  exact (mul_pos_iff_of_pos_left (pow_pos (inv_pos.mpr hr) k)).mp h

open scoped Matrix.Norms.L2Operator in
/-- For a nonzero irreducible nonnegative matrix, primitivity is equivalent to
the Perron root being the only peripheral spectral point.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsIrreducible.isPrimitive_iff_unique_peripheral {A : Matrix ι ι ℝ}
    (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    A.IsPrimitive ↔ ∀ μ ∈ spectrum ℂ (A.map Complex.ofReal),
      ‖μ‖ = (spectralRadius ℂ (A.map Complex.ofReal)).toReal →
        μ = ((spectralRadius ℂ (A.map Complex.ofReal)).toReal : ℂ) := by
  refine ⟨fun hP μ hμ hnorm => hP.peripheral_eigenvalue_eq_perron hAne hμ hnorm,
    fun hperipheral => ?_⟩
  obtain ⟨p, q, hr, hp, hq, _, _, hAp, hqA⟩ := hA.exists_positive_perron_pair hAne
  have hlim := (hA.perron_power_limit_and_rate hAne hp hq hAp hqA hperipheral).1
  apply isPrimitive_of_tendsto_normalized_pow_pos hA.nonneg hr _ hlim
  exact (perron_projector_pos_idempotent_and_commutes hp hq hAp hqA).1

open scoped Matrix.Norms.L2Operator in
/-- For an irreducible nonzero nonnegative matrix, normalized matrix powers
converge to some matrix precisely when the matrix is primitive.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsIrreducible.isPrimitive_iff_exists_tendsto_normalized_pow
    {A : Matrix ι ι ℝ} (hA : A.IsIrreducible) (hAne : A ≠ 0) :
    A.IsPrimitive ↔ ∃ L : Matrix ι ι ℝ,
      Tendsto (fun k : ℕ => (((spectralRadius ℂ (A.map Complex.ofReal)).toReal)⁻¹ • A) ^ k)
        atTop (𝓝 L) := by
  constructor
  · intro hP
    obtain ⟨p, q, _, hp, hq, _, _, hAp, hqA⟩ := hA.exists_positive_perron_pair hAne
    exact ⟨_, (hA.perron_power_limit_and_rate hAne hp hq hAp hqA
      ((hA.isPrimitive_iff_unique_peripheral hAne).mp hP)).1⟩
  · rintro ⟨L, hlim⟩
    apply (hA.isPrimitive_iff_unique_peripheral hAne).mpr
    intro μ hμ hμnorm
    obtain ⟨_, _, hr, _, _, _, _, _, _⟩ := hA.exists_positive_perron_pair hAne
    let r := (spectralRadius ℂ (A.map Complex.ofReal)).toReal
    let T := r⁻¹ • A
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hTmap : T.map Complex.ofReal = (r : ℂ)⁻¹ • A.map Complex.ofReal := by
      ext i j
      simp only [T, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.ofReal_mul, Complex.ofReal_inv]
    have hc : Continuous (fun M : Matrix ι ι ℝ => M.map Complex.ofReal) := by fun_prop
    have hClim : Tendsto (fun k : ℕ => (T.map Complex.ofReal) ^ k) atTop
        (𝓝 (L.map Complex.ofReal)) := by
      simpa only [Function.comp_def, NLAlib.map_ofReal_matrix_pow] using
        hc.continuousAt.tendsto.comp hlim
    obtain ⟨z, hz, hAz⟩ := NLAlib.exists_mulVec_eq_smul_of_mem_spectrum hμ
    have hTz : T.map Complex.ofReal *ᵥ z = (μ / (r : ℂ)) • z := by
      rw [hTmap, Matrix.smul_mulVec, hAz, smul_smul]
      congr 1
      ring
    have hunitnorm : ‖μ / (r : ℂ)‖ = 1 := by
      rw [norm_div, hμnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact div_self hr.ne'
    have hμone := eigenvalue_eq_one_of_tendsto_pow hClim
      (mem_spectrum_of_mulVec_eq_smul hz hTz) hunitnorm
    exact (div_eq_one_iff_eq hrC).mp hμone

open scoped Matrix.Norms.L2Operator in
/-- Primitive matrices have a positive normalized Perron pair, the explicit
rank-one normalized power limit, and every admissible geometric convergence rate.
All input hypotheses concern the matrix itself.
Source: Horn–Johnson, Chapter 8.
atlas: primitive-perron-power-limit (partial) -/
theorem IsPrimitive.exists_perron_power_limit_and_rate {A : Matrix ι ι ℝ}
    (hA : A.IsPrimitive) (hAne : A ≠ 0) :
    ∃ p q : ι → ℝ, (∀ i, 0 < p i) ∧ (∀ i, 0 < q i) ∧
      (∑ i, p i = 1) ∧ (∑ i, q i = 1) ∧
      let T := ((spectralRadius ℂ (A.map Complex.ofReal)).toReal)⁻¹ • A
      let P := (q ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p q
      Tendsto (fun k : ℕ => T ^ k) atTop (𝓝 P) ∧
        ∀ θ : ℝ, (spectralRadius ℂ ((T - P).map Complex.ofReal)).toReal < θ → θ < 1 →
          ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, NLAlib.specNorm (T ^ k - P) ≤ C * θ ^ k := by
  obtain ⟨p, q, _, hp, hq, hps, hqs, hAp, hqA⟩ := hA.isIrreducible.exists_positive_perron_pair hAne
  exact ⟨p, q, hp, hq, hps, hqs, hA.isIrreducible.perron_power_limit_and_rate
    hAne hp hq hAp hqA ((hA.isIrreducible.isPrimitive_iff_unique_peripheral hAne).mp hA)⟩

end Matrix
