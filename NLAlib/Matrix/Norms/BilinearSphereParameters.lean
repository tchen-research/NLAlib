import NLAlib.Matrix.Norms.BilinearProbes
import NLAlib.Matrix.Norms.QuadraticSeries

/-! # Literal unit-sphere bilinear coefficient parameters

The attained closed-ball energy agrees with the source's literal
unit-sphere standard-deviation supremum. Its equal-vector restriction
supplies the actual Gaussian coordinate energy used by concentration.
Source: arXiv:2406.11453v2, Section 2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
namespace NLAlib
variable {ι n : Type*} [Fintype ι] [Fintype n]
local notation "E" => EuclideanSpace ℂ n

private theorem norm_coefficient_bilinear_real_smul
    (A : Matrix n n ℂ) (v w : E) (a b : ℝ) :
    ‖star (a • v).ofLp ⬝ᵥ (A *ᵥ (b • w).ofLp)‖ =
      |a| * |b| * ‖star v.ofLp ⬝ᵥ (A *ᵥ w.ofLp)‖ := by
  simp only [WithLp.ofLp_smul, Matrix.mulVec_smul, star_smul, star_trivial,
    smul_dotProduct, dotProduct_smul, smul_smul, norm_smul, Real.norm_eq_abs, abs_mul]
  ring

/-- A literal uniform unit-sphere coefficient budget bounds the attained
closed-ball bilinear energy. Zero probes and empty shapes are included. -/
theorem bilinearSquareMass_le_of_unitSphere
    (A : ι → Matrix n n ℂ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ v w : E, ‖v‖ = 1 → ‖w‖ = 1 →
      (∑ i, ‖star v.ofLp ⬝ᵥ (A i *ᵥ w.ofLp)‖ ^ 2) ≤ B) :
    bilinearSquareMass A Finset.univ ≤ B := by
  obtain ⟨v, w, hv, hw, he⟩ := exists_bilinearSquareMass_eq A Finset.univ
  rw [he]
  by_cases hv0 : v = 0
  · simpa only [hv0, WithLp.ofLp_zero, star_zero, zero_dotProduct, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] using hB
  by_cases hw0 : w = 0
  · simpa only [hw0, WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, norm_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero] using hB
  let v' := NormedSpace.normalize v
  let w' := NormedSpace.normalize w
  have hs : (‖v‖ * ‖w‖) ^ 2 ≤ 1 := pow_le_one₀ (by positivity)
    (by simpa only [one_mul] using mul_le_mul hv hw (norm_nonneg w) (by norm_num : (0 : ℝ) ≤ 1))
  have hscale (i : ι) : ‖star v.ofLp ⬝ᵥ (A i *ᵥ w.ofLp)‖ ^ 2 =
      (‖v‖ * ‖w‖) ^ 2 * ‖star v'.ofLp ⬝ᵥ (A i *ᵥ w'.ofLp)‖ ^ 2 := by
    have hi := norm_coefficient_bilinear_real_smul (A i) v' w' ‖v‖ ‖w‖
    simp only [v', w', NormedSpace.norm_smul_normalize, abs_of_nonneg (norm_nonneg _)] at hi
    rw [hi]
    ring
  calc
    _ = (‖v‖ * ‖w‖) ^ 2 * ∑ i, ‖star v'.ofLp ⬝ᵥ (A i *ᵥ w'.ofLp)‖ ^ 2 := by
      simp_rw [hscale]
      rw [Finset.mul_sum]
    _ ≤ ∑ i, ‖star v'.ofLp ⬝ᵥ (A i *ᵥ w'.ofLp)‖ ^ 2 :=
      mul_le_of_le_one_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) hs
    _ ≤ B := h v' w' (NormedSpace.norm_normalize hv0) (NormedSpace.norm_normalize hw0)

/-- The actual bilinear square-root parameter is exactly the source
unit-sphere supremum, rather than a larger auxiliary budget.
Source: arXiv:2406.11453v2, Section 2.
atlas: gaussian-free-spectrum-two-sided (partial). -/
theorem sqrt_bilinearSquareMass_eq_sSup_unitSphere [Nonempty n]
    (A : ι → Matrix n n ℂ) :
    Real.sqrt (bilinearSquareMass A Finset.univ) =
      sSup ((fun q : E × E => Real.sqrt (∑ i, ‖star q.1.ofLp ⬝ᵥ (A i *ᵥ q.2.ofLp)‖ ^ 2)) ''
        {q | ‖q.1‖ = 1 ∧ ‖q.2‖ = 1}) := by
  let S := ((fun q : E × E => Real.sqrt (∑ i, ‖star q.1.ofLp ⬝ᵥ (A i *ᵥ q.2.ofLp)‖ ^ 2)) ''
    {q | ‖q.1‖ = 1 ∧ ‖q.2‖ = 1})
  have hSne : S.Nonempty := by
    obtain ⟨v, hv⟩ := exists_norm_eq E (show (0 : ℝ) ≤ 1 by norm_num)
    exact ⟨_, ⟨(v, v), ⟨hv, hv⟩, rfl⟩⟩
  have hLUB : IsLUB S (Real.sqrt (bilinearSquareMass A Finset.univ)) := by
    constructor
    · rintro _ ⟨q, hq, rfl⟩
      exact Real.sqrt_le_sqrt (sum_bilinear_sq_le_bilinearSquareMass A Finset.univ
        q.1 q.2 hq.1.le hq.2.le)
    · intro B hB
      have hB0 : 0 ≤ B := by
        obtain ⟨r, hr⟩ := hSne
        have hr0 : 0 ≤ r := by
          rcases hr with ⟨q, _, rfl⟩
          exact Real.sqrt_nonneg _
        exact hr0.trans (hB hr)
      apply Real.sqrt_le_iff.mpr ⟨hB0, ?_⟩
      apply bilinearSquareMass_le_of_unitSphere A (sq_nonneg B)
      intro v w hv hw
      exact (Real.sqrt_le_iff.mp (hB ⟨(v, w), ⟨hv, hw⟩, rfl⟩)).2
  exact (hLUB.csSup_eq hSne).symm

/-- The actual unit-vector Gaussian quadratic coordinate energy is
bounded by the true bilinear square mass, with no variance certificate. -/
theorem sum_re_quadForm_sq_le_bilinearSquareMass
    (A : ι → Matrix n n ℂ) (u : n → ℂ) (hu : ‖WithLp.toLp 2 u‖ = 1) :
    (∑ i, (quadForm (A i) u).re ^ 2) ≤ bilinearSquareMass A Finset.univ := by
  apply le_trans _ (sum_bilinear_sq_le_bilinearSquareMass A Finset.univ
    (WithLp.toLp 2 u) (WithLp.toLp 2 u) hu.le hu.le)
  apply Finset.sum_le_sum
  intro i _
  simpa only [quadForm, WithLp.ofLp_toLp] using
    (show (quadForm (A i) u).re ^ 2 ≤ ‖quadForm (A i) u‖ ^ 2 by
      nlinarith [Complex.sq_norm_sub_sq_re (quadForm (A i) u), sq_nonneg (quadForm (A i) u).im])

end NLAlib
