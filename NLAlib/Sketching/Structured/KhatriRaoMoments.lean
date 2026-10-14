import NLAlib.Sketching.Structured.KhatriRaoBasic
import NLAlib.Probability.SubGaussian.ExpSquareMoments
import NLAlib.Matrix.Norms.Core
import NLAlib.Probability.Moments.Euclidean
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Moments of independent tensor-product probes

Directional exponential-square bounds pass to factorial even-moment
budgets without assuming centered factors or independent coordinates.
The tensor-product construction retains the exact Euclidean coefficient
norm rather than paying the ambient tensor dimension.

Source: Heidary, *The Sharp Logarithmic Cost of Khatri–Rao Subspace
Embeddings*, Lemma 2.2 and its proof.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

/-- Independent vector factors multiply homogeneous directional even-moment
budgets. Arbitrary coordinate dependence within each factor is allowed.
Finite Jensen keeps the Euclidean tensor coefficient norm exactly.
Source: Heidary, Lemma 2.2, tensor induction. -/
theorem integrable_and_integral_pow_two_mul_dotProduct_khatriRaoProbe_le
    {d : ℕ} {n : Fin d → ℕ}
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {p : ℕ} (hp : 0 < p)
    {B : ℝ} (hB : 0 ≤ B)
    (hmoment : ∀ j (a : Fin (n j) → ℝ),
      Integrable (fun g => (a ⬝ᵥ g) ^ (2 * p)) (ν j) ∧
        (∫ g, (a ⬝ᵥ g) ^ (2 * p) ∂ν j) ≤ B * ‖WithLp.toLp 2 a‖ ^ (2 * p))
    (a : (∀ j : Fin d, Fin (n j)) → ℝ) :
    Integrable (fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) (Measure.pi ν) ∧
      (∫ g, (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p) ∂Measure.pi ν) ≤
        B ^ d * ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
  classical
  induction d with
  | zero =>
      simp only [khatriRaoProbe, Finset.univ_eq_empty, Finset.prod_empty,
        dotProduct, mul_one, Fintype.sum_unique]
      refine ⟨integrable_const _, ?_⟩
      rw [integral_const]
      simp only [probReal_univ, one_smul, pow_zero, one_mul]
      rw [show ‖WithLp.toLp 2 a‖ ^ (2 * p) = (‖WithLp.toLp 2 a‖ ^ 2) ^ p by rw [pow_mul]]
      rw [norm_toLp_sq_eq_dotProduct_self]
      simp only [dotProduct, Fintype.sum_unique, ← pow_two, pow_mul]
      exact le_refl _
  | succ d ih =>
      let ν' : ∀ j : Fin d, Measure (Fin (n j.succ) → ℝ) := fun j => ν j.succ
      let T : Matrix (Fin (n 0)) (∀ j : Fin d, Fin (n j.succ)) ℝ :=
        fun i b => a (Fin.cons i b)
      have htail (b : (∀ j : Fin d, Fin (n j.succ)) → ℝ) :=
        ih ν' (fun j => hmoment j.succ) b
      have hnorm := integrable_and_integral_norm_mulVec_pow_two_mul_le
        (khatriRaoProbe (n := fun j : Fin d => n j.succ))
        measurable_khatriRaoProbe.aemeasurable hp (pow_nonneg hB d) htail T
      let F : (Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ) → ℝ :=
        fun g => ((T *ᵥ khatriRaoProbe g.2) ⬝ᵥ g.1) ^ (2 * p)
      have hFmeas : StronglyMeasurable F := by
        apply Continuous.stronglyMeasurable
        dsimp [F]
        unfold khatriRaoProbe mulVec dotProduct
        fun_prop
      have hFnonneg (g) : 0 ≤ F g := Even.pow_nonneg (even_two.mul_right p) _
      have hfactor (g : ∀ j : Fin d, Fin (n j.succ) → ℝ) :=
        hmoment 0 (T *ᵥ khatriRaoProbe g)
      have hinner : Integrable (fun g => ∫ g₀, ‖F (g₀, g)‖ ∂ν 0) (Measure.pi ν') := by
        apply (hnorm.1.const_mul B).mono_nonneg
          hFmeas.norm.integral_prod_left'.aestronglyMeasurable
        · exact ae_of_all _ fun _ => integral_nonneg fun _ => norm_nonneg _
        · apply ae_of_all
          intro g
          simpa only [Real.norm_of_nonneg (hFnonneg _)] using (hfactor g).2
      have hFi : Integrable F ((ν 0).prod (Measure.pi ν')) :=
        (integrable_prod_iff' hFmeas.aestronglyMeasurable).2
          ⟨ae_of_all _ fun g => (hfactor g).1, hinner⟩
      have hFb : (∫ g, F g ∂(ν 0).prod (Measure.pi ν')) ≤
          B ^ (d + 1) * ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
        rw [integral_prod_symm _ hFi]
        calc
          (∫ g, ∫ g₀, F (g₀, g) ∂ν 0 ∂Measure.pi ν') ≤
              ∫ g, B * ‖WithLp.toLp 2 (T *ᵥ khatriRaoProbe g)‖ ^ (2 * p) ∂Measure.pi ν' :=
            integral_mono hFi.integral_prod_right (hnorm.1.const_mul B)
              (fun g => (hfactor g).2)
          _ = B * ∫ g, ‖WithLp.toLp 2 (T *ᵥ khatriRaoProbe g)‖ ^ (2 * p) ∂Measure.pi ν' :=
            integral_const_mul _ _
          _ ≤ B * (B ^ d * frobSq T ^ p) := mul_le_mul_of_nonneg_left hnorm.2 hB
          _ = B ^ (d + 1) * ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
            have hT : frobSq T = ‖WithLp.toLp 2 a‖ ^ 2 := by
              rw [frobSq_eq_sum_sq, norm_toLp_sq_eq_dotProduct_self]
              simpa only [T, dotProduct, ← pow_two] using sum_norm_sq_tensor_slices a
            rw [hT, pow_mul, pow_succ]
            ring
      let e : ((Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ)) ≃ᵐ
          (∀ j : Fin (d + 1), Fin (n j) → ℝ) :=
        { Fin.consEquiv (fun j => Fin (n j) → ℝ) with
          measurable_toFun := by
            apply measurable_pi_iff.2
            intro i
            refine Fin.cases ?_ (fun j => ?_) i
            · simpa only [Fin.consEquiv_apply, Fin.cons_zero] using
                (measurable_fst : Measurable (fun g :
                  (Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ) => g.1))
            · simpa only [Fin.consEquiv_apply, Fin.cons_succ, Function.comp_def] using
                (measurable_pi_apply j).comp measurable_snd
          measurable_invFun := by
            change Measurable (fun g : ∀ j : Fin (d + 1), Fin (n j) → ℝ =>
              (g 0, fun j : Fin d => g j.succ))
            exact (measurable_pi_apply 0).prodMk
              (measurable_pi_iff.2 fun j => measurable_pi_apply j.succ) }
      have he : MeasurePreserving e ((ν 0).prod (Measure.pi ν')) (Measure.pi ν) := by
        refine ⟨e.measurable, (Measure.pi_eq fun s _ => ?_).symm⟩
        rw [e.map_apply, Fin.prod_univ_succ, ← Measure.pi_pi, ← Measure.prod_prod]
        congr 1 with ⟨x, f⟩
        simp [e, Fin.forall_fin_succ]
      have hpoint : (fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) ∘
          (fun g : (Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ) =>
            Fin.cons g.1 g.2) = F := by
        funext g
        rw [Function.comp_apply, dotProduct_khatriRaoProbe_cons]
        rfl
      refine ⟨?_, ?_⟩
      · have hc : Integrable ((fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) ∘
            (fun g : (Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ) =>
              Fin.cons g.1 g.2)) ((ν 0).prod (Measure.pi ν')) := by
          rw [hpoint]
          exact hFi
        exact (he.integrable_comp (show Measurable
            (fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) from by
          unfold khatriRaoProbe dotProduct
          fun_prop).aestronglyMeasurable).1 hc
      · rw [← he.integral_comp']
        change (∫ g, ((fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) ∘
          (fun g : (Fin (n 0) → ℝ) × (∀ j : Fin d, Fin (n j.succ) → ℝ) =>
            Fin.cons g.1 g.2)) g ∂(ν 0).prod (Measure.pi ν')) ≤ _
        rw [hpoint]
        exact hFb

/-- Independent isotropic-scale sub-Gaussian vector factors have directional
tensor moments with factorial growth. Only the directional square-exponential
bound is needed here; neither centered factors nor coordinate independence is
assumed. Source: Heidary, Lemma 2.2, with the unoptimized scalar budget
`2 p! K^(2p)` in place of the isotropy-anchored improvement. -/
theorem integrable_and_integral_pow_two_mul_dotProduct_khatriRaoProbe_le_of_exp_sq
    {d : ℕ} {n : Fin d → ℕ}
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ j (u : Fin (n j) → ℝ), ‖WithLp.toLp 2 u‖ = 1 →
      ∫⁻ g, ENNReal.ofReal (Real.exp ((u ⬝ᵥ g / K) ^ 2)) ∂ν j ≤ 2)
    {p : ℕ} (hp : 0 < p) (a : (∀ j : Fin d, Fin (n j)) → ℝ) :
    Integrable (fun g => (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p)) (Measure.pi ν) ∧
      (∫ g, (a ⬝ᵥ khatriRaoProbe g) ^ (2 * p) ∂Measure.pi ν) ≤
        (2 * (p.factorial : ℝ) * K ^ (2 * p)) ^ d *
          ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
  exact integrable_and_integral_pow_two_mul_dotProduct_khatriRaoProbe_le ν hp (by positivity)
    (fun j a => integrable_and_integral_pow_two_mul_dotProduct_le_of_directional_exp_sq
      (ν j) hK (hpsi j) p a) a

/-- Restricting independent square-exponentially bounded tensor factors to
an orthonormal subspace keeps the same homogeneous directional moment
budget. Source: Heidary, Lemma 2.2, applied to the projected probe. -/
theorem integrable_and_integral_pow_two_mul_dotProduct_projected_khatriRaoProbe_le
    {d : ℕ} {n : Fin d → ℕ}
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)] {K : ℝ} (hK : 0 < K)
    (hpsi : ∀ j (u : Fin (n j) → ℝ), ‖WithLp.toLp 2 u‖ = 1 →
      ∫⁻ g, ENNReal.ofReal (Real.exp ((u ⬝ᵥ g / K) ^ 2)) ∂ν j ≤ 2)
    {r : ℕ} (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) {p : ℕ} (hp : 0 < p) (a : Fin r → ℝ) :
    Integrable (fun g => (a ⬝ᵥ (Uᵀ *ᵥ khatriRaoProbe g)) ^ (2 * p)) (Measure.pi ν) ∧
      (∫ g, (a ⬝ᵥ (Uᵀ *ᵥ khatriRaoProbe g)) ^ (2 * p) ∂Measure.pi ν) ≤
        (2 * (p.factorial : ℝ) * K ^ (2 * p)) ^ d *
          ‖WithLp.toLp 2 a‖ ^ (2 * p) := by
  have h := integrable_and_integral_pow_two_mul_dotProduct_khatriRaoProbe_le_of_exp_sq
    ν hK hpsi hp (U *ᵥ a)
  have hnorm : ‖WithLp.toLp 2 (U *ᵥ a)‖ ^ 2 = ‖WithLp.toLp 2 a‖ ^ 2 := by
    rw [norm_toLp_sq_eq_dotProduct_self, norm_toLp_sq_eq_dotProduct_self]
    simpa only [star_trivial, hU.conjTranspose_mul_self, Matrix.one_mulVec] using
      star_mulVec_dotProduct_mulVec_self U a
  have hnorm' : ‖WithLp.toLp 2 (U *ᵥ a)‖ ^ (2 * p) =
      ‖WithLp.toLp 2 a‖ ^ (2 * p) := by rw [pow_mul, hnorm, ← pow_mul]
  have hpoint (g) : a ⬝ᵥ (Uᵀ *ᵥ khatriRaoProbe g) =
      (U *ᵥ a) ⬝ᵥ khatriRaoProbe g := by
    rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
  simpa only [hpoint, hnorm'] using h

end NLAlib
