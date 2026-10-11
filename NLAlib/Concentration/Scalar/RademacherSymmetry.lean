import NLAlib.Concentration.Scalar.Rademacher
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Symmetry and support of the finite Rademacher cube

The actual product of the two-atom scalar Rademacher laws is invariant under
each individual sign flip. Polynomial-growth functions are integrable because
the whole finite coefficient vector has norm at most one almost everywhere.
Source: operator manuscript, sign-flip branch of `noncommutative-khintchine`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
namespace NLAlib

/-- The scalar Rademacher law is supported on precisely the two signs.
Source: its two-Dirac definition; supports `noncommutative-khintchine`. -/
theorem ae_eq_one_or_neg_one_rademacherMeasure :
    ∀ᵐ x ∂rademacherMeasure, x = 1 ∨ x = -1 := by
  rw [rademacherMeasure, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure
      ((ae_dirac_iff ((measurableSet_singleton 1).union (measurableSet_singleton (-1 : ℝ)))).2
        (Or.inl rfl)) _
  · exact Measure.ae_smul_measure
      ((ae_dirac_iff ((measurableSet_singleton 1).union (measurableSet_singleton (-1 : ℝ)))).2
        (Or.inr rfl)) _

/-- Negation preserves the exact two-atom Rademacher measure.
Source: interchange of its two atoms; supports `noncommutative-khintchine`. -/
theorem measurePreserving_neg_rademacherMeasure :
    MeasurePreserving (fun x : ℝ => -x) rademacherMeasure rademacherMeasure := by
  refine ⟨measurable_neg, ?_⟩
  rw [rademacherMeasure, Measure.map_add _ _ measurable_neg,
    Measure.map_smul, Measure.map_smul]
  simp only [Measure.map_dirac' measurable_neg]
  simp only [neg_neg]
  exact add_comm _ _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- An individual coordinate sign flip preserves the actual finite product
Rademacher law. Source: product invariance in manuscript `eq:recursion`;
supports `noncommutative-khintchine`. -/
theorem measurePreserving_update_neg_pi_rademacherMeasure (i : κ) :
    MeasurePreserving (fun x : κ → ℝ => Function.update x i (-x i))
      (Measure.pi fun _ => rademacherMeasure)
      (Measure.pi fun _ => rademacherMeasure) := by
  let f (j : κ) (t : ℝ) := if j = i then -t else t
  have hf (j : κ) : MeasurePreserving (f j) rademacherMeasure rademacherMeasure := by
    by_cases hji : j = i
    · simpa only [f, hji, if_true] using measurePreserving_neg_rademacherMeasure
    · change MeasurePreserving (fun t => if j = i then -t else t) rademacherMeasure rademacherMeasure
      simp only [hji, if_false]
      exact MeasurePreserving.id rademacherMeasure
  have h := measurePreserving_pi (fun _ : κ => rademacherMeasure)
    (fun _ : κ => rademacherMeasure) hf
  convert h using 1
  funext x j
  by_cases hji : j = i
  · subst j; simp only [Function.update_self, f, if_true]
  · simp only [Function.update_of_ne hji, f, hji, if_false]

/-- Integrals under the finite Rademacher product law are unchanged by an
individual coordinate sign flip. Source: genuine measure preservation;
supports `noncommutative-khintchine`. -/
theorem integral_update_neg_pi_rademacherMeasure
    (i : κ) (f : (κ → ℝ) → ℝ) (hf : Measurable f) :
    (∫ x, f (Function.update x i (-x i)) ∂Measure.pi (fun _ => rademacherMeasure)) =
      ∫ x, f x ∂Measure.pi (fun _ => rademacherMeasure) := by
  have h := measurePreserving_update_neg_pi_rademacherMeasure i
  calc _ = ∫ x, f x ∂(Measure.pi (fun _ : κ => rademacherMeasure)).map
        (fun x => Function.update x i (-x i)) :=
      (integral_map h.measurable.aemeasurable hf.aestronglyMeasurable).symm
    _ = _ := by rw [h.map_eq]

/-- The two-coordinate second moment of the actual product Rademacher law
is the Kronecker delta. Source: individual sign-flip symmetry and the
two-sign support; supports the exact order-one Khintchine identity. -/
theorem integral_coordinate_mul_coordinate_pi_rademacherMeasure (i j : κ) :
    (∫ x : κ → ℝ, x i * x j ∂Measure.pi (fun _ => rademacherMeasure)) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    have hsign : ∀ᵐ x : κ → ℝ ∂Measure.pi (fun _ => rademacherMeasure),
        x i = 1 ∨ x i = -1 :=
      (Measure.tendsto_eval_ae_ae (μ := fun _ : κ => rademacherMeasure) (i := i)).eventually
        ae_eq_one_or_neg_one_rademacherMeasure
    have he : (fun x : κ → ℝ => x i * x i) =ᵐ[Measure.pi (fun _ => rademacherMeasure)]
        fun _ => (1 : ℝ) := hsign.mono fun x hx => by rcases hx with h | h <;> simp [h]
    rw [integral_congr_ae he]
    simp
  · rw [if_neg hij]
    have hflip := integral_update_neg_pi_rademacherMeasure i
      (fun x : κ → ℝ => x i * x j) (by fun_prop)
    simp only [Function.update_self, Function.update_of_ne (Ne.symm hij), neg_mul,
      integral_neg] at hflip
    linarith

omit [DecidableEq κ] in
/-- Almost every vector under the finite product Rademacher law has norm
at most one, including the empty coefficient family. Source: the two-atom
support; supports `noncommutative-khintchine`. -/
theorem ae_norm_le_one_pi_rademacherMeasure :
    ∀ᵐ x : κ → ℝ ∂Measure.pi (fun _ => rademacherMeasure), ‖x‖ ≤ 1 := by
  have hcoord : ∀ j : κ, ∀ᵐ x : κ → ℝ ∂Measure.pi (fun _ => rademacherMeasure),
      x j = 1 ∨ x j = -1 := fun j =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : κ => rademacherMeasure) (i := j)).eventually
      ae_eq_one_or_neg_one_rademacherMeasure
  filter_upwards [Filter.eventually_all.2 hcoord] with x hx
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro j
  rcases hx j with h | h <;> simp [h]

omit [DecidableEq κ] in
/-- Products of two coordinates of the actual product Rademacher law are
absolutely integrable. Source: sign support; supports the exact second-moment
endpoint of `noncommutative-khintchine`. -/
theorem integrable_coordinate_mul_coordinate_pi_rademacherMeasure (i j : κ) :
    Integrable (fun x : κ → ℝ => x i * x j)
      (Measure.pi fun _ => rademacherMeasure) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [ae_norm_le_one_pi_rademacherMeasure (κ := κ)] with x hx
  rw [norm_mul]
  have hi : ‖x i‖ ≤ 1 := (norm_le_pi_norm x i).trans hx
  have hj : ‖x j‖ ≤ 1 := (norm_le_pi_norm x j).trans hx
  simpa only [one_mul] using mul_le_mul hi hj (norm_nonneg _) zero_le_one

omit [DecidableEq κ] in
/-- A measurable polynomial-growth scalar function is integrable under the
actual finite product Rademacher law. Source: bounded sign support;
supports `noncommutative-khintchine`. -/
theorem integrable_pi_rademacherMeasure_of_polynomial_growth
    (f : (κ → ℝ) → ℝ) (hf : Measurable f) (C : ℝ) (d : ℕ)
    (hbound : ∀ x, |f x| ≤ C * (1 + ‖x‖) ^ d) :
    Integrable f (Measure.pi fun _ => rademacherMeasure) := by
  by_cases hC : 0 ≤ C
  · apply (integrable_const (C * 2 ^ d : ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [ae_norm_le_one_pi_rademacherMeasure (κ := κ)] with x hx
    rw [Real.norm_eq_abs]
    calc _ ≤ C * (1 + ‖x‖) ^ d := hbound x
      _ ≤ C * 2 ^ d := by gcongr; linarith
  · have heq : f = 0 := by
      funext x
      have h := hbound x
      have hn : C * (1 + ‖x‖) ^ d < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hC) (by positivity)
      exact False.elim ((not_lt_of_ge (abs_nonneg (f x))) (lt_of_le_of_lt h hn))
    rw [heq]
    exact integrable_zero _ _ _

end NLAlib
