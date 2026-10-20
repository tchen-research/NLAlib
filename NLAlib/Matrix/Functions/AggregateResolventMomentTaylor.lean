import NLAlib.Matrix.Functions.ResolventMomentTaylor
import NLAlib.Matrix.Functions.CopyDirectionSquareMass
import NLAlib.Matrix.Functions.ResolventNeumannBounds
import Mathlib.Tactic.Module

/-!
# Aggregate actual first-copy Taylor kernels

The literal native third derivative is summed over the family before its
Neumann bound is used. The same three-copy square mass controls every actual
interpolation direction and restoration shift. Unit-square integration keeps
that bound without an extra family or dimension factor.
Source: Brailovskaya--van Handel, arXiv:2201.05142v3, Lemma 6.9.
Supports independent-sum-spectrum-universality (partial).
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped Matrix
namespace NLAlib
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]
local notation "M" => Matrix n n ℂ
local notation "E" => ((n × n) ⊕ (n × n)) → ℝ
local notation "L" => (hermitianMatrixFromRealCoordinates : E →L[ℝ] M)

private theorem sum_double_intervalIntegral_of_continuous
    (f : ι → ℝ → ℝ → ℂ) (hf : ∀ i, Continuous (fun t : ℝ × ℝ => f i t.1 t.2)) :
    (∑ i, ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, f i u v) =
      ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ∑ i, f i u v := by
  have hinner (i : ι) : Continuous (fun u : ℝ => ∫ v in (0 : ℝ)..1, f i u v) := by
    have h := continuous_parametric_integral_of_continuous (μ := volume)
      (f := f i) (hf i) (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    simpa only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Icc_eq_integral_Ioc] using h
  rw [← intervalIntegral.integral_finsetSum (fun i _ => (hinner i).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro u _
  exact (intervalIntegral.integral_finsetSum (fun i _ =>
    ((hf i).comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)).symm

/-- The aggregate genuine first-copy cubic Taylor kernels are controlled by
the common original-base resolvent moment and the realized masses of the
three copies. All parameters on the closed unit interval, zero radius and
empty matrix or summand index types are included. -/
theorem norm_sum_resolventMomentTaylorKernel_first_copy_le
    (A : M) (hA : A.IsHermitian) (ζ : ℂ) (hζ : ζ.im ≠ 0)
    {p : ℕ} (hp : 0 < p) (x₀ : E) (z : Fin 3 → ι → E)
    {R : ℝ} (hR : 0 ≤ R) (hZ : ∀ s i, specNorm (L (z s i)) ≤ R)
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hsmall : 16 * (p : ℝ) * R ≤ |ζ.im|) :
    let mass := 2 * (specNorm (∑ i, L (z 0 i) ^ 2) +
      specNorm (∑ i, L (z 1 i) ^ 2) + specNorm (∑ i, L (z 2 i) ^ 2))
    ‖∑ i, resolventMomentTaylorKernel A ζ p a
      (x₀ - a • (z 0 i - z 1 i)) (z 0 i - z 1 i) (z 1 i - z 2 i)‖ ≤
      ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ) *
        3 * (2 * R) * mass * (|ζ.im|⁻¹) ^ 4 *
          resolventEvenMoment (A + L x₀) ζ p ^
            (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ)) := by
  classical
  let mass := 2 * (specNorm (∑ i, L (z 0 i) ^ 2) +
    specNorm (∑ i, L (z 1 i) ^ 2) + specNorm (∑ i, L (z 2 i) ^ 2))
  let D : ι → E := fun i => z 0 i - z 1 i
  let V : ι → E := fun i => z 1 i - z 2 i
  let X : ι → ℝ → ℝ → E := fun i u v =>
    (x₀ - a • D i) - a • V i + v • (a • (V i + u • D i))
  let Φ : E → ℂ := fun y => normalizedTrace
    (resolvent (A + L y) ζ ^ p * resolvent (A + L y) (star ζ) ^ p)
  let f : ι → ℝ → ℝ → ℂ := fun i u v =>
    iteratedFDeriv ℝ 3 Φ (X i u v) ![V i + u • D i, D i, D i]
  let B : ℝ := 3 * (2 * R) * mass * (|ζ.im|⁻¹) ^ 4 *
    resolventEvenMoment (A + L x₀) ζ p ^
      (((2 * p - 1 : ℕ) : ℝ) / (2 * p : ℕ))
  let T : ℝ := ((2 * p : ℕ) : ℝ) * ((2 * p + 1 : ℕ) : ℝ) *
    ((2 * p + 2 : ℕ) : ℝ) * B
  have hc : ContDiff ℝ 3 Φ := contDiff_normalizedTrace_mixed_resolvent_coordinate A hA ζ hζ p
  have hfc (i : ι) : Continuous (fun t : ℝ × ℝ => f i t.1 t.2) := by
    have hpath : Continuous (fun t : ℝ × ℝ => X i t.1 t.2) := by dsimp only [X]; fun_prop
    have hdirs : Continuous (fun t : ℝ × ℝ => ![V i + t.1 • D i, D i, D i]) := by fun_prop
    exact continuous_eval.comp ((hc.continuous_iteratedFDeriv'.comp hpath).prodMk hdirs)
  have hsum : (∑ i, resolventMomentTaylorKernel A ζ p a
      (x₀ - a • D i) (D i) (V i)) =
        ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, ∑ i, f i u v := by
    exact sum_double_intervalIntegral_of_continuous f hfc
  have hpoint (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
      ‖∑ i, f i u v‖ ≤ T := by
    let Z : Fin 3 → ι → M := fun s i => L (z s i)
    let C : ι → Fin 3 → M := fun i => ![L (V i + u • D i), L (D i), L (D i)]
    let H : ι → M := fun i => a • ((1 - v) • Z 2 i +
      (v * (1 - u)) • Z 1 i + (u * v) • Z 0 i - Z 0 i)
    have hb := norm_and_specNorm_sum_sq_copy_directions_le Z
      (fun s i => isHermitian_hermitianMatrixFromRealCoordinates (z s i)) hR hZ
      hu0 hu1 hv0 hv1 ha0 ha1
    change _ ∧ _ ∧ _ at hb
    rcases hb with ⟨hD, hE, hH⟩
    have hDeq (i : ι) : L (D i) = Z 0 i - Z 1 i := by simp only [D, Z, map_sub]
    have hEeq (i : ι) : L (V i + u • D i) =
        (Z 1 i - Z 2 i) + u • (Z 0 i - Z 1 i) := by
      simp only [V, D, Z, map_add, map_sub, map_smul]
    have hCeq (i : ι) (t : Fin 3) :
        C i t = if t = 0 then (Z 1 i - Z 2 i) + u • (Z 0 i - Z 1 i)
          else Z 0 i - Z 1 i := by
      fin_cases t <;> simp [C, hDeq, hEeq]
    have hHermC (i : ι) (t : Fin 3) : (C i t).IsHermitian := by
      rw [hCeq]
      split_ifs <;> first | exact hE.1 i | exact hD.1 i
    have hBoundC (i : ι) (t : Fin 3) : specNorm (C i t) ≤ 2 * R := by
      rw [hCeq]
      split_ifs <;> first | exact hE.2.1 i | exact hD.2.1 i
    have hMassC (t : Fin 3) : specNorm (∑ i, C i t ^ 2) ≤ mass := by
      simp_rw [hCeq]
      by_cases ht : t = 0
      · simpa only [ht, if_true] using hE.2.2
      · simpa only [ht, if_false] using hD.2.2
    have hpath (i : ι) : A + L (X i u v) = (A + L x₀) + H i := by
      simp only [X, V, D, H, Z, map_sub, map_add, map_smul]
      module
    have hword (i₀ : Fin (p + p)) (i₁ : Fin (p + p + 1))
        (i₂ : Fin (p + p + 2)) :
        ‖∑ i, normalizedTrace (hermitianCoordinateResolventWord A
          (resolventWordInsert (resolventWordInsert
            (resolventWordInsert (mixedResolventWord ζ p) i₀ (L (D i))) i₁ (L (D i)))
              i₂ (L (V i + u • D i))) (X i u v))‖ ≤ B := by
      have hheight : 8 * (p : ℝ) * (2 * R) ≤ |ζ.im| := by nlinarith
      have hh := norm_sum_normalizedTrace_third_resolventWord_add_le hp i₀ i₁ i₂ C H
        hHermC hH.1 (by positivity : 0 ≤ 2 * R) hBoundC hH.2.1 hMassC hH.2.2
        (hA.add (isHermitian_hermitianMatrixFromRealCoordinates x₀)) hζ hheight
      simpa only [C, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, hermitianCoordinateResolventWord,
        List.map_ofFn, Function.comp_def, hermitianCoordinateResolvent, hpath, B] using hh
    have heq : (∑ i, f i u v) =
        ∑ i₀ : Fin (p + p), ∑ i₁ : Fin (p + p + 1), ∑ i₂ : Fin (p + p + 2),
          ∑ i, normalizedTrace (hermitianCoordinateResolventWord A
            (resolventWordInsert (resolventWordInsert
              (resolventWordInsert (mixedResolventWord ζ p) i₀ (L (D i))) i₁ (L (D i)))
                i₂ (L (V i + u • D i))) (X i u v)) := by
      simp only [f, Φ, iteratedFDeriv_three_normalizedTrace_mixed_resolvent_coordinate_apply
        A hA ζ hζ p, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i₀ _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i₁ _
      rw [Finset.sum_comm]
    rw [heq]
    calc
      _ ≤ ∑ i₀ : Fin (p + p), ‖∑ i₁ : Fin (p + p + 1),
          ∑ i₂ : Fin (p + p + 2), ∑ i, normalizedTrace (hermitianCoordinateResolventWord A
            (resolventWordInsert (resolventWordInsert
              (resolventWordInsert (mixedResolventWord ζ p) i₀ (L (D i))) i₁ (L (D i)))
                i₂ (L (V i + u • D i))) (X i u v))‖ := norm_sum_le _ _
      _ ≤ ∑ i₀ : Fin (p + p), ∑ i₁ : Fin (p + p + 1), ∑ i₂ : Fin (p + p + 2), B := by
        apply Finset.sum_le_sum
        intro i₀ _
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i₁ _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i₂ _ => hword i₀ i₁ i₂))
      _ = T := by simp [T]; ring
  rw [hsum]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun u => ∫ v in (0 : ℝ)..1, ∑ i, f i u v)
    (C := T) (fun u hu => by
    have hu' : u ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
    have hn' := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (f := fun v => ∑ i, f i u v) (C := T) (fun v hv => by
      have hv' : v ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hv
      exact hpoint u v hu'.1.le hu'.2 hv'.1.le hv'.2)
    simpa only [sub_zero, abs_one, mul_one] using hn')
  simpa only [sub_zero, abs_one, mul_one, T, B, D, V, mass, mul_assoc] using hn

end NLAlib
