import NLAlib.Matrix.Subspaces.UnitaryStiefel
import NLAlib.RandomMatrix.Haar.HaarFrameMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Actual unitary Haar and rectangular Stiefel probability laws

Normalized Haar measure on the actual compact unitary group defines the complex
frame law as well as its existing real orthogonal specialization. Transitivity
and Tonelli prove uniqueness from invariance; no matrix-Beta law is assumed.
-/

noncomputable section
open MeasureTheory Measure TopologicalSpace
open scoped ENNReal Matrix
namespace NLAlib
variable (𝕜 : Type*) [RCLike 𝕜]

/-- Normalized Haar probability on the actual unitary group. -/
def unitaryHaar (n : ℕ) : Measure (Matrix.unitaryGroup (Fin n) 𝕜) :=
  haarMeasure (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n) 𝕜))

/-- Whole-group Haar normalization is probability normalization. -/
instance unitaryHaar_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (unitaryHaar 𝕜 n) :=
  ⟨by simpa only [unitaryHaar,PositiveCompacts.coe_top] using
    (haarMeasure_self (K₀ := (⊤ : PositiveCompacts (Matrix.unitaryGroup (Fin n) 𝕜))))⟩

/-- The actual normalized unitary probability is Haar measure. -/
instance unitaryHaar_isHaarMeasure (n : ℕ) : IsHaarMeasure (unitaryHaar 𝕜 n) := by
  unfold unitaryHaar
  infer_instance

/-- Compact normalized Haar is also right invariant. -/
instance unitaryHaar_isMulRightInvariant (n : ℕ) : IsMulRightInvariant (unitaryHaar 𝕜 n) where
  map_mul_right_eq_self V := by
    have : IsProbabilityMeasure ((unitaryHaar 𝕜 n).map (fun O => O*V)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The actual invariant law of rectangular real or complex orthonormal frames. -/
def unitaryHaarFrameLaw (n k : ℕ) (hkn : k ≤ n) : Measure (UnitaryStiefel 𝕜 n k) :=
  (unitaryHaar 𝕜 n).map (fun O => O • coordinateUnitaryStiefel 𝕜 n k hkn)

/-- The unitary rectangular frame law is a probability. -/
instance unitaryHaarFrameLaw_isProbabilityMeasure (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (unitaryHaarFrameLaw 𝕜 n k hkn) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- The unitary action preserves the actual rectangular frame law. -/
theorem unitaryHaarFrameLaw_map_smul {n k : ℕ} (hkn : k ≤ n)
    (V : Matrix.unitaryGroup (Fin n) 𝕜) :
    (unitaryHaarFrameLaw 𝕜 n k hkn).map (fun Q => V • Q) = unitaryHaarFrameLaw 𝕜 n k hkn := by
  unfold unitaryHaarFrameLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : (fun Q : UnitaryStiefel 𝕜 n k => V • Q) ∘
      (fun O => O • coordinateUnitaryStiefel 𝕜 n k hkn) =
      (fun O => O • coordinateUnitaryStiefel 𝕜 n k hkn) ∘ (fun O => V*O) := by
    funext O
    exact (mul_smul V O _).symm
  rw [heq,← Measure.map_map (by fun_prop) (by fun_prop),map_mul_left_eq_self]

/-- The Haar image does not depend on the chosen initial orthonormal frame. -/
theorem unitaryHaar_map_smul_eq_frameLaw {n k : ℕ} (hkn : k ≤ n)
    (Q : UnitaryStiefel 𝕜 n k) :
    (unitaryHaar 𝕜 n).map (fun O => O • Q) = unitaryHaarFrameLaw 𝕜 n k hkn := by
  obtain ⟨V,hV⟩ := exists_unitaryGroup_smul_eq 𝕜 hkn (coordinateUnitaryStiefel 𝕜 n k hkn) Q
  rw [← hV]
  have heq : (fun O => O • V • coordinateUnitaryStiefel 𝕜 n k hkn) =
      (fun O => O • coordinateUnitaryStiefel 𝕜 n k hkn) ∘ (fun O => O*V) := by
    funext O
    exact (mul_smul O V _).symm
  rw [heq,← Measure.map_map (by fun_prop) (by fun_prop),map_mul_right_eq_self]
  rfl

/-- Haar/Tonelli uniqueness for the actual real/complex Stiefel probability.
atlas: gaussian-haar-sketch-solve-exact (partial) -/
theorem measure_eq_unitaryHaarFrameLaw_of_invariant {n k : ℕ} (hkn : k ≤ n)
    (ν : Measure (UnitaryStiefel 𝕜 n k)) [IsProbabilityMeasure ν]
    (hinv : ∀ O : Matrix.unitaryGroup (Fin n) 𝕜, ν.map (fun Q => O • Q) = ν) :
    ν = unitaryHaarFrameLaw 𝕜 n k hkn := by
  apply Measure.ext
  intro s hs
  let f : UnitaryStiefel 𝕜 n k → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hinner : ∀ O : Matrix.unitaryGroup (Fin n) 𝕜,
      (∫⁻ Q, f (O • Q) ∂ν) = ν s := by
    intro O
    have hh := lintegral_map (μ := ν) hf
      (show Measurable (fun Q : UnitaryStiefel 𝕜 n k => O • Q) from by fun_prop)
    rw [hinv O] at hh
    simpa only [f,lintegral_indicator hs,lintegral_const,Measure.restrict_apply_univ,one_mul] using hh.symm
  have horbit : ∀ Q : UnitaryStiefel 𝕜 n k,
      (∫⁻ O, f (O • Q) ∂unitaryHaar 𝕜 n) = unitaryHaarFrameLaw 𝕜 n k hkn s := by
    intro Q
    have hh := lintegral_map (μ := unitaryHaar 𝕜 n) hf (show Measurable
      (fun O : Matrix.unitaryGroup (Fin n) 𝕜 => O • Q) from by fun_prop)
    rw [unitaryHaar_map_smul_eq_frameLaw 𝕜 hkn Q] at hh
    simpa only [f,lintegral_indicator hs,lintegral_const,Measure.restrict_apply_univ,one_mul] using hh.symm
  have hact : Measurable (fun p : Matrix.unitaryGroup (Fin n) 𝕜 × UnitaryStiefel 𝕜 n k =>
      p.1 • p.2) := by
    apply Measurable.subtype_mk
    change Measurable (fun p : Matrix.unitaryGroup (Fin n) 𝕜 × UnitaryStiefel 𝕜 n k =>
      p.1.val*p.2.val)
    exact (measurable_subtype_coe.comp measurable_fst).matrix_mul
      (measurable_subtype_coe.comp measurable_snd)
  have hmeas : Measurable (fun p : Matrix.unitaryGroup (Fin n) 𝕜 × UnitaryStiefel 𝕜 n k =>
      f (p.1 • p.2)) := hf.comp hact
  calc
    ν s = ∫⁻ O : Matrix.unitaryGroup (Fin n) 𝕜, ∫⁻ Q, f (O • Q) ∂ν
        ∂unitaryHaar 𝕜 n := by simp only [hinner,lintegral_const,measure_univ,mul_one]
    _ = ∫⁻ Q, ∫⁻ O : Matrix.unitaryGroup (Fin n) 𝕜, f (O • Q) ∂unitaryHaar 𝕜 n
        ∂ν := lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by simp only [horbit,lintegral_const,measure_univ,mul_one]

/-- The real unitary Haar law is exactly the existing real orthogonal law. -/
theorem unitaryHaar_real_eq_orthogonalHaar (n : ℕ) : unitaryHaar ℝ n = orthogonalHaar n := rfl

/-- The generic real frame specialization agrees with the existing Stiefel law. -/
theorem unitaryHaarFrameLaw_real_eq_haarFrameLaw (n k : ℕ) (hkn : k ≤ n) :
    unitaryHaarFrameLaw ℝ n k hkn = haarFrameLaw n k hkn := rfl

end NLAlib
