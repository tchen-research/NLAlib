import NLAlib.Matrix.Stiefel
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual invariant probability law on Stiefel frames

Normalized Haar measure on the compact orthogonal group defines the frame law.
Transitivity, right invariance and Tonelli prove its uniqueness among invariant
Borel probabilities. Source: operator re-derivation `sh:haar-unique`.
Supports atlas `haar-orthogonal`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Measure TopologicalSpace
open scoped ENNReal Matrix Matrix.Norms.L2Operator
namespace NLAlib

/-- Normalized Haar measure on the actual compact real orthogonal group.
Source: operator re-derivation `sh:haar`, normalizing on the whole compact group. -/
def orthogonalHaar (n : ℕ) : Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  haarMeasure (⊤ : PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ))

/-- The whole-group normalization makes the orthogonal Haar law a probability.
Source: operator re-derivation `sh:haar`. -/
instance orthogonalHaar_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (orthogonalHaar n) :=
  ⟨by simpa only [orthogonalHaar, PositiveCompacts.coe_top] using
    (haarMeasure_self (K₀ := (⊤ : PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ))))⟩

/-- The normalized orthogonal law is Haar measure.
Source: Mathlib Haar construction; operator re-derivation `sh:haar`. -/
instance orthogonalHaar_isHaarMeasure (n : ℕ) : IsHaarMeasure (orthogonalHaar n) := by
  unfold orthogonalHaar
  infer_instance

/-- Normalized compact Haar probability is also right invariant.
Source: operator re-derivation `sh:haar-unique`, Haar uniqueness applied to a
right translate of the actual Haar law. -/
instance orthogonalHaar_isMulRightInvariant (n : ℕ) : IsMulRightInvariant (orthogonalHaar n) where
  map_mul_right_eq_self V := by
    have : IsProbabilityMeasure ((orthogonalHaar n).map (fun O => O * V)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The invariant frame probability is the Haar image of the coordinate frame.
Source: operator re-derivation `sh:haar`. -/
def haarFrameLaw (n k : ℕ) (hkn : k ≤ n) : Measure (Stiefel n k) :=
  (orthogonalHaar n).map (fun O => O • coordinateStiefel n k hkn)

/-- The Haar frame law is a probability measure.
Source: operator re-derivation `sh:haar`. -/
instance haarFrameLaw_isProbabilityMeasure (n k : ℕ) (hkn : k ≤ n) :
    IsProbabilityMeasure (haarFrameLaw n k hkn) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

/-- Orthogonal left action preserves the actual Haar frame law.
Source: operator re-derivation `sh:haar-unique`. -/
theorem haarFrameLaw_map_smul {n k : ℕ} (hkn : k ≤ n)
    (V : Matrix.orthogonalGroup (Fin n) ℝ) :
    (haarFrameLaw n k hkn).map (fun Q => V • Q) = haarFrameLaw n k hkn := by
  unfold haarFrameLaw
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  have heq : (fun Q : Stiefel n k => V • Q) ∘
      (fun O => O • coordinateStiefel n k hkn) =
      (fun O => O • coordinateStiefel n k hkn) ∘ (fun O => V * O) := by
    funext O
    exact (mul_smul V O _).symm
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), map_mul_left_eq_self]

/-- Haar's frame pushforward is independent of the chosen starting frame.
Source: operator re-derivation `sh:haar-unique`, transitivity and right invariance. -/
theorem orthogonalHaar_map_smul_eq_haarFrameLaw {n k : ℕ} (hkn : k ≤ n)
    (Q : Stiefel n k) :
    (orthogonalHaar n).map (fun O => O • Q) = haarFrameLaw n k hkn := by
  obtain ⟨V, hV⟩ := exists_orthogonalGroup_smul_eq hkn (coordinateStiefel n k hkn) Q
  rw [← hV]
  have heq : (fun O => O • V • coordinateStiefel n k hkn) =
      (fun O => O • coordinateStiefel n k hkn) ∘ (fun O => O * V) := by
    funext O
    exact (mul_smul O V _).symm
  rw [heq, ← Measure.map_map (by fun_prop) (by fun_prop), map_mul_right_eq_self]
  rfl

/-- The actual Haar frame law is the unique orthogonally invariant Borel
probability on Stiefel space. Source: operator re-derivation `sh:haar-unique`;
the proof is the direct Haar/Tonelli argument, with no uniqueness premise for
the Stiefel manifold. -/
theorem measure_eq_haarFrameLaw_of_invariant {n k : ℕ} (hkn : k ≤ n)
    (ν : Measure (Stiefel n k)) [IsProbabilityMeasure ν]
    (hinv : ∀ O : Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun Q => O • Q) = ν) :
    ν = haarFrameLaw n k hkn := by
  apply Measure.ext
  intro s hs
  let f : Stiefel n k → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hs
  have hinner : ∀ O : Matrix.orthogonalGroup (Fin n) ℝ,
      (∫⁻ Q, f (O • Q) ∂ν) = ν s := by
    intro O
    have hh := lintegral_map (μ := ν) hf
      (show Measurable (fun Q : Stiefel n k => O • Q) from by fun_prop)
    rw [hinv O] at hh
    simpa only [f, lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ,
      one_mul] using hh.symm
  have horbit : ∀ Q : Stiefel n k,
      (∫⁻ O, f (O • Q) ∂orthogonalHaar n) = haarFrameLaw n k hkn s := by
    intro Q
    have hh := lintegral_map (μ := orthogonalHaar n) hf (show Measurable
      (fun O : Matrix.orthogonalGroup (Fin n) ℝ => O • Q) from by fun_prop)
    rw [orthogonalHaar_map_smul_eq_haarFrameLaw hkn Q] at hh
    simpa only [f, lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ,
      one_mul] using hh.symm
  have hmeas : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × Stiefel n k =>
      f (p.1 • p.2)) := hf.comp (by fun_prop)
  calc
    ν s = ∫⁻ O : Matrix.orthogonalGroup (Fin n) ℝ, ∫⁻ Q, f (O • Q) ∂ν
        ∂orthogonalHaar n := by simp only [hinner, lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ Q, ∫⁻ O : Matrix.orthogonalGroup (Fin n) ℝ, f (O • Q) ∂orthogonalHaar n
        ∂ν := lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by simp only [horbit, lintegral_const, measure_univ, mul_one]

end NLAlib
