import NLAlib.Matrix.Perturbation.Pseudospectrum
/-!
# Resolvent and normal-matrix pseudospectral formulas

The positive-radius resolvent formula keeps the eigenvalue disjunct
explicit, so it is unaffected by the total matrix inverse at singular
inputs. For normal matrices the closed pseudospectrum is exactly the
union of closed spectral disks.

Source: Trefethen–Embree (2005), §2; matrix-toolkit re-derivation, §38.
Atlas: `pseudospectrum-perturbation-equivalence`.
-/
noncomputable section
open Matrix
open scoped Matrix
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The inverse norm of an invertible square matrix is the reciprocal of
its smallest singular value. This uses the full positive thin SVD. -/
theorem specNorm_inv_eq_one_div_singularValues_last [Nonempty n]
    (C : Matrix n n 𝕜) (hC : IsUnit C) :
    specNorm C⁻¹ = 1 / singularValues C (Fintype.card n - 1) := by
  obtain ⟨U, V, h⟩ := exists_isThinSVD C
  have hr : C.rank = Fintype.card n := Matrix.rank_of_isUnit C hC
  have hpos : 0 < C.rank := by rw [hr]; exact Fintype.card_pos
  have hn := h.isSingularTripletFamily.specNorm_truncatedSingularInverse hpos
  unfold truncatedSingularInverse at hn
  rw [← h.moorePenroseInverse_eq, moorePenroseInverse_eq_inv_of_isUnit C hC, hr] at hn
  exact hn

/-- The closed positive-radius pseudospectrum has the usual resolvent norm
description, with eigenvalues explicitly included. The total inverse's
singular junk value never decides membership.
atlas: pseudospectrum-perturbation-equivalence (partial) -/
theorem singularValues_last_shift_le_iff_spectrum_or_resolvent [Nonempty n]
    (A : Matrix n n ℂ) (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    singularValues (z • 1 - A) (Fintype.card n - 1) ≤ ε ↔
      z ∈ spectrum ℂ A ∨ 1 / ε ≤ specNorm (z • 1 - A)⁻¹ := by
  by_cases hz : z ∈ spectrum ℂ A
  · have hn : ¬ IsUnit (z • (1 : Matrix n n ℂ) - A) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.mem_iff.mp hz
    have hs : singularValues (z • 1 - A) (Fintype.card n - 1) = 0 := by
      have hnp : ¬ 0 < singularValues (z • 1 - A) (Fintype.card n - 1) :=
        fun hpos => hn ((singularValues_last_pos_iff_isUnit _).mp hpos)
      exact le_antisymm (le_of_not_gt hnp) (singularValues_nonneg _ _)
    simp [hz, hs, hε.le]
  · have hu : IsUnit (z • (1 : Matrix n n ℂ) - A) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hz
    have hs := (singularValues_last_pos_iff_isUnit _).mpr hu
    rw [or_iff_right hz, specNorm_inv_eq_one_div_singularValues_last _ hu,
      one_div_le_one_div hε hs]

open scoped Matrix.Norms.L2Operator in
/-- For a normal matrix, the closed pseudospectrum is the union of the
closed radius-ε disks around its complex spectrum. Zero radius is included.
atlas: pseudospectrum-perturbation-equivalence (partial) -/
theorem exists_perturbation_mem_spectrum_iff_exists_spectral_distance_le_of_normal
    (A : Matrix n n ℂ) (hA : A * Aᴴ = Aᴴ * A) (z : ℂ) (ε : ℝ) :
    (∃ E : Matrix n n ℂ, specNorm E ≤ ε ∧ z ∈ spectrum ℂ (A + E)) ↔
      ∃ μ ∈ spectrum ℂ A, ‖z - μ‖ ≤ ε := by
  constructor
  · rintro ⟨E, hE, hz⟩
    obtain ⟨μ, hμ, hdist⟩ := exists_mem_spectrum_distance_le_norm_perturbation_of_normal hA hz
    refine ⟨μ, hμ, ?_⟩
    calc
      ‖z - μ‖ = ‖μ - z‖ := norm_sub_rev _ _
      _ ≤ specNorm E := hdist
      _ ≤ ε := hE
  · rintro ⟨μ, hμ, hdist⟩
    let E : Matrix n n ℂ := (z - μ) • 1
    have hbound : specNorm E ≤ ε := by
      change ‖(z - μ) • (1 : Matrix n n ℂ)‖ ≤ ε
      rw [norm_smul]
      calc
        _ ≤ ‖z - μ‖ * 1 :=
          mul_le_mul_of_nonneg_left specNorm_one_le (norm_nonneg _)
        _ ≤ ε := by simpa using hdist
    obtain ⟨v, hv, he⟩ := exists_mulVec_eq_smul_of_mem_spectrum hμ
    have heig : (A + E) *ᵥ v = z • v := by
      rw [Matrix.add_mulVec, he]
      change μ • v + ((z - μ) • (1 : Matrix n n ℂ)) *ᵥ v = z • v
      rw [Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
      abel
    exact ⟨E, hbound, Matrix.mem_spectrum_of_isRoot_charpoly
      (isRoot_charpoly_of_mulVec_eq_smul hv heig)⟩

end NLAlib
