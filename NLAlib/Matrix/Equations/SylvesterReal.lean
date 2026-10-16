import NLAlib.Matrix.Equations.SylvesterNormal

/-! # Real Sylvester separation and the actual complexified spectra -/
noncomputable section
open scoped Matrix Kronecker
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [Fintype m] [Fintype n] in
/-- The actual Kronecker operator commutes with real scalar extension. -/
theorem sylvesterKronecker_map_ofReal (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    sylvesterKronecker (A.map Complex.ofReal) (B.map Complex.ofReal) =
      (sylvesterKronecker A B).map Complex.ofReal := by
  ext ⟨j,i⟩ ⟨l,k⟩
  by_cases hj : j = l <;> by_cases hi : i = k <;>
    simp [sylvesterKronecker, Matrix.kroneckerMap_apply, hj, hi]

/-- Real and complexified Frobenius separations coincide exactly. -/
theorem sylvesterSep_map_ofReal (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    sylvesterSep (A.map Complex.ofReal) (B.map Complex.ofReal) = sylvesterSep A B := by
  unfold sylvesterSep
  rw [sylvesterKronecker_map_ofReal]
  exact singularValues_map_ofReal (𝕜 := ℂ) (sylvesterKronecker A B) _

/-- A real Sylvester operator has positive sharp separation exactly when its
two complexified spectra are disjoint. Source: user derivations, Sylvester
operator separation.
atlas: sylvester-separation-residual-conditioning (partial) -/
theorem sylvesterSep_pos_iff_disjoint_complex_spectrum [Nonempty m] [Nonempty n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) :
    0 < sylvesterSep A B ↔ Disjoint (spectrum ℂ (A.map Complex.ofReal)) (spectrum ℂ (B.map Complex.ofReal)) := by
  rw [← sylvesterSep_map_ofReal, sylvesterSep_pos_iff_disjoint_spectrum]

/-- The normal spectral-distance formula applies to real normal coefficients
through their actual complexified spectra. -/
theorem isLeast_real_sylvesterSep_spectral_distances_of_normal [Nonempty m] [Nonempty n]
    (A : Matrix m m ℝ) (B : Matrix n n ℝ) (hA : A * Aᴴ = Aᴴ * A) (hB : B * Bᴴ = Bᴴ * B) :
    IsLeast {c : ℝ | ∃ a ∈ spectrum ℂ (A.map Complex.ofReal),
      ∃ b ∈ spectrum ℂ (B.map Complex.ofReal), ‖a-b‖ = c} (sylvesterSep A B) := by
  have hAC : A.map Complex.ofReal * (A.map Complex.ofReal)ᴴ =
      (A.map Complex.ofReal)ᴴ * A.map Complex.ofReal := by
    have h := congrArg (Complex.ofRealHom.mapMatrix) hA
    simp only [map_mul] at h
    have hstar : (A.map Complex.ofReal)ᴴ = Aᴴ.map Complex.ofReal := by
      ext i j
      simp
    change A.map Complex.ofReal * Aᴴ.map Complex.ofReal = Aᴴ.map Complex.ofReal * A.map Complex.ofReal at h
    rwa [← hstar] at h
  have hBC : B.map Complex.ofReal * (B.map Complex.ofReal)ᴴ =
      (B.map Complex.ofReal)ᴴ * B.map Complex.ofReal := by
    have h := congrArg (Complex.ofRealHom.mapMatrix) hB
    simp only [map_mul] at h
    have hstar : (B.map Complex.ofReal)ᴴ = Bᴴ.map Complex.ofReal := by
      ext i j
      simp
    change B.map Complex.ofReal * Bᴴ.map Complex.ofReal = Bᴴ.map Complex.ofReal * B.map Complex.ofReal at h
    rwa [← hstar] at h
  have h := isLeast_sylvesterSep_spectral_distances_of_normal _ _ hAC hBC
  rw [sylvesterSep_map_ofReal] at h
  exact h

end NLAlib
