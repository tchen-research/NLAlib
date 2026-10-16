import NLAlib.RandomMatrix.Chaos.Flattenings

/-!
# The deterministic degree-zero endpoint

There is exactly one empty tuple. Its polynomial and variance parameter are the
original deterministic matrix and its spectral norm; the covariance parameter
is zero. This endpoint is used only for the chaos inductions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NLAlib

variable {τ ι m n 𝕜 : Type*} [Fintype τ] [IsEmpty τ] [DecidableEq τ]
  [Fintype ι] [DecidableEq ι] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- Every zero-degree variance flattening is just the deterministic matrix up
to its unique empty-coordinate row and column factors. -/
theorem specNorm_chaosFlattening_of_isEmpty
    (A : (τ → ι) → Matrix m n 𝕜) (S : Finset τ) :
    specNorm (chaosFlattening A S) = specNorm (A default) := by
  let e := Equiv.uniqueProd m (S → ι)
  let f := Equiv.uniqueProd n (((Sᶜ : Finset τ)) → ι)
  have he : (chaosFlattening A S).reindex e f = A default := by
    ext a b
    change A (chaosAssemble S (e.symm a).1 (f.symm b).1) a b = A default a b
    congr 2
    exact Subsingleton.elim _ _
  rw [← he, specNorm_reindex]

/-- At degree zero the variance parameter is the deterministic spectral norm. -/
theorem chaosSigma_of_isEmpty (A : (τ → ι) → Matrix m n 𝕜) :
    chaosSigma A = specNorm (A default) := by
  apply le_antisymm
  · exact chaosSigma_le _ (fun S => (specNorm_chaosFlattening_of_isEmpty A S).le)
  · rw [← specNorm_chaosFlattening_of_isEmpty A ∅]
    exact specNorm_chaosFlattening_le _ _

/-- There is no nonempty covariance row subset at degree zero. -/
theorem chaosCovariance_of_isEmpty (A : (τ → ι) → Matrix m n 𝕜) :
    chaosCovariance A = 0 := by
  apply le_antisymm
  · apply chaosCovariance_le _ le_rfl
    intro S hS
    obtain ⟨t, _⟩ := hS
    exact isEmptyElim t
  · exact chaosCovariance_nonneg _

/-- A degree-zero chaos is exactly its unique deterministic coefficient. -/
theorem decoupledMatrixChaos_of_isEmpty
    (A : (τ → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    decoupledMatrixChaos A h = A default := by
  simp [decoupledMatrixChaos]

end NLAlib
