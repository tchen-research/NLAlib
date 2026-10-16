import NLAlib.RandomMatrix.Chaos.Flattenings

/-!
# Relabeling chaos modes

An equivalence of mode labels relabels every variance and covariance flattening
by row and column equivalences and preserves the actual multilinear polynomial.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NLAlib

variable {σ τ ι m n 𝕜 : Type*} [Fintype σ] [Fintype τ]
  [DecidableEq σ] [DecidableEq τ]

/-- Relabel the chaos modes while retaining the original coefficient entries. -/
def chaosReindexModes (e : σ ≃ τ) (A : (τ → ι) → Matrix m n 𝕜) :
    (σ → ι) → Matrix m n 𝕜 := fun z => A (fun t => z (e.symm t))

private def subsetModeEquiv (e : σ ≃ τ) (S : Finset σ) :
    S ≃ (S.map e.toEmbedding) :=
  Equiv.subtypeEquiv e (by intro a; simp only [Finset.mem_map_equiv,
    Equiv.symm_apply_apply])

private def complementModeEquiv (e : σ ≃ τ) (S : Finset σ) :
    (Sᶜ : Finset σ) ≃ ((S.map e.toEmbedding)ᶜ : Finset τ) :=
  Equiv.subtypeEquiv e (by intro a; simp only [Finset.mem_compl,
    Finset.mem_map_equiv, Equiv.symm_apply_apply])

variable [Fintype ι] [Fintype m] [Fintype n] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- A mode relabeling is an ordinary row/column relabeling of every variance
flattening. -/
theorem specNorm_chaosFlattening_reindexModes (e : σ ≃ τ)
    (A : (τ → ι) → Matrix m n 𝕜) (S : Finset σ) :
    specNorm (chaosFlattening (chaosReindexModes e A) S) =
      specNorm (chaosFlattening A (S.map e.toEmbedding)) := by
  let er := (subsetModeEquiv e S).symm
  let ec := (complementModeEquiv e S).symm
  let r := (Equiv.arrowCongr er (Equiv.refl ι)).prodCongr (Equiv.refl m)
  let c := (Equiv.arrowCongr ec (Equiv.refl ι)).prodCongr (Equiv.refl n)
  have he : (chaosFlattening A (S.map e.toEmbedding)).reindex r c =
      chaosFlattening (chaosReindexModes e A) S := by
    ext a b
    change A (chaosAssemble (S.map e.toEmbedding) (r.symm a).1 (c.symm b).1) a.2 b.2 =
      A (fun t => chaosAssemble S a.1 b.1 (e.symm t)) a.2 b.2
    congr 2
    funext t
    by_cases ht : e.symm t ∈ S
    · simp [r, c, er, ec, Equiv.arrowCongr, subsetModeEquiv, complementModeEquiv,
        chaosAssemble, Finset.mem_map_equiv, ht, Finset.equivMap]
    · simp [r, c, er, ec, Equiv.arrowCongr, complementModeEquiv,
        chaosAssemble, Finset.mem_map_equiv, ht, Finset.equivMap]
  rw [← he, specNorm_reindex]

/-- Covariance flattenings are likewise unchanged by mode relabeling. -/
theorem specNorm_chaosCovarianceFlattening_reindexModes (e : σ ≃ τ)
    (A : (τ → ι) → Matrix m n 𝕜) (S : Finset σ) :
    specNorm (chaosCovarianceFlattening (chaosReindexModes e A) S) =
      specNorm (chaosCovarianceFlattening A (S.map e.toEmbedding)) := by
  let er := (subsetModeEquiv e S).symm
  let ec := (complementModeEquiv e S).symm
  let r := Equiv.arrowCongr er (Equiv.refl ι)
  let c := (Equiv.arrowCongr ec (Equiv.refl ι)).prodCongr (Equiv.refl (m × n))
  have he : (chaosCovarianceFlattening A (S.map e.toEmbedding)).reindex r c =
      chaosCovarianceFlattening (chaosReindexModes e A) S := by
    ext a b
    change A (chaosAssemble (S.map e.toEmbedding) (r.symm a) (c.symm b).1) b.2.1 b.2.2 =
      A (fun t => chaosAssemble S a b.1 (e.symm t)) b.2.1 b.2.2
    congr 2
    funext t
    by_cases ht : e.symm t ∈ S
    · simp [r, c, er, ec, Equiv.arrowCongr, subsetModeEquiv, complementModeEquiv,
        chaosAssemble, Finset.mem_map_equiv, ht, Finset.equivMap]
    · simp [r, c, er, ec, Equiv.arrowCongr, complementModeEquiv,
        chaosAssemble, Finset.mem_map_equiv, ht, Finset.equivMap]
  rw [← he, specNorm_reindex]

/-- The variance parameter is unchanged by relabeling the chaos modes. -/
theorem chaosSigma_reindexModes (e : σ ≃ τ) (A : (τ → ι) → Matrix m n 𝕜) :
    chaosSigma (chaosReindexModes e A) = chaosSigma A := by
  apply le_antisymm
  · apply chaosSigma_le
    intro S
    rw [specNorm_chaosFlattening_reindexModes]
    exact specNorm_chaosFlattening_le _ _
  · apply chaosSigma_le
    intro T
    have h := specNorm_chaosFlattening_le (chaosReindexModes e A) (T.map e.symm.toEmbedding)
    rw [specNorm_chaosFlattening_reindexModes] at h
    have hT : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
      ext t
      simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [hT] at h
    exact h

/-- The covariance parameter is unchanged by relabeling the chaos modes. -/
theorem chaosCovariance_reindexModes (e : σ ≃ τ) (A : (τ → ι) → Matrix m n 𝕜) :
    chaosCovariance (chaosReindexModes e A) = chaosCovariance A := by
  apply le_antisymm
  · apply chaosCovariance_le _ (chaosCovariance_nonneg _)
    intro S hS
    rw [specNorm_chaosCovarianceFlattening_reindexModes]
    exact specNorm_chaosCovarianceFlattening_le _ _ hS.map
  · apply chaosCovariance_le _ (chaosCovariance_nonneg _)
    intro T hT
    have h := specNorm_chaosCovarianceFlattening_le (chaosReindexModes e A)
      (T.map e.symm.toEmbedding) hT.map
    rw [specNorm_chaosCovarianceFlattening_reindexModes] at h
    have heT : (T.map e.symm.toEmbedding).map e.toEmbedding = T := by
      ext t
      simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]
    rw [heT] at h
    exact h

/-- Relabeling coefficient modes and coordinate groups together leaves the
actual decoupled multilinear polynomial unchanged. -/
theorem decoupledMatrixChaos_reindexModes (e : σ ≃ τ)
    (A : (τ → ι) → Matrix m n 𝕜) (h : τ → ι → ℝ) :
    decoupledMatrixChaos (chaosReindexModes e A) (fun t => h (e t)) =
      decoupledMatrixChaos A h := by
  let ez := Equiv.arrowCongr e (Equiv.refl ι)
  unfold decoupledMatrixChaos
  rw [← ez.sum_comp (fun z : τ → ι => (∏ t, h t (z t)) • A z)]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  simpa [ez, Equiv.arrowCongr] using
    e.prod_comp (fun t => h t (z (e.symm t)))

end NLAlib
