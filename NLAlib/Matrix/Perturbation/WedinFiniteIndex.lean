import NLAlib.Matrix.Perturbation.WedinBounds
import NLAlib.Matrix.Spectral.SingularValueSpectrum
import NLAlib.Matrix.Subspaces.PrincipalAngleInvariance
/-!
# Wedin bounds on arbitrary finite coordinate labels

Transport the complete paired-SVD Wedin theorem to native rectangular matrices.
Leading frames come from the supplied normalized SVDs, so tied singular values
retain the same witness choices. All gap values use the native Euclidean linear
map's singular values, including the full-thin padded-zero endpoint.
Source: Wedin (1972), Section 3; Stewart–Sun, Theorem V.4.4.
-/

noncomputable section
set_option maxHeartbeats 800000
open scoped Matrix
namespace NLAlib

/-- Every complete Wedin conclusion for native finite row and column types:
exact paired residual identities, constant-one mixed-gap maximum-operator and
paired-Frobenius bounds, unconditional constant-two population-gap bound,
zero-width sine norms, and full-thin native padded zeros. The SVD premises are
the existing `IsSVD` predicate after canonical coordinate normalization, and
the native leading frames retain those precise supplied SVD choices at ties.
Wedin (1972), Section 3; Stewart–Sun, Theorem V.4.4.
atlas: wedin-sin-theta -/
theorem singular_subspace_perturbation_bounds_fintype
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {k : ℕ} {A E : Matrix m n ℝ} {U Uhat : Matrix m m ℝ}
    {V Vhat : Matrix n n ℝ}
    (hA : IsSVD (A.reindex (Fintype.equivFin m) (Fintype.equivFin n))
      (U.reindex (Fintype.equivFin m) (Fintype.equivFin m))
      (V.reindex (Fintype.equivFin n) (Fintype.equivFin n)))
    (hhat : IsSVD ((A + E).reindex (Fintype.equivFin m) (Fintype.equivFin n))
      (Uhat.reindex (Fintype.equivFin m) (Fintype.equivFin m))
      (Vhat.reindex (Fintype.equivFin n) (Fintype.equivFin n)))
    (hk : k ≤ min (Fintype.card m) (Fintype.card n)) :
    let em := Fintype.equivFin m
    let en := Fintype.equivFin n
    let U₁ := (headColumns (U.reindex em em)
      (hk.trans (min_le_left _ _))).reindex em.symm (Equiv.refl (Fin k))
    let V₁ := (headColumns (V.reindex en en)
      (hk.trans (min_le_right _ _))).reindex en.symm (Equiv.refl (Fin k))
    let Uhat₁ := (headColumns (Uhat.reindex em em)
      (hk.trans (min_le_left _ _))).reindex em.symm (Equiv.refl (Fin k))
    let Vhat₁ := (headColumns (Vhat.reindex en en)
      (hk.trans (min_le_right _ _))).reindex en.symm (Equiv.refl (Fin k))
    let T := Matrix.diagonal (fun i : Fin k => (A + E).toEuclideanLin.singularValues i)
    let R := A * Vhat₁ - Uhat₁ * T
    let S := Aᵀ * Uhat₁ - Vhat₁ * T
    let δ := (A + E).toEuclideanLin.singularValues (k - 1) -
      A.toEuclideanLin.singularValues k
    let g := A.toEuclideanLin.singularValues (k - 1) - A.toEuclideanLin.singularValues k
    R = -(E * Vhat₁) ∧ S = -(Eᵀ * Uhat₁) ∧
      max (specNorm R) (specNorm S) ≤ specNorm E ∧
      (0 < δ →
        max (specNorm (sinePrincipalAngles U₁ Uhat₁))
          (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ max (specNorm R) (specNorm S) / δ ∧
        max (specNorm (sinePrincipalAngles U₁ Uhat₁))
          (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ specNorm E / δ ∧
        Real.sqrt (frobNorm (sinePrincipalAngles U₁ Uhat₁) ^ 2 +
          frobNorm (sinePrincipalAngles V₁ Vhat₁) ^ 2) ≤
            Real.sqrt (frobNorm R ^ 2 + frobNorm S ^ 2) / δ) ∧
      (0 < g → max (specNorm (sinePrincipalAngles U₁ Uhat₁))
        (specNorm (sinePrincipalAngles V₁ Vhat₁)) ≤ 2 * specNorm E / g) ∧
      (k = 0 → specNorm (sinePrincipalAngles U₁ Uhat₁) = 0 ∧
        specNorm (sinePrincipalAngles V₁ Vhat₁) = 0 ∧
        frobNorm (sinePrincipalAngles U₁ Uhat₁) = 0 ∧
        frobNorm (sinePrincipalAngles V₁ Vhat₁) = 0) ∧
      (k = min (Fintype.card m) (Fintype.card n) →
        A.toEuclideanLin.singularValues k = 0 ∧
        (A + E).toEuclideanLin.singularValues k = 0) := by
  intro em en U₁ V₁ Uhat₁ Vhat₁ T R S δ g
  let AF := A.reindex em en
  let EF := E.reindex em en
  have hE : specNorm EF = specNorm E := specNorm_reindex E em en
  let UF := headColumns (U.reindex em em) (hk.trans (min_le_left _ _))
  let VF := headColumns (V.reindex en en) (hk.trans (min_le_right _ _))
  let UhatF := headColumns (Uhat.reindex em em) (hk.trans (min_le_left _ _))
  let VhatF := headColumns (Vhat.reindex en en) (hk.trans (min_le_right _ _))
  let RF := AF * VhatF - UhatF * T
  let SF := AFᵀ * UhatF - VhatF * T
  have hσA : singularValues AF = A.toEuclideanLin.singularValues :=
    singularValues_reindex A _ _
  have hσB : singularValues (AF + EF) = (A + E).toEuclideanLin.singularValues :=
    singularValues_reindex (A + E) _ _
  have h := singular_subspace_perturbation_bounds (A := AF) (E := EF) hA hhat hk
  change (AF * VhatF - UhatF * Matrix.diagonal (fun i : Fin k => singularValues (AF + EF) i) =
      -(EF * VhatF)) ∧ _ at h
  rw [hσB, hσA] at h
  change (RF = -(EF * VhatF)) ∧ (SF = -(EFᵀ * UhatF)) ∧
    max (specNorm RF) (specNorm SF) ≤ specNorm EF ∧
    (0 < δ →
      max (specNorm (sinePrincipalAngles UF UhatF))
        (specNorm (sinePrincipalAngles VF VhatF)) ≤ max (specNorm RF) (specNorm SF) / δ ∧
      max (specNorm (sinePrincipalAngles UF UhatF))
        (specNorm (sinePrincipalAngles VF VhatF)) ≤ specNorm EF / δ ∧
      Real.sqrt (frobNorm (sinePrincipalAngles UF UhatF) ^ 2 +
        frobNorm (sinePrincipalAngles VF VhatF) ^ 2) ≤
          Real.sqrt (frobNorm RF ^ 2 + frobNorm SF ^ 2) / δ) ∧
    (0 < g → max (specNorm (sinePrincipalAngles UF UhatF))
      (specNorm (sinePrincipalAngles VF VhatF)) ≤ 2 * specNorm EF / g) ∧
    (k = 0 → specNorm (sinePrincipalAngles UF UhatF) = 0 ∧
      specNorm (sinePrincipalAngles VF VhatF) = 0 ∧
      frobNorm (sinePrincipalAngles UF UhatF) = 0 ∧
      frobNorm (sinePrincipalAngles VF VhatF) = 0) at h
  have hUh : Uhat₁.reindex em (Equiv.refl (Fin k)) = UhatF := by simp [Uhat₁, UhatF]
  have hVh : Vhat₁.reindex en (Equiv.refl (Fin k)) = VhatF := by simp [Vhat₁, VhatF]
  have hR : R.reindex em (Equiv.refl (Fin k)) = RF := by
    change (A * Vhat₁ - Uhat₁ * T).reindex em (Equiv.refl (Fin k)) = _
    change (A * Vhat₁).reindex em (Equiv.refl (Fin k)) -
      (Uhat₁ * T).reindex em (Equiv.refl (Fin k)) = _
    rw [mul_reindex A Vhat₁ em en, mul_reindex Uhat₁ T em (Equiv.refl (Fin k)), hVh, hUh]
    rfl
  have hS : S.reindex en (Equiv.refl (Fin k)) = SF := by
    change (Aᵀ * Uhat₁ - Vhat₁ * T).reindex en (Equiv.refl (Fin k)) = _
    change (Aᵀ * Uhat₁).reindex en (Equiv.refl (Fin k)) -
      (Vhat₁ * T).reindex en (Equiv.refl (Fin k)) = _
    rw [mul_reindex Aᵀ Uhat₁ en em, mul_reindex Vhat₁ T en (Equiv.refl (Fin k)), hUh, hVh]
    rfl
  have hER : (E * Vhat₁).reindex em (Equiv.refl (Fin k)) = EF * VhatF := by
    rw [mul_reindex E Vhat₁ em en, hVh]
  have hES : (Eᵀ * Uhat₁).reindex en (Equiv.refl (Fin k)) = EFᵀ * UhatF := by
    rw [mul_reindex Eᵀ Uhat₁ en em, hUh]
    rfl
  have hsinU : sinePrincipalAngles UF UhatF = sinePrincipalAngles U₁ Uhat₁ := by
    exact (sinePrincipalAngles_reindex_rows UF UhatF em.symm).symm
  have hsinV : sinePrincipalAngles VF VhatF = sinePrincipalAngles V₁ Vhat₁ := by
    exact (sinePrincipalAngles_reindex_rows VF VhatF en.symm).symm
  rcases h with ⟨hRFin, hSFin, hnorm, hδbound, hgbound, hzero⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Matrix.reindex em (Equiv.refl (Fin k))).injective
    change R.reindex em (Equiv.refl (Fin k)) = -((E * Vhat₁).reindex em (Equiv.refl (Fin k)))
    rw [hR, hER]
    exact hRFin
  · apply (Matrix.reindex en (Equiv.refl (Fin k))).injective
    change S.reindex en (Equiv.refl (Fin k)) = -((Eᵀ * Uhat₁).reindex en (Equiv.refl (Fin k)))
    rw [hS, hES]
    exact hSFin
  · simpa only [← hR, ← hS, specNorm_reindex, hE] using hnorm
  · simpa only [hsinU, hsinV, ← hR, ← hS, specNorm_reindex, frobNorm_reindex, hE] using hδbound
  · simpa only [hsinU, hsinV, hE] using hgbound
  · simpa only [hsinU, hsinV] using hzero
  · intro hfull
    rw [← hσA, ← hσB]
    exact ⟨singularValues_eq_zero_of_min_le AF hfull.ge,
      singularValues_eq_zero_of_min_le (AF + EF) hfull.ge⟩

end NLAlib
