import NLAlib.RandomMatrix.Chaos.Flattenings
import NLAlib.Matrix.Structured.RectangularCoefficientBlocks

/-!
# Degree-one flattenings and the two variance matrices

The two coefficient flattenings of a linear matrix series are precisely its
horizontal and vertical block matrices, up to the unique empty-coordinate label.
Source: Bandeira–Lucca–Nizić-Nikolac–van Handel, §§2.1–2.2.
-/

noncomputable section
open scoped Matrix
namespace NLAlib

private def emptyCoordinateProdEquiv {τ ι m : Type*} [DecidableEq τ]
    (S : Finset τ) (hS : S = ∅) : ((S → ι) × m) ≃ m where
  toFun x := x.2
  invFun a := (fun t => False.elim (by simpa [hS] using t.property), a)
  left_inv x := by
    rcases x with ⟨x, a⟩
    apply Prod.ext
    · funext t
      exact False.elim (by simpa [hS] using t.property)
    · rfl
  right_inv _ := rfl

private def fullOneCoordinateEquiv {τ ι : Type*} [Fintype τ] [Unique τ]
    (S : Finset τ) (hS : S.Nonempty) : (S → ι) ≃ ι where
  toFun x := x ⟨hS.choose, hS.choose_spec⟩
  invFun j := fun _ => j
  left_inv x := by
    funext t
    exact congrArg x (Subsingleton.elim _ _)
  right_inv _ := rfl

variable {τ ι m n 𝕜 : Type*} [Fintype τ] [Unique τ] [DecidableEq τ]
  [Fintype ι] [Fintype m] [Fintype n] [DecidableEq ι]
  [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- In degree one, the empty-subset flattening is the horizontal coefficient
block up to relabeling its singleton row-coordinate factor.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_chaosFlattening_empty_of_unique (A : (τ → ι) → Matrix m n 𝕜) :
    specNorm (chaosFlattening A ∅) =
      specNorm (coefficientRow (fun j => A (fun _ => j))) := by
  let e : (((∅ : Finset τ) → ι) × m) ≃ m := emptyCoordinateProdEquiv ∅ rfl
  let f : ((((∅ : Finset τ)ᶜ : Finset τ) → ι) × n) ≃ (ι × n) :=
    (fullOneCoordinateEquiv _ (by simp)).prodCongr (Equiv.refl n)
  have he : (chaosFlattening A ∅).reindex e f =
      coefficientRow (fun j => A (fun _ => j)) := by
    ext a jb
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosFlattening,
      e, f, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
      emptyCoordinateProdEquiv, fullOneCoordinateEquiv, Equiv.coe_fn_symm_mk,
      Equiv.refl_symm, Equiv.refl_apply, coefficientRow]
    congr 2
  rw [← he, specNorm_reindex]

/-- In degree one, the full-subset flattening is the vertical coefficient block.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_chaosFlattening_univ_of_unique (A : (τ → ι) → Matrix m n 𝕜) :
    specNorm (chaosFlattening A Finset.univ) =
      specNorm (coefficientColumn (fun j => A (fun _ => j))) := by
  let e : ((↥(Finset.univ : Finset τ) → ι) × m) ≃ (ι × m) :=
    (fullOneCoordinateEquiv _ Finset.univ_nonempty).prodCongr (Equiv.refl m)
  let f : ((((Finset.univ : Finset τ)ᶜ : Finset τ) → ι) × n) ≃ n :=
    emptyCoordinateProdEquiv _ (by simp)
  have he : (chaosFlattening A Finset.univ).reindex e f =
      coefficientColumn (fun j => A (fun _ => j)) := by
    ext ia b
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, chaosFlattening,
      e, f, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
      emptyCoordinateProdEquiv, fullOneCoordinateEquiv, Equiv.coe_fn_symm_mk,
      Equiv.refl_symm, Equiv.refl_apply, coefficientColumn]
    congr 2
    funext t
    simp [chaosAssemble, Subsingleton.elim t default]
  rw [← he, specNorm_reindex]

/-- The empty-subset degree-one flattening squares to the row-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_chaosFlattening_empty_sq (A : (τ → ι) → Matrix m n 𝕜) :
    specNorm (chaosFlattening A ∅) ^ 2 =
      specNorm (∑ j, A (fun _ => j) * (A (fun _ => j))ᴴ) := by
  rw [specNorm_chaosFlattening_empty_of_unique, specNorm_coefficientRow_sq]

/-- The full-subset degree-one flattening squares to the column-variance norm.
Source: finite block multiplication.
atlas: matrix-chaos-flattenings-def (partial) -/
theorem specNorm_chaosFlattening_univ_sq (A : (τ → ι) → Matrix m n 𝕜) :
    specNorm (chaosFlattening A Finset.univ) ^ 2 =
      specNorm (∑ j, (A (fun _ => j))ᴴ * A (fun _ => j)) := by
  rw [specNorm_chaosFlattening_univ_of_unique, specNorm_coefficientColumn_sq]

end NLAlib
