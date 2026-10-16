import NLAlib.Matrix.Functions.Monotonicity
import NLAlib.Matrix.Spectral.Complexification
import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Scalar concavity from two-dimensional matrix monotonicity

A rotation and an arbitrarily small diagonal completion prove scalar
concavity at the boundary as well as in the interior. Continuity is
only required on the nonnegative half-line. Toolkit derivations (F1).
-/

noncomputable section
open Matrix Filter Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib

private def planeRotation (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt a : ℂ), -(Real.sqrt b : ℂ); (Real.sqrt b : ℂ), (Real.sqrt a : ℂ)]

private theorem planeRotation_mem_unitary {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a+b=1) : planeRotation a b ∈ unitary (Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j
  all_goals apply Complex.ext <;> simp [planeRotation, Matrix.star_eq_conjTranspose,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]; all_goals nlinarith

private theorem diagonal_completion_posSemidef (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hD : D.IsHermitian) {ε : ℝ} (hε : 0 < ε) :
    (diagonal ![D 0 0 + ε, D 1 1 + (D 0 1)^2/ε] - D).PosSemidef := by
  let v : Fin 2 → ℝ := ![1, -(D 0 1)/ε]
  have hv := (posSemidef_vecMulVec_self_star v).smul hε.le
  have he : diagonal ![D 0 0 + ε, D 1 1 + (D 0 1)^2/ε] - D =
      ε • vecMulVec v (star v) := by
    have hd : D 1 0 = D 0 1 := by simpa using hD.apply 0 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, v, vecMulVec, hd]
    all_goals field_simp
  rwa [← he] at hv

/-- A continuous operator-monotone function on the nonnegative half-line
is scalar concave, including combinations whose value is zero. -/
theorem OperatorMonotoneOn.concaveOn_nonneg {f : ℝ → ℝ}
    (hm : OperatorMonotoneOn (Ici 0) f) (hf : ContinuousOn f (Ici 0)) :
    ConcaveOn ℝ (Ici 0) f := by
  refine ⟨convex_Ici _, ?_⟩
  intro x hx y hy a b ha hb hab
  let R : unitary (Matrix (Fin 2) (Fin 2) ℂ) :=
    ⟨planeRotation a b, planeRotation_mem_unitary ha hb hab⟩
  let D := (R : Matrix (Fin 2) (Fin 2) ℂ) * diagonal (fun i : Fin 2 => ((![x,y] i : ℝ) : ℂ)) *
    (R : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose
  have hdiag : (diagonal (fun i : Fin 2 => ((![x,y] i : ℝ) : ℂ))).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · simpa using (RCLike.ofReal_nonneg.mpr hx : (0 : ℂ) ≤ (x : ℂ))
    · simpa using (RCLike.ofReal_nonneg.mpr hy : (0 : ℂ) ≤ (y : ℂ))
  have hD : D.PosSemidef := hdiag.mul_mul_conjTranspose_same _
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  let Dreal : Matrix (Fin 2) (Fin 2) ℝ :=
    !![a*x+b*y, Real.sqrt a*Real.sqrt b*(x-y);
       Real.sqrt a*Real.sqrt b*(x-y), b*x+a*y]
  have hreal : D = Dreal.map Complex.ofReal := by
    ext i j
    simp only [D, R, planeRotation, Dreal, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two, Matrix.map_apply]
    fin_cases i <;> fin_cases j
    all_goals apply Complex.ext <;> simp [Matrix.diagonal,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    all_goals nlinarith [congrArg (fun z => z*x) hsa, congrArg (fun z => z*y) hsa,
      congrArg (fun z => z*x) hsb, congrArg (fun z => z*y) hsb]
  have hDr : Dreal.PosSemidef := (posSemidef_realMatrixComplexification_iff Dreal).mp (hreal ▸ hD)
  have hDf : (cfc f D) 0 0 = ((a*f x+b*f y : ℝ) : ℂ) := by
    dsimp [D]
    rw [cfc_unitary_conj R f _ hdiag.isHermitian, cfc_diagonal_real]
    simp only [R, planeRotation, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    apply Complex.ext <;> simp [Matrix.diagonal, Complex.mul_re, Complex.mul_im,
      Complex.add_re, Complex.add_im]
    nlinarith [congrArg (fun z => z*f x) hsa, congrArg (fun z => z*f y) hsb]
  have hbound (ε : ℝ) (hε : 0 < ε) : a*f x+b*f y ≤ f (a*x+b*y+ε) := by
    let ev : Fin 2 → ℝ := ![Dreal 0 0 + ε, Dreal 1 1 + (Dreal 0 1)^2/ε]
    let E := diagonal (fun i => (ev i : ℂ))
    have hDE : D ≤ E := by
      rw [Matrix.le_iff, hreal]
      have h := (posSemidef_realMatrixComplexification_iff (𝕜 := ℂ) _).mpr
        (diagonal_completion_posSemidef Dreal hDr.isHermitian hε)
      change (realMatrixComplexification
        (diagonal ![Dreal 0 0 + ε, Dreal 1 1 + (Dreal 0 1)^2/ε] - Dreal) : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef at h
      rw [map_sub] at h
      convert! h using 1
      ext i j
      by_cases hij : i = j <;> simp [E, ev, Matrix.diagonal, hij, realMatrixComplexification]
    have hE : E.PosSemidef := (hD.nonneg.trans hDE).posSemidef
    have hm' := hm.cfc_le hD.isHermitian hE.isHermitian
      (fun _ hx => spectrum_nonneg_of_nonneg hD.nonneg hx)
      (fun _ hx => spectrum_nonneg_of_nonneg hE.nonneg hx) hDE
    have hd := (Matrix.le_iff.mp hm').diag_nonneg (i := (0 : Fin 2))
    rw [Matrix.sub_apply, hDf, show cfc f E = diagonal (fun i => (f (ev i) : ℂ)) from
      cfc_diagonal_real f ev] at hd
    have hh := (RCLike.nonneg_iff.mp hd).1
    simpa [ev, Dreal] using hh
  have hz : 0 ≤ a*x+b*y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have ht : Tendsto (fun ε : ℝ => a*x+b*y+ε) (𝓝[>] 0) (𝓝[Ici 0] (a*x+b*y)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using (tendsto_const_nhds.add (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0))), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact add_nonneg hz (le_of_lt hε)
  have hh := ge_of_tendsto ((hf _ hz).tendsto.comp ht)
    (Eventually.mono self_mem_nhdsWithin fun ε hε => hbound ε hε)
  exact hh

end NLAlib
