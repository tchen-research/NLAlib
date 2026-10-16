import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Spectral.DiagonalSingularValues

/-!
# Schatten power sums of diagonal matrices

The unsorted diagonal moduli give every square diagonal Schatten power sum;
no nonzero-entry, ordering or positive-dimension hypotheses are needed.
-/

noncomputable section
namespace NLAlib

/-- Every finite-exponent Schatten power sum of a complex diagonal matrix
is the power sum of the diagonal moduli, regardless of their order. -/
theorem schattenNormReal_diagonal_complex {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℂ) (p : ℝ) :
    schattenNormReal (Matrix.diagonal d) p = (∑ i, ‖d i‖^p)^(1/p) := by
  have h := congrArg (fun s : Multiset ℝ => (s.map (fun x => x^p)).sum)
    (multiset_singularValues_diagonal_complex d)
  simp only [Multiset.map_map, Function.comp_def, Finset.sum_map_val] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => singularValues (Matrix.diagonal d) i ^ p)
    (Fintype.card n)] at h
  simpa only [schattenNormReal,min_self] using congrArg (fun x : ℝ => x^(1/p)) h

/-- Every finite-exponent Schatten power sum of a real diagonal matrix
is the power sum of the absolute diagonal entries. -/
theorem schattenNormReal_diagonal_real {n : Type*} [Fintype n] [DecidableEq n]
    (d : n → ℝ) (p : ℝ) :
    schattenNormReal (Matrix.diagonal d) p = (∑ i, |d i|^p)^(1/p) := by
  have heq : (Matrix.diagonal d).map Complex.ofReal = Matrix.diagonal (fun i => (d i : ℂ)) := by
    simp
  have h := schattenNormReal_diagonal_complex (fun i => (d i : ℂ)) p
  rw [←heq] at h
  have hs (i : ℕ) : singularValues ((Matrix.diagonal d).map Complex.ofReal) i
      = singularValues (Matrix.diagonal d) i :=
    singularValues_map_ofReal (𝕜 := ℂ) (Matrix.diagonal d) i
  simpa only [schattenNormReal,hs,Complex.norm_real,Real.norm_eq_abs] using h

end NLAlib
