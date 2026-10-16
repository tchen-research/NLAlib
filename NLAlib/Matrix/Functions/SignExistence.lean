import NLAlib.Matrix.Functions.SignCharacterization
import NLAlib.ForMathlib.Algebra.PolynomialRootPartition
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Existence of the matrix sign by coprime characteristic factors

The root multiset is partitioned by the open right half-plane. Bezout
evaluation and Cayley--Hamilton construct complementary primary
projectors, without requiring diagonalizability. Higham, Functions of
Matrices, Chapter 5; matrix-toolkit derivations, Section `eq-sign-projectors`.
-/

noncomputable section
open Matrix Polynomial
open scoped Matrix.Norms.L2Operator
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Spectral separation from the imaginary axis gives a matrix satisfying
the sign characterization, constructed by coprime polynomial factors. -/
private theorem exists_isMatrixSign_nonempty {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : ∃ S, IsMatrixSign A S := by
  classical
  obtain ⟨f, g, hf, hg, hfg, hcop, hfr, hgr⟩ :=
    Polynomial.exists_coprime_factors_roots_partition A.charpoly A.charpoly_monic
      (fun z : ℂ => 0 < z.re)
  obtain ⟨a, b, hab⟩ := hcop
  let P := aeval A (b * g)
  let Q := aeval A (a * f)
  have hsum : P + Q = 1 := by
    change aeval A (b * g) + aeval A (a * f) = 1
    rw [← map_add, add_comm (b * g), hab, map_one]
  have hzero : aeval A (f * g) = 0 := by rw [hfg, Matrix.aeval_self_charpoly]
  have hPQ : P * Q = 0 := by
    change aeval A (b * g) * aeval A (a * f) = 0
    calc
      _ = aeval A ((f * g) * (a * b)) := by rw [← map_mul]; congr 1; ring
      _ = 0 := by rw [map_mul, hzero, Matrix.zero_mul]
  have hQP : Q * P = 0 := by
    have hc := (Commute.all (a * f) (b * g)).map (aeval A)
    exact hc.eq.trans hPQ
  have hPP : P * P = P := by
    calc
      _ = P * P + P * Q := by rw [hPQ, add_zero]
      _ = P * (P + Q) := (Matrix.mul_add _ _ _).symm
      _ = P := by rw [hsum, Matrix.mul_one]
  have hQQ : Q * Q = Q := by
    calc
      _ = Q * P + Q * Q := by rw [hQP, zero_add]
      _ = Q * (P + Q) := (Matrix.mul_add _ _ _).symm
      _ = Q := by rw [hsum, Matrix.mul_one]
  refine ⟨P - Q, ?_, ?_, ?_⟩
  · calc
      (P - Q) ^ 2 = P * P - P * Q - Q * P + Q * Q := by noncomm_ring
      _ = 1 := by rw [hPP, hQQ, hPQ, hQP, sub_zero, sub_zero, hsum]
  · have hc := (Commute.all (X : ℂ[X]) (b * g - a * f)).map (aeval A)
    simpa only [map_sub, aeval_X] using hc
  · intro z hz
    have heq : (P - Q) * A = aeval A ((b * g - a * f) * X) := by
      simp only [map_mul, map_sub, aeval_X, P, Q]
    rw [heq, spectrum.map_polynomial_aeval] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwroot : w ∈ A.charpoly.roots :=
      (Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr
        (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hw)
    have hbez : a.eval w * f.eval w + b.eval w * g.eval w = 1 := by
      simpa only [eval_add, eval_mul, eval_one] using congrArg (eval w) hab
    by_cases hwpos : 0 < w.re
    · have hfw : f.eval w = 0 := (Polynomial.mem_roots hf.ne_zero).mp
        (by rw [hfr, Multiset.mem_filter]; exact ⟨hwroot, hwpos⟩)
      have hbg : b.eval w * g.eval w = 1 := by simpa only [hfw, mul_zero, zero_add] using hbez
      simpa only [eval_mul, eval_sub, eval_X, hfw, mul_zero, hbg, sub_zero, one_mul] using hwpos
    · have hgw : g.eval w = 0 := (Polynomial.mem_roots hg.ne_zero).mp
        (by rw [hgr, Multiset.mem_filter]; exact ⟨hwroot, hwpos⟩)
      have haf : a.eval w * f.eval w = 1 := by simpa only [hgw, mul_zero, add_zero] using hbez
      have hwneg : w.re < 0 := lt_of_le_of_ne (le_of_not_gt hwpos) (hA w hw)
      simp only [eval_mul, eval_sub, eval_X, hgw, mul_zero, haf, zero_sub, neg_one_mul,
        Complex.neg_re]
      linarith

omit [Nonempty n] in
/-- The spectral sign exists in every finite dimension, including zero. -/
theorem exists_isMatrixSign {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : ∃ S, IsMatrixSign A S := by
  classical
  cases isEmpty_or_nonempty n with
  | inl hn =>
    let := hn
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · exact Commute.one_right A
    · intro z hz
      simp only [spectrum.of_subsingleton, Set.mem_empty_iff_false] at hz
  | inr hn =>
    let := hn
    exact exists_isMatrixSign_nonempty hA

/-- The matrix sign, uniquely characterized by an involution commuting
with the input whose product with the input is positive stable.
Outside the spectrally separated domain this is a total choice. -/
def matrixSign (A : Matrix n n ℂ) : Matrix n n ℂ := Classical.epsilon (IsMatrixSign A)

omit [Nonempty n] in
/-- The matrix sign satisfies its defining characterization whenever no
eigenvalue lies on the imaginary axis. -/
theorem isMatrixSign_matrixSign {A : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) : IsMatrixSign A (matrixSign A) :=
  Classical.epsilon_spec (exists_isMatrixSign hA)

omit [Nonempty n] in
/-- Every matrix satisfying the sign characterization equals the
canonical sign; the construction is independent of Bezout choices. -/
theorem IsMatrixSign.eq_matrixSign {A S : Matrix n n ℂ}
    (hA : ∀ z ∈ spectrum ℂ A, z.re ≠ 0) (hS : IsMatrixSign A S) :
    S = matrixSign A := hS.eq (isMatrixSign_matrixSign hA)

end NLAlib
