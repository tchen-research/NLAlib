import NLAlib.Matrix.Norms.Schatten
import NLAlib.Matrix.Spectral.SingularValueInvariance
import NLAlib.Matrix.Inequalities.KyFanNorms
import NLAlib.Matrix.Norms.NuclearNorm
import NLAlib.Matrix.Inequalities.KyFanSums
import NLAlib.Matrix.Inequalities.MajorizationConvex

/-!
# Schatten norm axioms

Increasing convex power functions preserve the proved singular-value weak
majorization. Scalar Minkowski then gives the matrix triangle inequality.
Source: Bhatia (1997), §IV.2; Horn–Johnson (1991), §3.4.
Atlas: `schatten-norms-def`.
-/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators

namespace NLAlib

/-- A positive-part power is increasing and convex at every exponent at least
one. This is the global scalar test used for nonnegative singular-value lists. -/
theorem monotone_convexOn_rpow_max_zero {p : ℝ} (hp : 1 ≤ p) :
    Monotone (fun u : ℝ => max u 0 ^ p) ∧ ConvexOn ℝ Set.univ (fun u : ℝ => max u 0 ^ p) := by
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  have hm : Monotone (fun u : ℝ => max u 0) := fun u v huv => max_le_max huv le_rfl
  have hc : ConvexOn ℝ Set.univ (fun u : ℝ => max u 0) := by
    simpa only [sub_zero] using (monotone_convexOn_max_sub 0).2
  have him : (fun u : ℝ => max u 0) '' Set.univ = Set.Ici 0 := by
    ext z
    constructor
    · rintro ⟨u, _, rfl⟩
      exact Set.mem_Ici.mpr (le_max_right u (0 : ℝ))
    · intro hz
      exact ⟨z, Set.mem_univ z, max_eq_left hz⟩
  have hpow : ConvexOn ℝ ((fun u : ℝ => max u 0) '' Set.univ) (fun u : ℝ => u ^ p) := by
    rw [him]
    exact convexOn_rpow hp
  have hpowm : MonotoneOn (fun u : ℝ => u ^ p) ((fun u : ℝ => max u 0) '' Set.univ) := by
    rw [him]
    exact Real.monotoneOn_rpow_Ici_of_exponent_nonneg hp0
  refine ⟨fun u v huv => Real.rpow_le_rpow (le_max_right u 0) (hm huv) hp0, ?_⟩
  exact hpow.comp hc hpowm

/-- Nonnegative weakly majorized lists have every norm-exponent power sum
bounded by that of the comparator. -/
theorem WeaklyMajorized.sum_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {x y : ι → ℝ} (hxy : WeaklyMajorized x y) (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ i, 0 ≤ y i) {p : ℝ} (hp : 1 ≤ p) : (∑ i, x i ^ p) ≤ ∑ i, y i ^ p := by
  have h := hxy.sum_monotone_convex_le (monotone_convexOn_rpow_max_zero hp).1
    (monotone_convexOn_rpow_max_zero hp).2
  simpa only [max_eq_left (hx _), max_eq_left (hy _)] using h

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Every finite Schatten norm at exponent at least one obeys the matrix
triangle inequality. It follows from actual singular-value weak majorization
and scalar Minkowski, without assuming a gauge or a matrix norm property.
atlas: schatten-norms-def (partial) -/
theorem schattenNorm_add_le (A B : Matrix m n ℝ) {p : ℝ} (hp : 1 ≤ p) :
    schattenNorm (A + B) p ≤ schattenNorm A p + schattenNorm B p := by
  let N := min (Fintype.card m) (Fintype.card n)
  have hsum := (weaklyMajorized_singularValues_add A B).sum_rpow_le
    (fun i => singularValues_nonneg _ i)
    (fun i => add_nonneg (singularValues_nonneg _ i) (singularValues_nonneg _ i)) hp
  have hroot := Real.rpow_le_rpow (Finset.sum_nonneg (fun (i : Fin N) (_ : i ∈ Finset.univ) =>
    Real.rpow_nonneg (singularValues_nonneg (A + B) i) p)) hsum
      (one_div_nonneg.mpr (le_trans zero_le_one hp))
  have htri := Real.Lp_add_le_of_nonneg (Finset.univ : Finset (Fin N))
    (f := fun i => singularValues A i) (g := fun i => singularValues B i) hp
    (fun i _ => singularValues_nonneg _ i) (fun i _ => singularValues_nonneg _ i)
  have h := hroot.trans htri
  rw [Fin.sum_univ_eq_sum_range (fun i => singularValues (A + B) i ^ p) N,
    Fin.sum_univ_eq_sum_range (fun i => singularValues A i ^ p) N,
    Fin.sum_univ_eq_sum_range (fun i => singularValues B i ^ p) N] at h
  exact h

omit [DecidableEq m] in
/-- Absolute homogeneity of every positive-exponent finite Schatten norm. -/
theorem schattenNorm_smul (A : Matrix m n ℝ) (c : ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm (c • A) p = |c| * schattenNorm A p := by
  have hsum : 0 ≤ ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i ^ p :=
    Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (singularValues_nonneg _ i) p)
  unfold schattenNorm
  simp_rw [singularValues_smul, Real.mul_rpow (abs_nonneg c) (singularValues_nonneg _ _),
    ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) p) hsum,
    one_div, Real.rpow_rpow_inv (abs_nonneg c) hp.ne']

omit [DecidableEq m] in
/-- At every positive exponent, the Schatten norm vanishes on the zero matrix. -/
theorem schattenNorm_zero {p : ℝ} (hp : 0 < p) : schattenNorm (0 : Matrix m n ℝ) p = 0 := by
  simp [schattenNorm, singularValues_eq_linearMap, Real.zero_rpow hp.ne',
    Real.zero_rpow (show p⁻¹ ≠ 0 from inv_ne_zero hp.ne')]

/-- At every positive exponent, the finite Schatten power sum separates zero,
including empty matrix spaces. -/
theorem schattenNorm_eq_zero_iff (A : Matrix m n ℝ) {p : ℝ} (hp : 0 < p) :
    schattenNorm A p = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hsum0 : (∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        singularValues A i ^ p) = 0 :=
      (Real.rpow_eq_zero (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValues_nonneg _ i) p) (by positivity)).mp h
    have hi (i : ℕ) (hi : i ∈ Finset.range (min (Fintype.card m) (Fintype.card n))) :
        singularValues A i = 0 := by
      have hpw : singularValues A i ^ p = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
          Real.rpow_nonneg (singularValues_nonneg _ j) p)).mp hsum0 i hi
      exact (Real.rpow_eq_zero (singularValues_nonneg _ i) hp.ne').mp hpw
    apply (nuclearNorm_eq_zero_iff A).mp
    exact Finset.sum_eq_zero hi
  · rintro rfl
    exact schattenNorm_zero hp

/-- The bundled Schatten seminorm for every finite norm exponent. Its
separating zero criterion is proved above, so this is a genuine norm.
atlas: schatten-norms-def (partial) -/
def schattenSeminorm (p : ℝ) (hp : 1 ≤ p) : Seminorm ℝ (Matrix m n ℝ) :=
  Seminorm.of (fun A => schattenNorm A p) (fun A B => schattenNorm_add_le A B hp)
    (fun c A => by simpa only [Real.norm_eq_abs] using
      schattenNorm_smul A c (lt_of_lt_of_le zero_lt_one hp))

/-- The bundled Schatten seminorm agrees with the native singular-value formula. -/
@[simp] theorem schattenSeminorm_apply (A : Matrix m n ℝ) (p : ℝ) (hp : 1 ≤ p) :
    schattenSeminorm p hp A = schattenNorm A p := rfl

end NLAlib
