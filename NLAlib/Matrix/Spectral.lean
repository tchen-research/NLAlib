import Mathlib.LinearAlgebra.Matrix.DotProduct
import NLAlib.Matrix.Norms

/-!
# Extreme eigenvalues and singular values

Variational definitions of the smallest eigenvalue of a symmetric matrix and of the smallest
singular value of a rectangular matrix, and the perturbation bounds every probabilistic
argument about them starts from.

* `NLAlib.lamMin M`: the minimum of the Rayleigh quotient, `inf { xᵀ M x : ‖x‖₂ = 1 }`
  (`lamMin_eq_iInf_rayleigh` gives the quotient form `inf_{x ≠ 0} xᵀMx / xᵀx`);
* `NLAlib.sigmaMin A`: the smallest singular value of a tall matrix `A : Matrix m n ℝ`,
  `inf { ‖Ax‖₂ : ‖x‖₂ = 1 }` (for a wide matrix apply it to `Aᵀ`);
* `NLAlib.sigmaMinSq A = lamMin (Aᵀ A)`, with `sigmaMinSq_eq_sigmaMin_sq` and
  `sigmaMin_eq_sqrt_sigmaMinSq`.

Every infimum is over the unit sphere of `n → ℝ`; when `n` is empty the sphere is empty and the
real convention `inf ∅ = 0` makes all three equal to `0`.

## Contents

* Basic facts: nonnegativity, `sigmaMin A ≤ ‖Ax‖₂` on the sphere and `sigmaMin A ‖x‖₂ ≤ ‖Ax‖₂`
  everywhere, `sigmaMin A ≤ ‖A‖₂` when `n` is nonempty, the relation with `lamMin (AᵀA)`.
* Lipschitz bounds (atlas `norm-lipschitz`): `σ_min` and `‖·‖₂` are `1`-Lipschitz for the
  Frobenius norm, `|σ_min(A) − σ_min(B)| ≤ ‖A − B‖_F` and `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖_F`.
* Euclidean coordinates and nets: `‖u‖ = √(∑ uⱼ²)`, `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`, and the net
  bound `(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩` for an `ε`-net `I` of pairs of unit vectors
  (`one_sub_two_mul_mul_specNorm_le_iSup`), used by the Gaussian comparison proofs of
  `NLAlib.Gaussian.Extreme`.

The definition of `sigmaMin` and the Lipschitz proofs are ported from the Prove2me Gaussian
series (`GaussianMatrix.sMin`, solutions `GaussianMatrix.sMin_lipschitz` and
`GaussianMatrix.specNorm_lipschitz`).

Follow-up: the identification of `sigmaMin` with `NLAlib.singularValues` (the
`min m n`-th singular value when `n ≤ m`) is not proved here.

Atlas: `norm-lipschitz`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n]

/-! ### Definitions -/

/-- The smallest eigenvalue of a (symmetric) matrix, as the minimum of the Rayleigh quotient on
the unit sphere: `λ_min(M) = inf { xᵀ M x : xᵀ x = 1 }` (`0` when `n` is empty). -/
def lamMin (M : Matrix n n ℝ) : ℝ :=
  ⨅ x : {x : n → ℝ // x ⬝ᵥ x = 1}, x.1 ⬝ᵥ M *ᵥ x.1

/-- The smallest singular value of a tall matrix `A : Matrix m n ℝ`:
`σ_min(A) = inf { ‖A x‖₂ : x ∈ ℝⁿ, ‖x‖₂ = 1 }` (`0` when `n` is empty, by the real convention
`inf ∅ = 0`). For a wide matrix use `sigmaMin Aᵀ`. Same definition as the Prove2me
`GaussianMatrix.sMin`. -/
def sigmaMin (A : Matrix m n ℝ) : ℝ :=
  ⨅ x : {x : n → ℝ // x ⬝ᵥ x = 1}, Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1))

/-- The squared smallest singular value of a tall matrix, `σ_min(A)² = λ_min(AᵀA)`
(`sigmaMinSq_eq_sigmaMin_sq`). For a wide matrix `G`, `sigmaMinSq Gᵀ = lamMin (G Gᵀ)`. -/
def sigmaMinSq (A : Matrix m n ℝ) : ℝ := lamMin (Aᵀ * A)

/-! ### Basic facts -/

/-- `‖v‖₂ = √(v ⬝ v)` for the Euclidean norm of `WithLp.toLp 2 v`. Atlas `norm-lipschitz`. -/
theorem sqrt_dotProduct_self_eq_norm (v : m → ℝ) :
    Real.sqrt (v ⬝ᵥ v) = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ m)‖ := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- Triangle inequality for the Euclidean length `√(v ⬝ v)`. Atlas `norm-lipschitz`. -/
theorem sqrt_dotProduct_add_le (u v : m → ℝ) :
    Real.sqrt ((u + v) ⬝ᵥ (u + v)) ≤ Real.sqrt (u ⬝ᵥ u) + Real.sqrt (v ⬝ᵥ v) := by
  rw [sqrt_dotProduct_self_eq_norm, sqrt_dotProduct_self_eq_norm, sqrt_dotProduct_self_eq_norm,
    WithLp.toLp_add]
  exact norm_add_le _ _

/-- Row-wise Cauchy–Schwarz, dot-product form: `‖Bx‖₂² ≤ ‖B‖_F² ‖x‖₂²`.
Atlas `norm-lipschitz`. -/
theorem mulVec_dotProduct_mulVec_le_frobSq_mul (B : Matrix m n ℝ) (x : n → ℝ) :
    (B *ᵥ x) ⬝ᵥ (B *ᵥ x) ≤ frobSq B * (x ⬝ᵥ x) := by
  have h := sum_sq_mulVec_le_frobSq B x
  simpa [dotProduct, sq] using h

/-- `x ⬝ (AᵀA) x = ‖Ax‖₂²`. Atlas `norm-lipschitz`. -/
theorem dotProduct_transpose_mul_mulVec (A : Matrix m n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (Aᵀ * A) *ᵥ x = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

omit [Fintype m] in
/-- On an empty index type the unit sphere is empty and `σ_min = 0`. -/
theorem sigmaMin_of_isEmpty [Fintype m] [IsEmpty n] (A : Matrix m n ℝ) : sigmaMin A = 0 := by
  have : IsEmpty {x : n → ℝ // x ⬝ᵥ x = 1} := ⟨fun x => by
    have := x.2; simp [dotProduct] at this⟩
  exact Real.iInf_of_isEmpty _

/-- The sphere is nonempty as soon as the index type is. -/
theorem nonempty_unitSphere [Nonempty n] : Nonempty {x : n → ℝ // x ⬝ᵥ x = 1} := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  exact ⟨⟨Pi.single i 1, by simp [dotProduct, Pi.single_apply]⟩⟩

/-- The set of values `√(‖Ax‖₂²)` on the sphere is bounded below by `0`. -/
theorem bddBelow_range_sqrt_mulVec (A : Matrix m n ℝ) :
    BddBelow (Set.range fun x : {x : n → ℝ // x ⬝ᵥ x = 1} =>
      Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact Real.sqrt_nonneg _

/-- `σ_min(A) ≥ 0`. Atlas `norm-lipschitz`. -/
theorem sigmaMin_nonneg (A : Matrix m n ℝ) : 0 ≤ sigmaMin A := by
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · unfold sigmaMin; rw [Real.iInf_of_isEmpty]
  · exact le_ciInf fun _ => Real.sqrt_nonneg _

/-- `σ_min(A) ≤ ‖Ax‖₂` for every unit vector `x`. Atlas `norm-lipschitz`. -/
theorem sigmaMin_le_sqrt_mulVec (A : Matrix m n ℝ) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) :
    sigmaMin A ≤ Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) :=
  ciInf_le (bddBelow_range_sqrt_mulVec A) ⟨x, hx⟩

/-- `c ≤ σ_min(A)` as soon as `c ≤ ‖Ax‖₂` for every unit vector `x` (index type nonempty).
Atlas `norm-lipschitz`. -/
theorem le_sigmaMin [Nonempty n] (A : Matrix m n ℝ) {c : ℝ}
    (h : ∀ x : n → ℝ, x ⬝ᵥ x = 1 → c ≤ Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x))) : c ≤ sigmaMin A := by
  have := nonempty_unitSphere (n := n)
  exact le_ciInf fun x => h x.1 x.2

/-- `σ_min(A) ‖x‖₂ ≤ ‖Ax‖₂` for every vector `x`. Atlas `norm-lipschitz`. -/
theorem sigmaMin_mul_sqrt_le (A : Matrix m n ℝ) (x : n → ℝ) :
    sigmaMin A * Real.sqrt (x ⬝ᵥ x) ≤ Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
  by_cases hx : x ⬝ᵥ x = 0
  · rw [hx, Real.sqrt_zero, mul_zero]; exact Real.sqrt_nonneg _
  · have hpos : 0 < x ⬝ᵥ x := lt_of_le_of_ne (dotProduct_self_nonneg x) (Ne.symm hx)
    set r := Real.sqrt (x ⬝ᵥ x) with hr
    have hrpos : 0 < r := Real.sqrt_pos.2 hpos
    have hrsq : r * r = x ⬝ᵥ x := Real.mul_self_sqrt hpos.le
    have hu : (r⁻¹ • x) ⬝ᵥ (r⁻¹ • x) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hrsq]
      field_simp
    have h := sigmaMin_le_sqrt_mulVec A hu
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, Real.sqrt_mul (mul_nonneg (inv_nonneg.2 hrpos.le) (inv_nonneg.2 hrpos.le)),
      Real.sqrt_mul_self (inv_nonneg.2 hrpos.le)] at h
    calc sigmaMin A * r ≤ r⁻¹ * Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) * r :=
          mul_le_mul_of_nonneg_right h hrpos.le
      _ = Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by field_simp

/-- For a nonempty index type, the smallest singular value is at most the spectral norm.
Ported from the Prove2me solution `GaussianMatrix.gordon` (helper `gordonSol_sMin_le_specNorm`).
Atlas `norm-lipschitz`. -/
theorem sigmaMin_le_specNorm [DecidableEq m] [DecidableEq n] [Nonempty n] (A : Matrix m n ℝ) :
    sigmaMin A ≤ specNorm A := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  set x : n → ℝ := Pi.single i 1 with hxdef
  have hx : x ⬝ᵥ x = 1 := by
    simp [hxdef, dotProduct, Pi.single_apply]
  refine (sigmaMin_le_sqrt_mulVec A hx).trans ?_
  have hop := Matrix.l2_opNorm_mulVec A (WithLp.toLp 2 x)
  have hnx : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ n)‖ = 1 := by
    rw [← sqrt_dotProduct_self_eq_norm, hx, Real.sqrt_one]
  have hnAx : ‖(EuclideanSpace.equiv m ℝ).symm (A *ᵥ x)‖
      = Real.sqrt ((A *ᵥ x) ⬝ᵥ (A *ᵥ x)) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp [dotProduct, sq]
  rw [hnx, mul_one] at hop
  simp only at hop
  rw [hnAx] at hop
  exact hop

/-- `λ_min(AᵀA) ≥ 0`. Atlas `norm-lipschitz`. -/
theorem sigmaMinSq_nonneg (A : Matrix m n ℝ) : 0 ≤ sigmaMinSq A := by
  unfold sigmaMinSq lamMin
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · rw [Real.iInf_of_isEmpty]
  · refine le_ciInf fun x => ?_
    rw [dotProduct_transpose_mul_mulVec]
    exact dotProduct_self_nonneg _

/-- `σ_min(A) = √(λ_min(AᵀA))`. Atlas `norm-lipschitz`. -/
theorem sigmaMin_eq_sqrt_sigmaMinSq (A : Matrix m n ℝ) :
    sigmaMin A = Real.sqrt (sigmaMinSq A) := by
  unfold sigmaMin sigmaMinSq lamMin
  simp_rw [dotProduct_transpose_mul_mulVec]
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty, Real.sqrt_zero]
  · have hbdd : BddBelow (Set.range fun x : {x : n → ℝ // x ⬝ᵥ x = 1} =>
        (A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) := ⟨0, by
      rintro _ ⟨y, rfl⟩; exact dotProduct_self_nonneg _⟩
    exact (Monotone.map_ciInf_of_continuousAt Real.continuous_sqrt.continuousAt
      (fun _ _ h => Real.sqrt_le_sqrt h) hbdd).symm

/-- `λ_min(AᵀA) = σ_min(A)²`. Atlas `norm-lipschitz`. -/
theorem sigmaMinSq_eq_sigmaMin_sq (A : Matrix m n ℝ) : sigmaMinSq A = sigmaMin A ^ 2 := by
  rw [sigmaMin_eq_sqrt_sigmaMinSq, Real.sq_sqrt (sigmaMinSq_nonneg A)]

/-- For a wide matrix `G`, `σ_min(Gᵀ)² = λ_min(G Gᵀ)`. Atlas `norm-lipschitz`. -/
theorem sigmaMin_transpose_sq (G : Matrix m n ℝ) : sigmaMin Gᵀ ^ 2 = lamMin (G * Gᵀ) := by
  rw [← sigmaMinSq_eq_sigmaMin_sq, sigmaMinSq, Matrix.transpose_transpose]

/-- Unit-sphere values of the Rayleigh quotient are bounded below (by `-∑ᵢⱼ |Mᵢⱼ|`). -/
theorem bddBelow_range_rayleigh (M : Matrix n n ℝ) :
    BddBelow (Set.range fun x : {x : n → ℝ // x ⬝ᵥ x = 1} => x.1 ⬝ᵥ M *ᵥ x.1) := by
  refine ⟨-∑ i, ∑ j, |M i j|, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcoord : ∀ i, |x.1 i| ≤ 1 := by
    intro i
    have h1 : x.1 i ^ 2 ≤ x.1 ⬝ᵥ x.1 := by
      rw [dotProduct]
      have := Finset.single_le_sum (f := fun j => x.1 j * x.1 j)
        (fun j _ => mul_self_nonneg (x.1 j)) (Finset.mem_univ i)
      simpa [sq] using this
    rw [x.2] at h1
    exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  have h : |x.1 ⬝ᵥ M *ᵥ x.1| ≤ ∑ i, ∑ j, |M i j| := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    calc |x.1 i| * (|M i j| * |x.1 j|) ≤ 1 * (|M i j| * 1) := by
          gcongr
          · exact hcoord i
          · exact hcoord j
      _ = |M i j| := by ring
  linarith [neg_abs_le (x.1 ⬝ᵥ M *ᵥ x.1)]

/-- `λ_min(M) ≤ xᵀ M x` for every unit vector `x`. Atlas `norm-lipschitz`. -/
theorem lamMin_le (M : Matrix n n ℝ) {x : n → ℝ} (hx : x ⬝ᵥ x = 1) :
    lamMin M ≤ x ⬝ᵥ M *ᵥ x :=
  ciInf_le (bddBelow_range_rayleigh M) ⟨x, hx⟩

/-- Rayleigh-quotient form: `λ_min(M) = inf_{x ≠ 0} xᵀMx / xᵀx` (both sides `0` when `n` is
empty). Atlas `norm-lipschitz`. -/
theorem lamMin_eq_iInf_rayleigh (M : Matrix n n ℝ) :
    lamMin M = ⨅ x : {x : n → ℝ // x ≠ 0}, (x.1 ⬝ᵥ M *ᵥ x.1) / (x.1 ⬝ᵥ x.1) := by
  -- normalise a nonzero vector to the sphere
  have hnorm : ∀ x : n → ℝ, x ≠ 0 → ∃ y : n → ℝ, y ⬝ᵥ y = 1 ∧
      y ⬝ᵥ M *ᵥ y = (x ⬝ᵥ M *ᵥ x) / (x ⬝ᵥ x) := by
    intro x hx
    have hpos : 0 < x ⬝ᵥ x := by
      rcases (dotProduct_self_nonneg x).lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.1 h.symm) hx
    set r := Real.sqrt (x ⬝ᵥ x)
    have hrpos : 0 < r := Real.sqrt_pos.2 hpos
    have hrsq : r * r = x ⬝ᵥ x := Real.mul_self_sqrt hpos.le
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hrsq]
      field_simp
    · rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
        ← hrsq]
      field_simp
  rcases isEmpty_or_nonempty n with hn | hn
  · have h1 : IsEmpty {x : n → ℝ // x ⬝ᵥ x = 1} := ⟨fun x => by
      have := x.2; simp [dotProduct] at this⟩
    have h2 : IsEmpty {x : n → ℝ // x ≠ 0} := ⟨fun x => x.2 (Subsingleton.elim _ _)⟩
    unfold lamMin
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
  · have := nonempty_unitSphere (n := n)
    have hne : Nonempty {x : n → ℝ // x ≠ 0} := by
      obtain ⟨x⟩ := nonempty_unitSphere (n := n)
      exact ⟨⟨x.1, fun h => by have := x.2; rw [h] at this; simp at this⟩⟩
    have hbdd2 : BddBelow (Set.range fun x : {x : n → ℝ // x ≠ 0} =>
        (x.1 ⬝ᵥ M *ᵥ x.1) / (x.1 ⬝ᵥ x.1)) := by
      obtain ⟨c, hc⟩ := bddBelow_range_rayleigh M
      refine ⟨c, ?_⟩
      rintro _ ⟨x, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hnorm x.1 x.2
      show c ≤ (x.1 ⬝ᵥ M *ᵥ x.1) / (x.1 ⬝ᵥ x.1)
      rw [← hyx]
      exact hc ⟨⟨y, hy⟩, rfl⟩
    apply le_antisymm
    · refine le_ciInf fun x => ?_
      obtain ⟨y, hy, hyx⟩ := hnorm x.1 x.2
      rw [← hyx]
      exact lamMin_le M hy
    · refine le_ciInf fun x => ?_
      have hx0 : x.1 ≠ 0 := fun h => by have := x.2; rw [h] at this; simp at this
      refine (ciInf_le hbdd2 ⟨x.1, hx0⟩).trans_eq ?_
      simp [x.2]

/-! ### Lipschitz bounds (atlas `norm-lipschitz`) -/

/-- One half of the Lipschitz bound: `σ_min(A) ≤ σ_min(B) + ‖A - B‖_F`.
Ported from Prove2me solution `GaussianMatrix.sMin_lipschitz` (helper
`sMin_le_sMin_add_frobNorm`). Atlas `norm-lipschitz`. -/
theorem sigmaMin_le_sigmaMin_add_frobNorm (A B : Matrix m n ℝ) :
    sigmaMin A ≤ sigmaMin B + frobNorm (A - B) := by
  have hF : 0 ≤ frobNorm (A - B) := Real.sqrt_nonneg _
  rcases isEmpty_or_nonempty {x : n → ℝ // x ⬝ᵥ x = 1} with hE | hE
  · unfold sigmaMin
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
    linarith
  · rw [← sub_le_iff_le_add]
    unfold sigmaMin
    refine le_ciInf fun x => ?_
    have h1 := ciInf_le (bddBelow_range_sqrt_mulVec A) x
    have h2 : Real.sqrt ((A *ᵥ x.1) ⬝ᵥ (A *ᵥ x.1)) ≤ Real.sqrt ((B *ᵥ x.1) ⬝ᵥ (B *ᵥ x.1)) +
        Real.sqrt (((A - B) *ᵥ x.1) ⬝ᵥ ((A - B) *ᵥ x.1)) := by
      have hsplit : A *ᵥ x.1 = B *ᵥ x.1 + (A - B) *ᵥ x.1 := by
        rw [Matrix.sub_mulVec]; abel
      rw [hsplit]
      exact sqrt_dotProduct_add_le _ _
    have h3 : Real.sqrt (((A - B) *ᵥ x.1) ⬝ᵥ ((A - B) *ᵥ x.1)) ≤ frobNorm (A - B) := by
      have := mulVec_dotProduct_mulVec_le_frobSq_mul (A - B) x.1
      rw [x.2, mul_one] at this
      exact Real.sqrt_le_sqrt this
    linarith

/-- The smallest singular value is `1`-Lipschitz for the Frobenius norm:
`|σ_min(A) − σ_min(B)| ≤ ‖A − B‖_F`. Weyl's perturbation inequality, Frobenius form
(Vershynin 2012, proof of Cor. 5.35). Generalised from `Fin N × Fin n` to arbitrary finite index
types. Ported from Prove2me solution `GaussianMatrix.sMin_lipschitz`. Atlas `norm-lipschitz`. -/
theorem abs_sigmaMin_sub_sigmaMin_le_frobNorm (A B : Matrix m n ℝ) :
    |sigmaMin A - sigmaMin B| ≤ frobNorm (A - B) := by
  rw [abs_le]
  have h1 := sigmaMin_le_sigmaMin_add_frobNorm A B
  have h2 := sigmaMin_le_sigmaMin_add_frobNorm B A
  have h3 : frobNorm (B - A) = frobNorm (A - B) := by
    rw [← neg_sub, frobNorm_neg]
  constructor <;> linarith

/-- Reverse triangle inequality for the spectral norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖₂`.
Ported from Prove2me solution `GaussianMatrix.specNorm_lipschitz` (helper `specNorm_sub_le`).
Atlas `norm-lipschitz`. -/
theorem abs_specNorm_sub_specNorm_le [DecidableEq m] [DecidableEq n] (A B : Matrix m n ℝ) :
    |specNorm A - specNorm B| ≤ specNorm (A - B) :=
  abs_norm_sub_norm_le A B

/-- The spectral norm is `1`-Lipschitz for the Frobenius norm: `|‖A‖₂ − ‖B‖₂| ≤ ‖A − B‖_F`
(Vershynin 2012, proof of Cor. 5.35). Generalised from `Fin N × Fin n` to arbitrary finite index
types. Ported from Prove2me solution `GaussianMatrix.specNorm_lipschitz`.
Atlas `norm-lipschitz`. -/
theorem abs_specNorm_sub_specNorm_le_frobNorm [DecidableEq m] [DecidableEq n]
    (A B : Matrix m n ℝ) : |specNorm A - specNorm B| ≤ frobNorm (A - B) :=
  (abs_specNorm_sub_specNorm_le A B).trans (specNorm_le_frobNorm (A - B))


/-! ### Euclidean coordinates and nets -/

/-- `‖u‖ = √(∑ⱼ uⱼ²)` for a real Euclidean vector. Ported from Prove2me solution
`GaussianMatrix.gordon_upper` (helper `gu_norm_eq_sqrt`). Atlas `norm-lipschitz` (helper). -/
theorem norm_eq_sqrt_sum_sq {κ : Type*} [Fintype κ] (u : EuclideanSpace ℝ κ) :
    ‖u‖ = Real.sqrt (∑ j, u j ^ 2) := by
  rw [← EuclideanSpace.real_norm_sq_eq, Real.sqrt_sq (norm_nonneg _)]

/-- `‖v‖ = √(v ⬝ v)` for a real Euclidean vector. Ported from Prove2me solution
`GaussianMatrix.spectral_second_moment_bound` (helper `ssb_euclid_norm`).
Atlas `norm-lipschitz` (helper). -/
theorem norm_eq_sqrt_dotProduct (v : EuclideanSpace ℝ n) : ‖v‖ = Real.sqrt (v.ofLp ⬝ᵥ v.ofLp) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

/-- `‖0‖₂ = 0`. Atlas `norm-lipschitz` (helper). -/
theorem specNorm_zero [DecidableEq m] [DecidableEq n] : specNorm (0 : Matrix m n ℝ) = 0 :=
  norm_zero

open scoped RealInnerProductSpace in
/-- The bilinear form of a matrix in coordinates: `⟨v, A u⟩ = ∑ᵢⱼ vᵢ Aᵢⱼ uⱼ`.
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_inner_matrix`).
Atlas `norm-lipschitz` (helper). -/
theorem inner_toEuclideanLin_eq_sum {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (u : EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin N)) :
    ⟪v, (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A u⟫
      = ∑ i, ∑ j, v i * A i j * u j := by
  simp [PiLp.inner_apply, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

open scoped Matrix.Norms.L2Operator RealInnerProductSpace in
/-- Net argument for the spectral norm: if every pair of unit vectors `(u, v)` is `ε`-close to a
pair in the finite set `I` (whose second components are unit vectors), then
`(1 - 2ε)‖A‖₂ ≤ max_{(u,v) ∈ I} ⟨v, A u⟩`. Standard (Vershynin 2012, Lemma 5.4 in this form).
Ported from Prove2me solution `GaussianMatrix.gordon_upper` (helper `gu_net_bound`).
Atlas `norm-lipschitz` (helper of `gordon`, `spectral-second-moment`). -/
theorem one_sub_two_mul_mul_specNorm_le_iSup {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (I : Finset (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin N)))
    (hI : ∀ t ∈ I, ‖t.2‖ = 1)
    (hcov : ∀ (u : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin N)), ‖u‖ = 1 → ‖v‖ = 1 →
      ∃ t ∈ I, ‖u - t.1‖ ≤ ε ∧ ‖v - t.2‖ ≤ ε) :
    (1 - 2 * ε) * specNorm A ≤ ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j := by
  set Φ := (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) A with hΦ
  have hM : specNorm A = ‖Φ‖ := rfl
  set S := ⨆ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j with hS
  have hbdd : BddAbove (Set.range fun t : I => ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j) :=
    (Set.finite_range _).bddAbove
  set M := ‖Φ‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  rw [hM]
  rcases hM0.lt_or_eq with hMpos | hMzero
  · -- main case
    have claim : ∀ r : ℝ, 0 ≤ r → r < M → r - 2 * ε * M ≤ S := by
      intro r hr0 hrM
      obtain ⟨x, hx1, hrx⟩ := Φ.exists_lt_apply_of_lt_opNorm hrM
      have hx0 : x ≠ 0 := by
        rintro rfl
        simp at hrx
        linarith
      have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
      set u : EuclideanSpace ℝ (Fin n) := (‖x‖⁻¹ : ℝ) • x with hu
      have hu1 : ‖u‖ = 1 := norm_smul_inv_norm hx0
      have hΦu : ‖Φ x‖ ≤ ‖Φ u‖ := by
        rw [hu, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
        rw [le_inv_mul_iff₀ hxpos]
        exact mul_le_of_le_one_left (norm_nonneg _) hx1.le
      set w := Φ u with hw
      have hrw : r < ‖w‖ := lt_of_lt_of_le hrx hΦu
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hrw; linarith
      set v : EuclideanSpace ℝ (Fin N) := (‖w‖⁻¹ : ℝ) • w with hv
      have hv1 : ‖v‖ = 1 := norm_smul_inv_norm hw0
      have hvw : ⟪v, w⟫ = ‖w‖ := by
        rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq]
        have : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw0
        field_simp
      obtain ⟨t, ht, htu, htv⟩ := hcov u v hu1 hv1
      have ht2 : ‖t.2‖ = 1 := hI t ht
      have hwM : ‖w‖ ≤ M := by
        have := Φ.le_opNorm u; rw [hu1, mul_one] at this; exact this
      have hdecomp : Φ t.1 = w - Φ (u - t.1) := by
        rw [map_sub]; abel
      have hval : ∑ i, ∑ j, t.2 i * A i j * t.1 j = ⟪t.2, Φ t.1⟫ :=
        (inner_toEuclideanLin_eq_sum A t.1 t.2).symm
      have hval2 : ⟪t.2, Φ t.1⟫ = ⟪v, w⟫ - ⟪v - t.2, w⟫ - ⟪t.2, Φ (u - t.1)⟫ := by
        rw [hdecomp, inner_sub_right, inner_sub_left]; ring
      have hb1 : ⟪v - t.2, w⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        exact mul_le_mul htv hwM (norm_nonneg _) hε
      have hb2 : ⟪t.2, Φ (u - t.1)⟫ ≤ ε * M := by
        refine (real_inner_le_norm _ _).trans ?_
        rw [ht2, one_mul]
        refine (Φ.le_opNorm _).trans ?_
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right htu hM0
      have hle : ∑ i, ∑ j, t.2 i * A i j * t.1 j ≤ S :=
        le_ciSup hbdd (⟨t, ht⟩ : I)
      rw [hval, hval2, hvw] at hle
      linarith
    by_contra hcon
    push Not at hcon
    set r := (S + 2 * ε * M + M) / 2
    have h1 := claim (max r 0) (le_max_right _ _) (max_lt (by
      simp only [r]; nlinarith) hMpos)
    have : r ≤ max r 0 := le_max_left _ _
    simp only [r] at this
    nlinarith
  · -- `A = 0`
    have hA : Φ = 0 := norm_eq_zero.1 hMzero.symm
    have hA' : ∀ t : I, ∑ i, ∑ j, t.1.2 i * A i j * t.1.1 j = 0 := by
      intro t
      rw [← inner_toEuclideanLin_eq_sum, ← hΦ, hA]
      simp
    rw [← hMzero]
    simp only [mul_zero]
    rw [hS]
    simp only [hA', Real.iSup_const_zero, le_refl]

end NLAlib
