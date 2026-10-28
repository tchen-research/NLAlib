import NLAlib.Krylov.QueryModel.Program
import NLAlib.Krylov.QueryModel.ChebyshevArithmetic
import NLAlib.Matrix.Functions.PolynomialVectors
import Mathlib.LinearAlgebra.Complex.Module

/-!
# Chebyshev vectors through matrix and adjoint products

One real- or imaginary-part product takes two primitive queries. Two recurrences
through degree `M` therefore take exactly `4M` queries. The strategy is chosen
before receiving the matrix oracle, and includes the mode-zero normalization.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Matrix
open Polynomial
namespace NLAlib
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A query marked `false` applies the matrix; `true` applies its adjoint. -/
def matrixAdjointOracle (A : Matrix n n ℂ) (query : Bool × (n → ℂ)) : n → ℂ :=
  if query.1 then Aᴴ *ᵥ query.2 else A *ᵥ query.2

/-- One Hermitian-component product implemented by two charged primitive queries. -/
def hermitianPartProductProgram (imaginary : Bool) (x : n → ℂ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (n → ℂ) 2 :=
  .query (false,x) fun y => .query (true,x) fun z =>
    .pure (if imaginary then (-Complex.I / 2) • (y-z) else (1/2 : ℂ) • (y+z))

omit [DecidableEq n] in
/-- The two-query implementation is the native Hermitian component product. -/
theorem run_hermitianPartProductProgram (A : Matrix n n ℂ) (imaginary : Bool) (x : n → ℂ) :
    (hermitianPartProductProgram imaginary x).run (matrixAdjointOracle A) =
      (if imaginary then (imaginaryPart A : Matrix n n ℂ) else (realPart A : Matrix n n ℂ)) *ᵥ x := by
  cases imaginary <;>
    simp only [hermitianPartProductProgram, QueryProgram.run, matrixAdjointOracle,
      Bool.false_eq_true, ↓reduceIte, realPart_apply_coe, imaginaryPart_apply_coe,
      Matrix.star_eq_conjTranspose, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
  all_goals
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul,
      RCLike.real_smul_eq_coe_mul]
    norm_num
    <;> ring

/-- Query count for one component recurrence. -/
def hermitianPartChebyshevCost : ℕ → ℕ
  | 0 => 0
  | k+1 => 2 + hermitianPartChebyshevCost k

/-- Exactly two primitive queries are used for each new polynomial degree. -/
theorem hermitianPartChebyshevCost_eq (M : ℕ) : hermitianPartChebyshevCost M = 2*M := by
  induction M with
  | zero => rfl
  | succ M ih => rw [hermitianPartChebyshevCost, ih]; omega

/-- Shared recurrence table, with unnormalized vectors and an oracle-free final
normalization. Previous columns are retained without additional queries. -/
def hermitianPartChebyshevProgram (imaginary : Bool) (b : n → ℂ) :
    (M : ℕ) → QueryProgram (Bool × (n → ℂ)) (n → ℂ) (ℕ → n → ℂ) (hermitianPartChebyshevCost M)
  | 0 => .pure (fun _ => b)
  | k+1 => (hermitianPartChebyshevProgram imaginary b k).bind fun V =>
      (hermitianPartProductProgram imaginary (V k)).map fun response =>
        Function.update V (k+1) (if k=0 then response else (2:ℂ) • response - V (k-1))

private theorem chebyshev_succ_mulVec (H : Matrix n n ℂ) (b : n → ℂ) (j : ℕ) :
    (aeval H (Chebyshev.T ℂ ((j+1:ℕ):ℤ))) *ᵥ b =
      if j=0 then H *ᵥ ((aeval H (Chebyshev.T ℂ (j:ℤ))) *ᵥ b)
      else (2:ℂ) • (H *ᵥ ((aeval H (Chebyshev.T ℂ (j:ℤ))) *ᵥ b)) -
        (aeval H (Chebyshev.T ℂ ((j-1:ℕ):ℤ))) *ᵥ b := by
  by_cases hj : j=0
  · subst j; simp
  rw [if_neg hj, Nat.cast_add, Nat.cast_one, Chebyshev.T_add_one,
    map_sub, map_mul, map_mul, map_ofNat, aeval_X, Matrix.sub_mulVec]
  rw [show (j:ℤ)-1=((j-1:ℕ):ℤ) by omega]
  congr 1
  simp only [show (2 : Matrix n n ℂ) = (2:ℂ) • (1 : Matrix n n ℂ) by
    ext i l; simp [Matrix.ofNat_apply, Matrix.one_apply], Matrix.smul_mul,
    Matrix.one_mul, Matrix.smul_mulVec, Matrix.mulVec_mulVec]

/-- Every retained table entry is the actual polynomial vector for the native
real or imaginary Hermitian part, including the special degree-one step. -/
theorem run_hermitianPartChebyshevProgram (A : Matrix n n ℂ) (imaginary : Bool)
    (b : n → ℂ) (M j : ℕ) (hj : j ≤ M) :
    (hermitianPartChebyshevProgram imaginary b M).run (matrixAdjointOracle A) j =
      (aeval (if imaginary then (imaginaryPart A : Matrix n n ℂ) else (realPart A : Matrix n n ℂ))
        (Chebyshev.T ℂ (j:ℤ))) *ᵥ b := by
  induction M generalizing j with
  | zero =>
    have hj0 : j=0 := by omega
    subst j
    simp [hermitianPartChebyshevProgram, QueryProgram.run]
  | succ M ih =>
    rw [hermitianPartChebyshevProgram, QueryProgram.run_bind, QueryProgram.run_map,
      run_hermitianPartProductProgram]
    by_cases hlast : j=M+1
    · subst j
      rw [Function.update_self, chebyshev_succ_mulVec, ih M le_rfl, ih (M-1) (by omega)]
    · rw [Function.update_of_ne hlast]
      exact ih j (by omega)

/-- Normalizing the shared table computes every required polynomial column
without any more matrix or adjoint queries. -/
def hermitianPartChebyshevVectorProgram (imaginary : Bool) (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Matrix n (Fin (M+1)) ℂ)
      (hermitianPartChebyshevCost M) :=
  (hermitianPartChebyshevProgram imaginary b M).map fun V =>
    fun (r : n) (j : Fin (M+1)) => (normalizedChebyshevWeight j : ℂ) * V j.val r

/-- The actual component recurrence returns the exact native normalized columns. -/
theorem run_hermitianPartChebyshevVectorProgram (A : Matrix n n ℂ) (imaginary : Bool)
    (b : n → ℂ) (M : ℕ) :
    (hermitianPartChebyshevVectorProgram imaginary b M).run (matrixAdjointOracle A) =
      normalizedChebyshevVectorMatrix
        (if imaginary then (imaginaryPart A : Matrix n n ℂ) else (realPart A : Matrix n n ℂ)) b M := by
  rw [hermitianPartChebyshevVectorProgram, QueryProgram.run_map]
  ext r j
  rw [normalizedChebyshevVectorMatrix_apply]
  rw [run_hermitianPartChebyshevProgram A imaginary b M j (by have := j.isLt; omega)]

/-- The two actual normalized vector families computed by `4M` primitive products. -/
def normalMixedVectorProgram (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ)
      (Matrix n (Fin (M+1)) ℂ × Matrix n (Fin (M+1)) ℂ)
      (hermitianPartChebyshevCost M + hermitianPartChebyshevCost M) :=
  (hermitianPartChebyshevVectorProgram false b M).bind fun X =>
    (hermitianPartChebyshevVectorProgram true b M).map fun Y => (X,Y)

/-- Exact realization of both normalized vector matrices by the charged two-sided oracle.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem run_normalMixedVectorProgram (A : Matrix n n ℂ) (b : n → ℂ) (M : ℕ) :
    (normalMixedVectorProgram b M).run (matrixAdjointOracle A) =
      (normalizedChebyshevVectorMatrix (realPart A : Matrix n n ℂ) b M,
        normalizedChebyshevVectorMatrix (imaginaryPart A : Matrix n n ℂ) b M) := by
  simp only [normalMixedVectorProgram, QueryProgram.run_bind, QueryProgram.run_map,
    run_hermitianPartChebyshevVectorProgram, Bool.false_eq_true, ↓reduceIte]

/-- Compute the complete cross-Gram matrix by oracle-free finite scalar operations. -/
def normalMixedMomentProgram (b : n → ℂ) (M : ℕ) :
    QueryProgram (Bool × (n → ℂ)) (n → ℂ) (Matrix (Fin (M+1)) (Fin (M+1)) ℂ)
      (hermitianPartChebyshevCost M + hermitianPartChebyshevCost M) :=
  (normalMixedVectorProgram b M).map fun XY => XY.1ᴴ * XY.2

omit [Fintype n] [DecidableEq n] in
/-- Each actual component coordinate is evaluated by its counted scalar program,
for an arbitrary oracle, before any normal-matrix hypothesis is imposed. -/
theorem run_hermitianPartProductProgram_eq_scalar
    (oracle : Bool × (n → ℂ) → n → ℂ) (imaginary : Bool) (x : n → ℂ) (r : n) :
    ((hermitianPartProductProgram imaginary x).run oracle) r =
      (hermitianPartScalarProgram imaginary (oracle (false,x) r) (oracle (true,x) r)).run := by
  cases imaginary <;> rfl

omit [Fintype n] [DecidableEq n] in
/-- The actual next retained coordinate is exactly the counted recurrence update. -/
theorem run_hermitianPartChebyshevProgram_succ_eq_scalar
    (oracle : Bool × (n → ℂ) → n → ℂ) (imaginary : Bool) (b : n → ℂ) (k : ℕ) (r : n) :
    let V := (hermitianPartChebyshevProgram imaginary b k).run oracle
    let response := (hermitianPartProductProgram imaginary (V k)).run oracle
    ((hermitianPartChebyshevProgram imaginary b (k+1)).run oracle) (k+1) r =
      (chebyshevStepScalarProgram k (response r) (V (k-1) r)).run := by
  dsimp only
  rw [hermitianPartChebyshevProgram, QueryProgram.run_bind, QueryProgram.run_map,
    Function.update_self, run_chebyshevStepScalarProgram]
  by_cases hk : k=0 <;> simp [hk, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- Every actual normalized readout has the one-multiplication scalar realization. -/
theorem run_hermitianPartChebyshevVectorProgram_eq_scalar
    (oracle : Bool × (n → ℂ) → n → ℂ) (imaginary : Bool) (b : n → ℂ)
    (M : ℕ) (r : n) (j : Fin (M+1)) :
    ((hermitianPartChebyshevVectorProgram imaginary b M).run oracle) r j =
      (chebyshevNormalizeScalarProgram j
        (((hermitianPartChebyshevProgram imaginary b M).run oracle) j r)).run := by
  rw [hermitianPartChebyshevVectorProgram, QueryProgram.run_map]
  rfl

omit [DecidableEq n] in
/-- Every output entry uses the actual finite scalar cross-Gram computation. -/
theorem run_normalMixedMomentProgram_eq_scalar
    (oracle : Bool × (n → ℂ) → n → ℂ) (b : n → ℂ) (M : ℕ) (j k : Fin (M+1)) :
    let XY := (normalMixedVectorProgram b M).run oracle
    ((normalMixedMomentProgram b M).run oracle) j k =
      (crossGramScalarProgram XY.1 XY.2 j k).run := by
  dsimp only
  rw [normalMixedMomentProgram, QueryProgram.run_map]
  exact (run_crossGramScalarProgram _ _ j k).symm

/-- Scalar work evaluated on the actual response histories and retained tables
of the native query strategy. The preceding local bridges identify every
counted scalar expression with the corresponding actual program operation. -/
def normalMixedProgramScalarWork (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) : ℕ :=
  let V := fun imaginary k => (hermitianPartChebyshevProgram imaginary b k).run oracle
  let XY := (normalMixedVectorProgram b M).run oracle
  normalMixedScalarWork M
    (fun imaginary k => oracle (false,V imaginary k k))
    (fun imaginary k => oracle (true,V imaginary k k))
    (fun imaginary k => V imaginary k (k-1)) XY.1 XY.2

omit [DecidableEq n] in
/-- The actual native query strategy has the stated additional scalar work for
every oracle, including degree zero. Fixed normalized coefficients are inputs.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem normalMixedProgramScalarWork_le (b : n → ℂ) (M : ℕ)
    (oracle : Bool × (n → ℂ) → n → ℂ) :
    normalMixedProgramScalarWork b M oracle ≤ 13*Fintype.card n*(M+1)^2 := by
  unfold normalMixedProgramScalarWork
  exact (normalMixedScalarWork_le_budget _ _ _ _ _ _).trans (normalMixedArithmeticBudget_le _ _)

/-- Native normalized polynomial cross-Gram output, with no additional queries. -/
theorem run_normalMixedMomentProgram (A : Matrix n n ℂ) (b : n → ℂ) (M : ℕ) :
    (normalMixedMomentProgram b M).run (matrixAdjointOracle A) =
      (normalizedChebyshevVectorMatrix (realPart A : Matrix n n ℂ) b M)ᴴ *
        normalizedChebyshevVectorMatrix (imaginaryPart A : Matrix n n ℂ) b M := by
  rw [normalMixedMomentProgram, QueryProgram.run_map, run_normalMixedVectorProgram]

/-- The budget of the native two-sided recurrence is exactly `4M`, including `M=0`.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem normalMixedMomentProgram_queryCount (M : ℕ) :
    hermitianPartChebyshevCost M + hermitianPartChebyshevCost M = 4*M := by
  rw [hermitianPartChebyshevCost_eq]
  omega

end NLAlib
