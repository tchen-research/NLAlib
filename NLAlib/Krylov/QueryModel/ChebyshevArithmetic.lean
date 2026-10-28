import NLAlib.Krylov.QueryModel.ScalarArithmetic
import NLAlib.Matrix.Functions.PolynomialVectors

/-!
# Scalar work in the two-sided Chebyshev recurrence

Fixed polynomial normalizations are available before the oracle is supplied.
The scalar programs below specify each vector update and the finite cross-Gram
evaluation. Their operation counts give an explicit quadratic work bound.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
variable {n : Type*} [Fintype n]

/-- Combine a matrix response and its adjoint response in one coordinate. -/
def hermitianPartScalarProgram (imaginary : Bool) (y z : ℂ) : ScalarProgram ℂ :=
  if imaginary then .mul (.input (-Complex.I/2)) (.sub (.input y) (.input z))
  else .mul (.input (1/2)) (.add (.input y) (.input z))

/-- Every coordinate of the Hermitian-part product uses two scalar operations. -/
theorem cost_hermitianPartScalarProgram (imaginary : Bool) (y z : ℂ) :
    (hermitianPartScalarProgram imaginary y z).cost = 2 := by
  cases imaginary <;> rfl

/-- The counted component combination is the one in the two-query program. -/
theorem run_hermitianPartScalarProgram (imaginary : Bool) (y z : ℂ) :
    (hermitianPartScalarProgram imaginary y z).run =
      if imaginary then (-Complex.I/2)*(y-z) else (1/2:ℂ)*(y+z) := by
  cases imaginary <;> rfl

/-- Scalar update of the shared Chebyshev recurrence. The degree-one step
retains the response; every later step multiplies by two and subtracts. -/
def chebyshevStepScalarProgram (k : ℕ) (response previous : ℂ) : ScalarProgram ℂ :=
  if k=0 then .input response
  else .sub (.mul (.input 2) (.input response)) (.input previous)

/-- Each recurrence-coordinate update uses at most two scalar operations. -/
theorem cost_chebyshevStepScalarProgram_le (k : ℕ) (response previous : ℂ) :
    (chebyshevStepScalarProgram k response previous).cost ≤ 2 := by
  by_cases hk : k=0 <;> simp [chebyshevStepScalarProgram, hk, ScalarProgram.cost]

/-- The counted recurrence update evaluates to the actual shared-table update. -/
theorem run_chebyshevStepScalarProgram (k : ℕ) (response previous : ℂ) :
    (chebyshevStepScalarProgram k response previous).run =
      if k=0 then response else 2*response-previous := by
  by_cases hk : k=0 <;> simp [chebyshevStepScalarProgram, hk, ScalarProgram.run]

/-- The normalization is a single multiplication by a fixed coefficient. -/
def chebyshevNormalizeScalarProgram (j : ℕ) (x : ℂ) : ScalarProgram ℂ :=
  .mul (.input (normalizedChebyshevWeight j : ℂ)) (.input x)

/-- A fixed normalized mode costs one multiplication per coordinate. -/
theorem cost_chebyshevNormalizeScalarProgram (j : ℕ) (x : ℂ) :
    (chebyshevNormalizeScalarProgram j x).cost = 1 := rfl

/-- The counted readout is the native normalized polynomial-vector coordinate. -/
theorem run_chebyshevNormalizeScalarProgram (j : ℕ) (x : ℂ) :
    (chebyshevNormalizeScalarProgram j x).run = (normalizedChebyshevWeight j : ℂ)*x := rfl

/-- Literal cross-Gram entry evaluation, using any fixed enumeration of rows. -/
def crossGramScalarProgram {p q : Type*} (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (j : p) (k : q) : ScalarProgram ℂ :=
  innerProductScalarProgram
    (fun r => X ((Fintype.equivFin n).symm r) j)
    (fun r => Y ((Fintype.equivFin n).symm r) k)

/-- The scalar program computes the native cross-Gram entry. -/
theorem run_crossGramScalarProgram {p q : Type*} (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (j : p) (k : q) : (crossGramScalarProgram X Y j k).run = (Xᴴ * Y) j k := by
  rw [crossGramScalarProgram, run_innerProductScalarProgram]
  simp only [dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact (Fintype.equivFin n).symm.sum_comp (fun r => star (X r j) * Y r k)

/-- Each cross-Gram entry uses exactly three operations per row. -/
theorem cost_crossGramScalarProgram {p q : Type*} (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (j : p) (k : q) : (crossGramScalarProgram X Y j k).cost = 3*Fintype.card n :=
  cost_innerProductScalarProgram _ _

/-- Total operation count of all the actual finite cross-Gram entry programs. -/
theorem sum_cost_crossGramScalarProgram (M : ℕ)
    (X Y : Matrix n (Fin (M+1)) ℂ) :
    (∑ j, ∑ k, (crossGramScalarProgram X Y j k).cost) =
      3*Fintype.card n*(M+1)^2 := by
  simp only [cost_crossGramScalarProgram, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]
  ring

/-- A uniform budget: four scalar operations per recurrence coordinate, one
normalizing multiplication per retained entry, and the complete cross-Gram. -/
def normalMixedArithmeticBudget (n M : ℕ) : ℕ :=
  8*n*M + 2*n*(M+1) + 3*n*(M+1)^2

/-- Sum the actual scalar-program costs over both recurrence histories, both
normalizing readouts and every cross-Gram entry. The histories contain the
already obtained primitive responses; this accounting holds for every oracle. -/
def normalMixedScalarWork (M : ℕ)
    (matrixResponse adjointResponse previous : Bool → Fin M → n → ℂ)
    (X Y : Matrix n (Fin (M+1)) ℂ) : ℕ :=
  (∑ imaginary : Bool, ∑ k : Fin M, ∑ r : n,
    ((hermitianPartScalarProgram imaginary (matrixResponse imaginary k r)
      (adjointResponse imaginary k r)).cost +
      (chebyshevStepScalarProgram k
        (hermitianPartScalarProgram imaginary (matrixResponse imaginary k r)
          (adjointResponse imaginary k r)).run (previous imaginary k r)).cost)) +
    (∑ j : Fin (M+1), ∑ r : n,
      ((chebyshevNormalizeScalarProgram j (X r j)).cost +
        (chebyshevNormalizeScalarProgram j (Y r j)).cost)) +
    ∑ j, ∑ k, (crossGramScalarProgram X Y j k).cost

/-- Every possible response history meets the explicit arithmetic budget.
No spectral identities or idealized free matrix products are used here. -/
theorem normalMixedScalarWork_le_budget (M : ℕ)
    (matrixResponse adjointResponse previous : Bool → Fin M → n → ℂ)
    (X Y : Matrix n (Fin (M+1)) ℂ) :
    normalMixedScalarWork M matrixResponse adjointResponse previous X Y ≤
      normalMixedArithmeticBudget (Fintype.card n) M := by
  have hstep (imaginary : Bool) (k : Fin M) (r : n) :
      (hermitianPartScalarProgram imaginary (matrixResponse imaginary k r)
        (adjointResponse imaginary k r)).cost +
        (chebyshevStepScalarProgram k
          (hermitianPartScalarProgram imaginary (matrixResponse imaginary k r)
            (adjointResponse imaginary k r)).run (previous imaginary k r)).cost ≤ 4 := by
    rw [cost_hermitianPartScalarProgram]
    have := cost_chebyshevStepScalarProgram_le k
      (hermitianPartScalarProgram imaginary (matrixResponse imaginary k r)
        (adjointResponse imaginary k r)).run (previous imaginary k r)
    omega
  unfold normalMixedScalarWork
  calc
    _ ≤ (∑ _ : Bool, ∑ _ : Fin M, ∑ _ : n, 4) +
        (∑ _ : Fin (M+1), ∑ _ : n, (1+1)) + 3*Fintype.card n*(M+1)^2 := by
      gcongr
      · exact hstep _ _ _
      · simp [cost_chebyshevNormalizeScalarProgram]
      · simp [cost_chebyshevNormalizeScalarProgram]
      · exact (sum_cost_crossGramScalarProgram M X Y).le
    _ = normalMixedArithmeticBudget (Fintype.card n) M := by
      simp [normalMixedArithmeticBudget, Nat.mul_add]
      ring

/-- The explicit unit-cost budget is quadratic in degree and linear in dimension.
atlas: normal-matrix-mixed-chebyshev-moments (partial) -/
theorem normalMixedArithmeticBudget_le (n M : ℕ) :
    normalMixedArithmeticBudget n M ≤ 13*n*(M+1)^2 := by
  unfold normalMixedArithmeticBudget
  nlinarith [Nat.zero_le (10*n*M*M), Nat.zero_le (10*n*M), Nat.zero_le (8*n)]

end NLAlib
