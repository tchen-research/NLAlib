import NLAlib.Matrix.Functions.OddPolarIteration

/-! # Counted Horner evaluation for polynomial polar updates

Only full matrix products are counted. Scalar multiplications, additions,
and supplied scalar coefficient computation are outside this cost model.
The first scalar-matrix multiplication in Horner is evaluated without a
matrix product. Source: Polar Express, §2 and Appendix E.
-/
noncomputable section
open Finset
open scoped Matrix
namespace NLAlib
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- A computed value together with the products used by its actual recursive
evaluation. -/
structure MatrixProductResult (α : Type*) where
  /-- The computed result. -/
  value : α
  /-- Number of full matrix multiplications; scalar operations are free. -/
  products : ℕ

/-- Horner evaluation, omitting multiplication of `S` by the leading scalar
matrix. Its degree-one base case therefore has no matrix products. -/
def polarGramHorner : ℕ → (ℕ → ℝ) → Matrix n n ℂ → MatrixProductResult (Matrix n n ℂ)
  | 0, a, _ => ⟨a 0 • 1, 0⟩
  | 1, a, S => ⟨a 0 • 1 + a 1 • S, 0⟩
  | q + 2, a, S =>
    let tail := polarGramHorner (q + 1) (fun j => a (j + 1)) S
    ⟨a 0 • 1 + S * tail.value, tail.products + 1⟩

/-- The literal Horner recursion evaluates the supplied Gram polynomial. -/
theorem polarGramHorner_value (q : ℕ) (a : ℕ → ℝ) (S : Matrix n n ℂ) :
    (polarGramHorner q a S).value = ∑ j ∈ range (q + 1), a j • S ^ j := by
  induction q using Nat.twoStepInduction generalizing a with
  | zero => simp [polarGramHorner]
  | one => simp [polarGramHorner, Finset.sum_range_succ]
  | more q _ ih =>
    conv_rhs => rw [Finset.sum_range_succ']
    rw [polarGramHorner, ih]
    simp only [pow_zero, Matrix.mul_sum, Matrix.mul_smul, ← pow_succ']
    rw [add_comm]

/-- A degree-`q+1` Gram polynomial uses exactly `q` full matrix products. -/
theorem polarGramHorner_products (q : ℕ) (a : ℕ → ℝ) (S : Matrix n n ℂ) :
    (polarGramHorner (q + 1) a S).products = q := by
  induction q generalizing a with
  | zero => rfl
  | succ q ih => simp only [polarGramHorner, ih]

/-- Actual odd update evaluation: one Gram product, the Horner calls, and
one final multiplication by the rectangular input. -/
def polarPolynomialHorner (q : ℕ) (a : ℕ → ℝ) (X : Matrix m n ℂ) :
    MatrixProductResult (Matrix m n ℂ) :=
  let gram := Xᴴ * X
  let h := polarGramHorner q a gram
  ⟨X * h.value, h.products + 2⟩

/-- The counted implementation computes the advertised matrix update exactly.
Source: Polar Express, §2, equation (6), and Appendix E.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem polarPolynomialHorner_value (q : ℕ) (a : ℕ → ℝ) (X : Matrix m n ℂ) :
    (polarPolynomialHorner q a X).value = oddMatrixUpdate q a X := by
  simp only [polarPolynomialHorner, polarGramHorner_value, oddMatrixUpdate,
    Matrix.mul_sum, Matrix.mul_smul]

/-- For positive `q`, the actual update implementation uses exactly `q+1`
matrix products; no products are attributed to scalar coefficients. -/
theorem polarPolynomialHorner_products (q : ℕ) (a : ℕ → ℝ) (X : Matrix m n ℂ) :
    (polarPolynomialHorner (q + 1) a X).products = (q + 1) + 1 := by
  simp only [polarPolynomialHorner, polarGramHorner_products]

/-- The counted staged algorithm calls the actual Horner update recursively. -/
def polarPolynomialHornerIterate (q : ℕ) (a : ℕ → ℕ → ℝ) (A : Matrix m n ℂ) :
    ℕ → MatrixProductResult (Matrix m n ℂ)
  | 0 => ⟨A, 0⟩
  | k + 1 =>
    let previous := polarPolynomialHornerIterate q a A k
    let next := polarPolynomialHorner q (a k) previous.value
    ⟨next.value, previous.products + next.products⟩

/-- Exact realization of the complete staged matrix iteration by Horner calls. -/
theorem polarPolynomialHornerIterate_value (q : ℕ) (a : ℕ → ℕ → ℝ)
    (A : Matrix m n ℂ) (k : ℕ) :
    (polarPolynomialHornerIterate q a A k).value = oddMatrixIterate q a A k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [polarPolynomialHornerIterate, polarPolynomialHorner_value, ih, oddMatrixIterate]

/-- The source's `(q+1)T` matrix-product guarantee, attached to the implemented
Horner composition rather than an independent numerical count.
Source: Polar Express, §2 and Appendix E.
atlas: polar-minimax-polynomial-iteration (partial) -/
theorem polarPolynomialHornerIterate_products (q : ℕ) (a : ℕ → ℕ → ℝ)
    (A : Matrix m n ℂ) (k : ℕ) :
    (polarPolynomialHornerIterate (q + 1) a A k).products = ((q + 1) + 1) * k := by
  induction k with
  | zero => simp [polarPolynomialHornerIterate]
  | succ k ih =>
    simp only [polarPolynomialHornerIterate, polarPolynomialHorner_products, ih]
    ring

end NLAlib
