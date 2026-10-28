import NLAlib.Matrix.Norms.Frobenius

/-!
# Unit-cost scalar expressions for query postprocessing

Previously computed scalar values and fixed coefficients are inputs. Each new
addition, subtraction, multiplication or conjugation costs one operation. The
expression tree records the actual finite computation, rather than attaching an
unrelated budget to an opaque output function.
-/

namespace NLAlib

/-- A finite scalar computation with previously available values as inputs. -/
inductive ScalarProgram (K : Type*)
  | input (value : K)
  | add (left right : ScalarProgram K)
  | sub (left right : ScalarProgram K)
  | mul (left right : ScalarProgram K)
  | conjugate (arg : ScalarProgram K)

namespace ScalarProgram
variable {K : Type*}

/-- Evaluate the stated primitive scalar operations. -/
def run [Add K] [Sub K] [Mul K] [Star K] : ScalarProgram K → K
  | .input x => x
  | .add p q => p.run + q.run
  | .sub p q => p.run - q.run
  | .mul p q => p.run * q.run
  | .conjugate p => star p.run

/-- The number of primitive operations in a scalar expression. -/
def cost : ScalarProgram K → ℕ
  | .input _ => 0
  | .add p q | .sub p q | .mul p q => p.cost + q.cost + 1
  | .conjugate p => p.cost + 1

end ScalarProgram

/-- A literal finite inner product, with one conjugation, multiplication and
addition for each coordinate. -/
def innerProductScalarProgram {K : Type*} [Zero K] :
    {k : ℕ} → (Fin k → K) → (Fin k → K) → ScalarProgram K
  | 0, _, _ => .input 0
  | _k+1, x, y => .add (.mul (.conjugate (.input (x 0))) (.input (y 0)))
      (innerProductScalarProgram (Fin.tail x) (Fin.tail y))

/-- The finite scalar program evaluates to the native Hermitian pairing. -/
theorem run_innerProductScalarProgram {K : Type*} [Ring K] [Star K]
    {k : ℕ} (x y : Fin k → K) :
    (innerProductScalarProgram x y).run = star x ⬝ᵥ y := by
  induction k with
  | zero => simp [innerProductScalarProgram, ScalarProgram.run, dotProduct]
  | succ k ih =>
    simp only [innerProductScalarProgram, ScalarProgram.run, ih, dotProduct, Pi.star_apply]
    rw [Fin.sum_univ_succ]
    rfl

/-- The native inner-product evaluation uses exactly three operations per coordinate. -/
theorem cost_innerProductScalarProgram {K : Type*} [Zero K] {k : ℕ} (x y : Fin k → K) :
    (innerProductScalarProgram x y).cost = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [innerProductScalarProgram, ScalarProgram.cost, ih]; omega

end NLAlib
