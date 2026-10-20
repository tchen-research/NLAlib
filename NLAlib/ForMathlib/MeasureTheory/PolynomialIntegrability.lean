import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul

/-!
# Finite polynomial moments form an algebra

Real random variables with every natural power integrable are closed under finite sums and
products. This elementary interface lets finite-dimensional matrix polynomials inherit
integrability directly from coordinate moments.
-/

noncomputable section

open scoped BigOperators

namespace MeasureTheory

/-- A real random variable has finite natural moments if every natural power is integrable. -/
def HasFiniteNatMoments {Ω : Type*} [MeasurableSpace Ω] (f : Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  ∀ p : ℕ, Integrable (fun ω => f ω ^ p) μ

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f g : Ω → ℝ}

/-- Every finite-natural-moment variable is integrable. -/
theorem HasFiniteNatMoments.integrable (hf : HasFiniteNatMoments f μ) : Integrable f μ := by
  simpa only [pow_one] using hf 1

/-- A power of a finite-natural-moment variable has finite natural moments. -/
theorem HasFiniteNatMoments.pow (hf : HasFiniteNatMoments f μ) (p : ℕ) :
    HasFiniteNatMoments (fun ω => f ω ^ p) μ := by
  intro q
  simpa only [← pow_mul] using hf (p * q)

private theorem integrable_mul_of_sq (hf : Integrable (fun ω => f ω ^ 2) μ)
    (hg : Integrable (fun ω => g ω ^ 2) μ)
    (hfmeas : AEStronglyMeasurable f μ) (hgmeas : AEStronglyMeasurable g μ) :
    Integrable (fun ω => f ω * g ω) μ := by
  exact ((memLp_two_iff_integrable_sq hfmeas).2 hf).integrable_mul
    ((memLp_two_iff_integrable_sq hgmeas).2 hg)

/-- Products preserve finiteness of all natural moments. -/
theorem HasFiniteNatMoments.mul (hf : HasFiniteNatMoments f μ)
    (hg : HasFiniteNatMoments g μ) : HasFiniteNatMoments (fun ω => f ω * g ω) μ := by
  intro p
  have hfp := hf.pow p
  have hgp := hg.pow p
  simpa only [mul_pow] using integrable_mul_of_sq (hfp 2) (hgp 2)
    hfp.integrable.aestronglyMeasurable hgp.integrable.aestronglyMeasurable

/-- Multiplication by a scalar preserves finiteness of all natural moments. -/
theorem HasFiniteNatMoments.const_mul (hf : HasFiniteNatMoments f μ) (c : ℝ) :
    HasFiniteNatMoments (fun ω => c * f ω) μ := by
  intro p
  simpa only [mul_pow] using (hf p).const_mul (c ^ p)

/-- Sums preserve finiteness of all natural moments. -/
theorem HasFiniteNatMoments.add (hf : HasFiniteNatMoments f μ)
    (hg : HasFiniteNatMoments g μ) : HasFiniteNatMoments (fun ω => f ω + g ω) μ := by
  intro p
  simp_rw [add_pow]
  apply integrable_finsetSum
  intro i _
  have hi := ((hf.pow i).mul (hg.pow (p - i))).integrable
  exact hi.mul_const _

/-- Constant variables have finite natural moments on a finite measure space. -/
theorem hasFiniteNatMoments_const [IsFiniteMeasure μ] (c : ℝ) :
    HasFiniteNatMoments (fun _ : Ω => c) μ := by
  intro p
  exact integrable_const _

/-- Finite sums preserve finiteness of all natural moments. -/
theorem HasFiniteNatMoments.sum [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι) {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, HasFiniteNatMoments (f i) μ) :
    HasFiniteNatMoments (fun ω => ∑ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using (hasFiniteNatMoments_const (μ := μ) 0)
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Finite products preserve finiteness of all natural moments. The empty product
is integrable because the measure is finite. -/
theorem HasFiniteNatMoments.prod [IsFiniteMeasure μ] {ι : Type*} (s : Finset ι)
    {f : ι → Ω → ℝ} (hf : ∀ i ∈ s, HasFiniteNatMoments (f i) μ) :
    HasFiniteNatMoments (fun ω => ∏ i ∈ s, f i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (hasFiniteNatMoments_const (μ := μ) 1)
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact ((hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Measure-preserving substitution preserves finiteness of all natural moments. -/
theorem HasFiniteNatMoments.comp_measurePreserving {Ω' : Type*} [MeasurableSpace Ω']
    {ν : Measure Ω'} (hf : HasFiniteNatMoments f μ) {T : Ω' → Ω}
    (hT : MeasurePreserving T ν μ) : HasFiniteNatMoments (fun ω => f (T ω)) ν := by
  intro p
  exact hT.integrable_comp_of_integrable (hf p)

/-- Every entry of a matrix power has finite natural moments when all entries do. -/
theorem HasFiniteNatMoments.matrix_pow_entry [IsFiniteMeasure μ] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, HasFiniteNatMoments (fun ω => A ω i j) μ) (p : ℕ) (i j : ι) :
    HasFiniteNatMoments (fun ω => (A ω ^ p) i j) μ := by
  induction p generalizing i j with
  | zero => simpa only [pow_zero] using hasFiniteNatMoments_const (μ := μ) ((1 : Matrix ι ι ℝ) i j)
  | succ p ih =>
      simp only [pow_succ, Matrix.mul_apply]
      exact HasFiniteNatMoments.sum Finset.univ fun a _ => (ih i a).mul (hA a j)

/-- Traces of matrix powers have finite natural moments when all entries do. -/
theorem HasFiniteNatMoments.trace_matrix_pow [IsFiniteMeasure μ] {ι : Type*}
    [Fintype ι] [DecidableEq ι] {A : Ω → Matrix ι ι ℝ}
    (hA : ∀ i j, HasFiniteNatMoments (fun ω => A ω i j) μ) (p : ℕ) :
    HasFiniteNatMoments (fun ω => (A ω ^ p).trace) μ := by
  exact HasFiniteNatMoments.sum Finset.univ fun a _ =>
    HasFiniteNatMoments.matrix_pow_entry hA p a a

end MeasureTheory
