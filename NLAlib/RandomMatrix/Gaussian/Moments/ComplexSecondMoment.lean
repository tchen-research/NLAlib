import NLAlib.RandomMatrix.Gaussian.Basic.ComplexGaussianMatrix
import NLAlib.Probability.Gaussian.Moments.ComplexLinear
import NLAlib.Matrix.Measurability.GramPseudoinverse

/-!
# Native complex Gaussian sandwiched moments

Each entry of `S G T` is one complex Gaussian linear form in the full
independent entry family. Its exact squared-modulus moment factors into
the squared Frobenius norms of `S` and `T`, with coefficient two for the
circular convention used here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix
namespace NLAlib
variable {a b m n : Type*} [Fintype a] [Fintype b] [Fintype m] [Fintype n]

omit [Fintype a] [Fintype b] in
private theorem mul_entry_eq_dotProduct_flat (S : Matrix a m ℂ) (T : Matrix n b ℂ)
    (G : Matrix m n ℂ) (i : a) (j : b) :
    (S*G*T) i j=(fun ij : m × n => S i ij.1*T ij.2 j) ⬝ᵥ (fun ij => G ij.1 ij.2) := by
  have he : (S*G*T) i j=∑ k,∑ l,S i k*G k l*T l j := by
    simp only [Matrix.mul_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he]
  simp only [dotProduct,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

private theorem hasLaw_uncurry_circularComplexGaussianMatrix :
    HasLaw (fun G : Matrix m n ℂ => fun ij : m × n => G ij.1 ij.2)
      (circularComplexGaussianVector (m × n)) (circularComplexGaussianMatrix m n) :=
  ⟨(by fun_prop : Measurable _).aemeasurable,circularComplexGaussianMatrix_map_uncurry⟩

omit [Fintype a] [Fintype b] in
/-- Every deterministic sandwiched complex Gaussian matrix entry is
integrable and has zero complex mean. -/
theorem integrable_and_integral_mul_circularComplexGaussianMatrix_mul_entry
    (S : Matrix a m ℂ) (T : Matrix n b ℂ) (i : a) (j : b) :
    Integrable (fun G : Matrix m n ℂ => (S*G*T) i j) (circularComplexGaussianMatrix m n) ∧
      ∫ G, (S*G*T) i j ∂circularComplexGaussianMatrix m n=0 := by
  let c : m × n → ℂ := fun ij => S i ij.1*T ij.2 j
  obtain ⟨hi,hv⟩ := integrable_and_integral_dotProduct_circularComplexGaussianVector c
  have hm : AEStronglyMeasurable (fun z : m × n → ℂ => c ⬝ᵥ z)
      (circularComplexGaussianVector (m × n)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hG := hasLaw_uncurry_circularComplexGaussianMatrix (m := m) (n := n)
  simp_rw [mul_entry_eq_dotProduct_flat]
  constructor
  · rw [← hG.map_eq] at hi
    exact hi.comp_aemeasurable hG.aemeasurable
  · exact (hG.integral_comp hm).trans hv

omit [Fintype a] [Fintype b] in
/-- Every squared entry modulus of a deterministic sandwiched native
complex Gaussian matrix has its exact second moment. -/
theorem integrable_and_integral_normSq_mul_circularComplexGaussianMatrix_mul_entry
    (S : Matrix a m ℂ) (T : Matrix n b ℂ) (i : a) (j : b) :
    Integrable (fun G : Matrix m n ℂ => Complex.normSq ((S*G*T) i j)) (circularComplexGaussianMatrix m n) ∧
      ∫ G, Complex.normSq ((S*G*T) i j) ∂circularComplexGaussianMatrix m n=
        2*∑ ij : m × n,Complex.normSq (S i ij.1*T ij.2 j) := by
  let c : m × n → ℂ := fun ij => S i ij.1*T ij.2 j
  obtain ⟨hi,hv⟩ := integrable_and_integral_normSq_dotProduct_circularComplexGaussianVector c
  have hm : AEStronglyMeasurable (fun z : m × n → ℂ => Complex.normSq (c ⬝ᵥ z))
      (circularComplexGaussianVector (m × n)) := (by fun_prop : Measurable _).aestronglyMeasurable
  have hG := hasLaw_uncurry_circularComplexGaussianMatrix (m := m) (n := n)
  simp_rw [mul_entry_eq_dotProduct_flat]
  constructor
  · rw [← hG.map_eq] at hi
    exact hi.comp_aemeasurable hG.aemeasurable
  · exact (hG.integral_comp hm).trans hv

open scoped Matrix.Norms.L2Operator in
/-- The exact native complex Gaussian Frobenius sandwich identity. Its
coefficient is two because both real components of every entry have variance
one. All dimensions may be zero. -/
theorem integrable_and_integral_frobSq_mul_circularComplexGaussianMatrix_mul
    (S : Matrix a m ℂ) (T : Matrix n b ℂ) :
    Integrable (fun G : Matrix m n ℂ => frobSq (S*G*T)) (circularComplexGaussianMatrix m n) ∧
      ∫ G, frobSq (S*G*T) ∂circularComplexGaussianMatrix m n=2*frobSq S*frobSq T := by
  have hentry (i : a) (j : b) :=
    integrable_and_integral_normSq_mul_circularComplexGaussianMatrix_mul_entry S T i j
  have he (G : Matrix m n ℂ) : frobSq (S*G*T)=∑ i,∑ j,Complex.normSq ((S*G*T) i j) := by
    simp only [frobSq_eq_sum_norm_sq,Complex.normSq_eq_norm_sq]
  simp_rw [he]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hentry i j).1,?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hentry i j).1]
  simp_rw [integral_finsetSum _ fun j _ => (hentry _ j).1,(hentry _ _).2]
  have hc (i : a) (j : b) : 2*∑ ij : m × n,Complex.normSq (S i ij.1*T ij.2 j)=
      (2*∑ k,Complex.normSq (S i k))*(∑ l,Complex.normSq (T l j)) := by
    simp only [Fintype.sum_prod_type,Complex.normSq_mul]
    rw [mul_assoc,Finset.sum_mul_sum]
  simp_rw [hc]
  rw [frobSq_eq_sum_norm_sq,frobSq_eq_sum_norm_sq]
  simp only [← Complex.normSq_eq_norm_sq]
  have hT : (∑ j : b,∑ l : n,Complex.normSq (T l j))=∑ l : n,∑ j : b,Complex.normSq (T l j) :=
    Finset.sum_comm
  calc
    _ = (∑ i : a,2*∑ k : m,Complex.normSq (S i k))*(∑ j : b,∑ l : n,Complex.normSq (T l j)) := by
      rw [Finset.sum_mul_sum]
    _ = _ := by rw [← Finset.mul_sum,hT]

end NLAlib
