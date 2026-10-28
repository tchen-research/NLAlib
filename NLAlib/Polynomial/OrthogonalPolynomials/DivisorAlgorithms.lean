import NLAlib.Polynomial.OrthogonalPolynomials.DivisorModification

/-!
# Linear and quadratic divisor algorithms

The small inverse-moment algorithm has exactly one coefficient in the linear
case and two in the quadratic case. Its lower-order initial systems are retained.
Source: Gautschi (2004), Algorithms 2.8--2.11.
-/

noncomputable section
open Polynomial Finset
namespace NLAlib
variable {𝕜 : Type*} [Field 𝕜]

/-- The one lower coefficient when the divisor system has size one; zero is
the totalization convention when no lower polynomial is requested. -/
def linearDivisorCoefficient (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (v : 𝕜[X]) (n : ℕ) : 𝕜 :=
  if h : 0 < min n v.natDegree then divisorModificationCoefficients L T v n ⟨0,h⟩ else 0

/-- The two computed coefficients multiplying `π_(n-1)` and `π_(n-2)`, in that
order; `(0,0)` is the totalization outside a system of size at least two. -/
def quadraticDivisorCoefficients (L T : 𝕜[X] →ₗ[𝕜] 𝕜) (v : 𝕜[X]) (n : ℕ) : 𝕜 × 𝕜 :=
  if h : 2 ≤ min n v.natDegree then
    (divisorModificationCoefficients L T v n ⟨1,by omega⟩,
      divisorModificationCoefficients L T v n ⟨0,by omega⟩) else (0,0)

/-- A size-one inverse-moment system gives the actual linear divisor update,
also covering the first step of a higher-degree divisor.
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_eq_linearDivisor
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ} (hsize : min n v.natDegree = 1)
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0) :
    monicOrthogonalPolynomial T n = monicOrthogonalPolynomial L n +
      C (linearDivisorCoefficient L T v n) * monicOrthogonalPolynomial L (n-1) := by
  have hs : 0 < min n v.natDegree := by omega
  let i0 : Fin (min n v.natDegree) := ⟨0,hs⟩
  have hu : (Finset.univ : Finset (Fin (min n v.natDegree))) = {i0} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff, Fin.ext_iff]
    have := i.isLt
    dsimp only [i0]
    omega
  have hbase : n-v.natDegree = n-1 := by omega
  have he := monicOrthogonalPolynomial_eq_divisorModification L T hv hTv hL hn
  rw [hu, Finset.sum_singleton] at he
  simpa only [i0, Nat.add_zero, hbase, linearDivisorCoefficient, dif_pos hs] using he

/-- A size-two inverse-moment system gives the advertised quadratic divisor
formula with the coefficients produced by the actual algorithm. Nonsingularity
has already been derived from the finite measure-functional hypotheses.
atlas: christoffel-uvarov-modification (partial) -/
theorem monicOrthogonalPolynomial_eq_quadraticDivisor
    (L T : 𝕜[X] →ₗ[𝕜] 𝕜) {v : 𝕜[X]} (hv : v ≠ 0)
    (hTv : ∀ p, T (v*p) = L p) {n : ℕ} (hsize : min n v.natDegree = 2)
    (hL : ∀ j ≤ n, hankelMomentDet L j ≠ 0) (hn : hankelMomentDet T n ≠ 0) :
    monicOrthogonalPolynomial T n = monicOrthogonalPolynomial L n +
      C (quadraticDivisorCoefficients L T v n).1 * monicOrthogonalPolynomial L (n-1) +
      C (quadraticDivisorCoefficients L T v n).2 * monicOrthogonalPolynomial L (n-2) := by
  have hs : 2 ≤ min n v.natDegree := hsize.ge
  let i0 : Fin (min n v.natDegree) := ⟨0,by omega⟩
  let i1 : Fin (min n v.natDegree) := ⟨1,by omega⟩
  have hne : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0,i1] at this
  have hu : (Finset.univ : Finset (Fin (min n v.natDegree))) = {i0,i1} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff, Fin.ext_iff]
    have := i.isLt
    dsimp only [i0,i1]
    omega
  have hbase : n-v.natDegree = n-2 := by omega
  have hnext : n-2+1 = n-1 := by omega
  have he := monicOrthogonalPolynomial_eq_divisorModification L T hv hTv hL hn
  rw [hu, Finset.sum_pair hne] at he
  simp only [i0, i1, Nat.add_zero, hbase, hnext] at he
  simp only [quadraticDivisorCoefficients, dif_pos hs]
  rw [he]
  ring

end NLAlib
