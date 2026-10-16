import NLAlib.Matrix.Structured.RadixTwoRoots

/-! # Even/odd Fourier splitting and correctness of radix-two recursion

The input permutation is an explicit finite equivalence. The two output
halves use periodicity and the half-length root identity, proving the actual
butterfly recursion computes the finite root-power sum.
Source: Golub–Van Loan, Matrix Computations, §1.4.
-/
noncomputable section
open Finset
namespace NLAlib.RadixTwoFFT

private theorem sum_even_odd {N : ℕ} {R : Type*} [AddCommMonoid R]
    (f : Fin (N + N) → R) :
    (∑ j, f j) = ∑ j : Fin N, (f (evenIndex j) + f (oddIndex j)) := by
  let e : Fin N × Fin 2 ≃ Fin (N + N) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_two N))
  have he := Fintype.sum_equiv e (fun j => f (e j)) f (fun _ => rfl)
  rw [← he, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  congr 1 <;> congr 1 <;> apply Fin.ext <;>
    simp [e, evenIndex, oddIndex, finProdFinEquiv, Nat.add_comm]

/-- The finite Fourier root-power sum at an arbitrary natural frequency. -/
def polynomialDFT {N : ℕ} (ζ : ℂ) (x : Fin N → ℂ) (k : ℕ) : ℂ :=
  ∑ j : Fin N, ζ ^ (j.val * k) * x j

/-- Exact even/odd splitting of a finite root-power sum, for any complex root. -/
theorem polynomialDFT_even_odd {N : ℕ} (ζ : ℂ) (x : Fin (N + N) → ℂ) (k : ℕ) :
    polynomialDFT ζ x k = polynomialDFT (ζ ^ 2) (fun j => x (evenIndex j)) k +
      ζ ^ k * polynomialDFT (ζ ^ 2) (fun j => x (oddIndex j)) k := by
  rw [polynomialDFT, sum_even_odd]
  simp only [polynomialDFT, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have he : ζ ^ ((2 * j.val) * k) = (ζ ^ 2) ^ (j.val * k) := by
    rw [← pow_mul]
    congr 1
    ring
  have ho : ζ ^ ((2 * j.val + 1) * k) = (ζ ^ 2) ^ (j.val * k) * ζ ^ k := by
    rw [show (2 * j.val + 1) * k = 2 * (j.val * k) + k by ring, pow_add, pow_mul]
  change ζ ^ ((2 * j.val) * k) * x (evenIndex j) +
    ζ ^ ((2 * j.val + 1) * k) * x (oddIndex j) = _
  rw [he, ho]
  ring

/-- Fourier root-power sums are periodic in frequency with the transform length. -/
theorem polynomialDFT_add_period {N : ℕ} {ζ : ℂ} (hζ : ζ ^ N = 1)
    (x : Fin N → ℂ) (k : ℕ) : polynomialDFT ζ x (k + N) = polynomialDFT ζ x k := by
  apply Finset.sum_congr rfl
  intro j _
  have hp : ζ ^ (j.val * N) = 1 := by rw [Nat.mul_comm, pow_mul, hζ, one_pow]
  rw [Nat.mul_add, pow_add, hp, mul_one]

/-- The literal recursive algorithm computes the finite Fourier root-power sum
under exactly its supplied-root identities. Concrete DFT roots are discharged
by `hasRootSchedule_standardRoot`.
Source: Golub–Van Loan, §1.4.
atlas: radix-two-fft-realization (partial) -/
theorem run_value_eq_polynomialDFT (s : ℕ) (ζ : ℂ) (x : Fin (size s) → ℂ)
    (hζ : HasRootSchedule s ζ) (k : Fin (size s)) :
    (run s ζ x).value k = polynomialDFT ζ x k.val := by
  induction s generalizing ζ with
  | zero =>
    change (Fin 1 → ℂ) at x
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    change x 0 = ∑ j : Fin 1, ζ ^ (j.val * 0) * x j
    simp
  | succ s ih =>
    change (Fin (size s + size s) → ℂ) at x
    change Fin (size s + size s) at k
    have hhalf : ζ ^ size s = -1 := hζ.1
    have hchild : HasRootSchedule s (ζ ^ 2) := hζ.2
    have hperiod : (ζ ^ 2) ^ size s = 1 := by
      rw [← pow_mul, Nat.mul_comm 2, pow_mul, hhalf]
      norm_num
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simp only [run, Fin.addCases_left, butterfly, Fin.val_castAdd]
      rw [ih _ _ hchild, ih _ _ hchild]
      exact (polynomialDFT_even_odd (N := size s) ζ x j.val).symm
    · simp only [run, Fin.addCases_right, butterfly, Fin.val_natAdd]
      rw [ih _ _ hchild, ih _ _ hchild]
      change polynomialDFT (ζ ^ 2) (fun j => x (evenIndex j)) j.val -
        ζ ^ j.val * polynomialDFT (ζ ^ 2) (fun j => x (oddIndex j)) j.val =
          polynomialDFT (N := size s + size s) ζ x (size s + j.val)
      rw [polynomialDFT_even_odd (N := size s) ζ x (size s + j.val)]
      rw [Nat.add_comm (size s), polynomialDFT_add_period hperiod,
        polynomialDFT_add_period hperiod, pow_add, hhalf]
      ring

end NLAlib.RadixTwoFFT
