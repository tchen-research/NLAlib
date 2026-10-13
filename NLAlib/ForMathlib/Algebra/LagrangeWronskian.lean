import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.Tactic.Ring

/-!
# Finite Wronskian formula for Lagrange cardinals

Each cardinal-pair Wronskian is a scalar times a square of the node product omitting the pair.
Source: finite nodal sum-of-squares route to the peak-Jacobian certificate.
-/

noncomputable section

open Polynomial Finset

namespace NLAlib

/-- A Lagrange cardinal is its nodal weight times the node product omitting its node.
Source: Mathlib's product definition of `Lagrange.basis`. -/
theorem lagrange_basis_eq_weight_mul_prod {ι : Type*} [DecidableEq ι]
    {R : Type*} [Field R] (s : Finset ι) (v : ι → R) (i : ι) :
    Lagrange.basis s v i = C (Lagrange.nodalWeight s v i) * ∏ j ∈ s.erase i, (X - C (v j)) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, Lagrange.nodalWeight,
    prod_mul_distrib, ← map_prod]

/-- The Wronskian of two distinct cardinal polynomials is exactly a weighted node-distance
 times the square of their common omitted-node product.
Source: the finite nodal sum-of-squares identity for interval peak comparison. -/
theorem wronskian_lagrange_basis {ι : Type*} [DecidableEq ι]
    {R : Type*} [Field R] (s : Finset ι) (v : ι → R) {i j : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    Polynomial.wronskian (Lagrange.basis s v i) (Lagrange.basis s v j) =
      C (Lagrange.nodalWeight s v i * Lagrange.nodalWeight s v j * (v i - v j)) *
        (∏ k ∈ (s.erase i).erase j, (X - C (v k))) ^ 2 := by
  let P : R[X] := ∏ k ∈ (s.erase i).erase j, (X - C (v k))
  have hpi : (∏ k ∈ s.erase i, (X - C (v k))) = (X - C (v j)) * P := by
    exact (Finset.mul_prod_erase (s.erase i) (fun k => X - C (v k))
      (mem_erase.mpr ⟨Ne.symm hij, hj⟩)).symm
  have hpj : (∏ k ∈ s.erase j, (X - C (v k))) = (X - C (v i)) * P := by
    have h := Finset.mul_prod_erase (s.erase j) (fun k => (X : R[X]) - C (v k))
      (mem_erase.mpr ⟨hij, hi⟩)
    rw [erase_right_comm] at h
    exact h.symm
  rw [lagrange_basis_eq_weight_mul_prod, lagrange_basis_eq_weight_mul_prod, hpi, hpj]
  simp only [Polynomial.wronskian, derivative_mul, derivative_X, derivative_C,
    zero_mul, zero_add, sub_zero, one_mul, map_mul, map_sub]
  change _ = C (Lagrange.nodalWeight s v i) * C (Lagrange.nodalWeight s v j) *
    (C (v i) - C (v j)) * P ^ 2
  ring



/-- Constant factors multiply a polynomial Wronskian by their product.
Source: bilinearity and the derivative of a constant. -/
theorem wronskian_C_mul_C_mul {R : Type*} [CommRing R] (a b : R) (p q : R[X]) :
    Polynomial.wronskian (C a * p) (C b * q) = C (a * b) * Polynomial.wronskian p q := by
  simp only [Polynomial.wronskian, derivative_mul, derivative_C, zero_mul, zero_add, map_mul]
  ring

/-- A finite mixed sum of Lagrange cardinals has a cardinal-pair Wronskian expansion.
Source: finite bilinearity of the Wronskian. -/
theorem wronskian_lagrange_partition_expansion {ι : Type*} [DecidableEq ι]
    {R : Type*} [Field R] (s u v : Finset ι) (t : ι → R) (a b : ι → R)
    (hu : u ⊆ s) (hv : v ⊆ s) (hdis : Disjoint u v) :
    Polynomial.wronskian (∑ i ∈ u, C (a i) * Lagrange.basis s t i)
        (∑ j ∈ v, C (b j) * Lagrange.basis s t j) =
      ∑ i ∈ u, ∑ j ∈ v,
        C (a i * b j * Lagrange.nodalWeight s t i * Lagrange.nodalWeight s t j * (t i - t j)) *
          (∏ k ∈ (s.erase i).erase j, (X - C (t k))) ^ 2 := by
  rw [← Polynomial.wronskianBilin_apply, LinearMap.map_sum₂]
  apply sum_congr rfl
  intro i hi
  rw [map_sum]
  apply sum_congr rfl
  intro j hj
  rw [Polynomial.wronskianBilin_apply, wronskian_C_mul_C_mul,
    wronskian_lagrange_basis s t (hu hi) (hv hj) (by
      intro hij; exact Finset.disjoint_left.mp hdis hi (hij ▸ hj)), ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  ring

end NLAlib
