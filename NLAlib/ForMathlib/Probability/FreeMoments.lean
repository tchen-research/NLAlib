import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Algebra.FreeAlgebra
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.InsertIdx
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Chain

/-!
# Algebraic freeness determines all joint polynomial moments

The centered alternating-polynomial definition is the usual algebraic
freeness of a family of generated unital algebras. Normalization and matching
one-variable moments determine every ordered joint polynomial expectation.
The proof merges equal adjacent colors and expands the genuinely centered
alternating product; it assumes no joint-moment or representation equality.
The scalar ring may be any commutative ring and the ambient algebras may be
noncommutative. This is the generic algebraic transport input for free models.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical
namespace NoncommutativeProbability
variable {K A B ι : Type*} [CommRing K] [Ring A] [Ring B] [Algebra K A] [Algebra K B]

/-- Polynomial form of algebraic freeness: every nonempty centered alternating product vanishes. -/
def IsFreeFamily (φ : A →ₗ[K] K) (X : ι → A) : Prop :=
  ∀ (m : ℕ) (_hm : 0<m) (color : Fin m → ι),
    (List.ofFn color).IsChain (· ≠ ·) → ∀ P : Fin m → Polynomial K,
      (∀ j, φ (Polynomial.aeval (X (color j)) (P j))=0) →
        φ ((List.ofFn fun j => Polynomial.aeval (X (color j)) (P j)).prod)=0

/-- The actual ordered product of a list of colored one-variable polynomials. -/
def polynomialWordProduct (X : ι → A) (l : List (ι×Polynomial K)) : A :=
  (l.map fun u => Polynomial.aeval (X u.1) u.2).prod

/-- The actual scalar expectation of the ordered colored polynomial product. -/
def polynomialWordMoment (φ : A →ₗ[K] K) (X : ι → A) (l : List (ι×Polynomial K)) : K :=
  φ (polynomialWordProduct X l)

/-- Adjacent one-variable polynomials in the same actual generator merge by multiplication. -/
theorem polynomialWordProduct_merge (X : ι → A) (l r : List (ι×Polynomial K))
    (i : ι) (P Q : Polynomial K) :
    polynomialWordProduct X (l++(i,P)::(i,Q)::r)=
      polynomialWordProduct X (l++(i,P*Q)::r) := by
  simp only [polynomialWordProduct,List.map_append,List.map_cons,List.prod_append,
    List.prod_cons,map_mul,mul_assoc]

/-- A genuinely constant polynomial contributes its scalar factor and removes that position from the ordered moment. -/
theorem polynomialWordMoment_constant (φ : A →ₗ[K] K) (X : ι → A)
    (l : List (ι×Polynomial K)) (j : ℕ) (hj : j<l.length) (c : K)
    (hc : (l[j]).2=Polynomial.C c) :
    polynomialWordMoment φ X l=c*polynomialWordMoment φ X (l.eraseIdx j) := by
  let ev : ι×Polynomial K → A := fun u => Polynomial.aeval (X u.1) u.2
  have he : ev (l[j])=algebraMap K A c := by simp [ev,hc]
  have hh := List.mul_prod_eraseIdx (l := l.map ev) (i := j)
    (by simpa only [List.length_map] using hj) (fun a ha => by
      rw [List.getElem_map,he]
      exact Algebra.commutes c a)
  rw [List.eraseIdx_map] at hh
  have hp : polynomialWordProduct X l=c•polynomialWordProduct X (l.eraseIdx j) := by
    change (l.map ev).prod=c•((l.eraseIdx j).map ev).prod
    rw [← hh,List.getElem_map,he,Algebra.smul_def]
  unfold polynomialWordMoment
  rw [hp,map_smul,smul_eq_mul]

/-- The actual polynomial-product expectation, bundled as a multilinear map in its ordered polynomial arguments. -/
def polynomialProductMoment (φ : A →ₗ[K] K) (X : ι → A) {m : ℕ}
    (color : Fin m → ι) : MultilinearMap K (fun _ : Fin m => Polynomial K) K :=
  φ.compMultilinearMap ((MultilinearMap.mkPiAlgebraFin K m A).compLinearMap
    (fun j => (Polynomial.aeval (X (color j))).toLinearMap))

/-- The multilinear polynomial-product moment is the literal ordered colored-word moment. -/
theorem polynomialProductMoment_apply (φ : A →ₗ[K] K) (X : ι → A) {m : ℕ}
    (color : Fin m → ι) (P : Fin m → Polynomial K) :
    polynomialProductMoment φ X color P=
      polynomialWordMoment φ X (List.ofFn fun j => (color j,P j)) := by
  change φ ((List.ofFn fun j => Polynomial.aeval (X (color j)) (P j)).prod)=_
  simp only [polynomialWordMoment,polynomialWordProduct,List.map_ofFn,Function.comp_def]

/-- Freeness and the genuine one-variable polynomial moments determine all ordered mixed moments. -/
theorem polynomialWordMoment_eq_of_free
    (φ : A →ₗ[K] K) (ψ : B →ₗ[K] K) (X : ι → A) (Y : ι → B)
    (hφ : φ 1=1) (hψ : ψ 1=1) (hX : IsFreeFamily φ X) (hY : IsFreeFamily ψ Y)
    (hLaw : ∀ (i : ι) (P : Polynomial K), φ (Polynomial.aeval (X i) P)=ψ (Polynomial.aeval (Y i) P))
    (l : List (ι×Polynomial K)) :
    polynomialWordMoment φ X l=polynomialWordMoment ψ Y l := by
  have hall (n : ℕ) : ∀ l : List (ι×Polynomial K), l.length=n →
      polynomialWordMoment φ X l=polynomialWordMoment ψ Y l := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hlen
      by_cases hn : n=0
      · have hl : l=[] := List.length_eq_zero_iff.mp (hlen.trans hn)
        subst l
        simp only [polynomialWordMoment,polynomialWordProduct,List.map_nil,List.prod_nil,hφ,hψ]
      have hnpos : 0<n := Nat.pos_of_ne_zero hn
      by_cases hchain : l.IsChain (fun u v => u.1≠v.1)
      · let color : Fin l.length → ι := fun j => (l.get j).1
        let P : Fin l.length → Polynomial K := fun j => (l.get j).2
        let c : Fin l.length → K := fun j => φ (Polynomial.aeval (X (color j)) (P j))
        let Pc : Fin l.length → Polynomial K := fun j => P j-Polynomial.C (c j)
        let C : Fin l.length → Polynomial K := fun j => Polynomial.C (c j)
        let D := polynomialProductMoment φ X color-polynomialProductMoment ψ Y color
        have hcolor : (List.ofFn color).IsChain (· ≠ ·) := by
          apply List.isChain_ofFn.mpr
          intro j hj
          exact (List.isChain_iff_getElem.mp hchain) j hj
        have hcenterX (j : Fin l.length) : φ (Polynomial.aeval (X (color j)) (Pc j))=0 := by
          simp [Pc,c,map_sub,Algebra.algebraMap_eq_smul_one,map_smul,hφ,smul_eq_mul]
        have hcenterY (j : Fin l.length) : ψ (Polynomial.aeval (Y (color j)) (Pc j))=0 := by
          simp [Pc,c,map_sub,Algebra.algebraMap_eq_smul_one,map_smul,hψ,smul_eq_mul,hLaw]
        have hcenter : D Pc=0 := by
          change φ ((List.ofFn fun j => Polynomial.aeval (X (color j)) (Pc j)).prod)-
            ψ ((List.ofFn fun j => Polynomial.aeval (Y (color j)) (Pc j)).prod)=0
          rw [hX l.length (hlen ▸ hnpos) color hcolor Pc hcenterX,
            hY l.length (hlen ▸ hnpos) color hcolor Pc hcenterY,sub_self]
        have hproper (s : Finset (Fin l.length)) (hs : s≠Finset.univ) :
            D (s.piecewise Pc C)=0 := by
          have hex : ∃ j : Fin l.length, j∉s := by
            by_contra h
            push Not at h
            exact hs (Finset.eq_univ_of_forall h)
          obtain ⟨j,hjs⟩ := hex
          let b : List (ι×Polynomial K) := List.ofFn fun j => (color j,s.piecewise Pc C j)
          have hj : (j : ℕ)<b.length := by simpa only [b,List.length_ofFn] using j.isLt
          have hb : (b[(j : ℕ)]).2=Polynomial.C (c j) := by
            simp [b,Finset.piecewise,hjs,C]
          have hbshort : (b.eraseIdx j).length<n := by
            have hbLen : b.length=n := by simp only [b,List.length_ofFn,hlen]
            rw [List.length_eraseIdx,if_pos hj,hbLen]
            omega
          have hh := ih (b.eraseIdx j).length hbshort (b.eraseIdx j) rfl
          change polynomialProductMoment φ X color (s.piecewise Pc C)-
            polynomialProductMoment ψ Y color (s.piecewise Pc C)=0
          rw [polynomialProductMoment_apply,polynomialProductMoment_apply]
          change polynomialWordMoment φ X b-polynomialWordMoment ψ Y b=0
          rw [polynomialWordMoment_constant φ X b j hj (c j) hb,
            polynomialWordMoment_constant ψ Y b j hj (c j) hb,hh,sub_self]
        have hdecomp : P=Pc+C := by
          funext j
          exact (sub_add_cancel (P j) (Polynomial.C (c j))).symm
        have hD : D P=0 := by
          rw [hdecomp,D.map_add_univ]
          rw [Finset.sum_eq_single Finset.univ]
          · simpa only [Finset.piecewise_univ] using hcenter
          · intro s hs hne
            exact hproper s hne
          · simp
        have hlist : (List.ofFn fun j => (color j,P j))=l := by
          change List.ofFn (fun j : Fin l.length => l.get j)=l
          exact List.ofFn_get l
        change polynomialProductMoment φ X color P-polynomialProductMoment ψ Y color P=0 at hD
        rw [polynomialProductMoment_apply,polynomialProductMoment_apply,hlist] at hD
        exact sub_eq_zero.mp hD
      · rw [List.isChain_iff_forall_rel_of_append_cons_cons] at hchain
        push Not at hchain
        obtain ⟨a,b,l₁,l₂,he,hab⟩ := hchain
        rcases a with ⟨i,P⟩
        rcases b with ⟨j,Q⟩
        have hij : i=j := hab
        subst j
        let l' := l₁++(i,P*Q)::l₂
        have hshort : l'.length<n := by simp only [he,List.length_append,List.length_cons] at hlen; dsimp [l']; simp only [List.length_append,List.length_cons]; omega
        have hh := ih l'.length hshort l' rfl
        rw [he]
        unfold polynomialWordMoment
        rw [polynomialWordProduct_merge,polynomialWordProduct_merge]
        exact hh
  exact hall l.length l rfl


/-- Genuine powers determine the actual one-variable polynomial expectation. -/
theorem aeval_moment_eq_of_powers (φ : A →ₗ[K] K) (ψ : B →ₗ[K] K)
    (x : A) (y : B) (hpow : ∀ n : ℕ, φ (x^n)=ψ (y^n)) (P : Polynomial K) :
    φ (Polynomial.aeval x P)=ψ (Polynomial.aeval y P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (· + ·) hP hQ
  | monomial n c =>
    simp only [Polynomial.aeval_monomial,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,
      one_mul,map_smul,hpow]

/-- Free families with the same one-variable moments have the same actual free-algebra polynomial expectations. -/
theorem freeAlgebra_lift_moment_eq_of_free
    (φ : A →ₗ[K] K) (ψ : B →ₗ[K] K) (X : ι → A) (Y : ι → B)
    (hφ : φ 1=1) (hψ : ψ 1=1) (hX : IsFreeFamily φ X) (hY : IsFreeFamily ψ Y)
    (hLaw : ∀ (i : ι) (P : Polynomial K), φ (Polynomial.aeval (X i) P)=ψ (Polynomial.aeval (Y i) P))
    (P : FreeAlgebra K ι) :
    φ (FreeAlgebra.lift K X P)=ψ (FreeAlgebra.lift K Y P) := by
  have hEvalX : FreeAlgebra.lift K X=
      (MonoidAlgebra.lift K A (FreeMonoid ι) (FreeMonoid.lift X)).comp
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := ι)).toAlgHom := by
    ext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hEvalY : FreeAlgebra.lift K Y=
      (MonoidAlgebra.lift K B (FreeMonoid ι) (FreeMonoid.lift Y)).comp
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := K) (X := ι)).toAlgHom := by
    ext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  have hword (w : FreeMonoid ι) : φ ((w.toList.map X).prod)=ψ ((w.toList.map Y).prod) := by
    have hh := polynomialWordMoment_eq_of_free φ ψ X Y hφ hψ hX hY hLaw
      (w.toList.map fun i => (i,Polynomial.X))
    simpa only [polynomialWordMoment,polynomialWordProduct,List.map_map,
      Function.comp_def,Polynomial.aeval_X] using hh
  rw [hEvalX,hEvalY,AlgHom.comp_apply,AlgHom.comp_apply]
  simp only [MonoidAlgebra.lift_apply,FreeMonoid.lift_apply]
  simp only [Finsupp.sum,map_sum,map_smul,hword]

end NoncommutativeProbability
