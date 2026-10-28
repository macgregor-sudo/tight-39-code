module

public import QuadricRelations
public import MatrixRankSpecialization
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHilbertCharZero
open MvPolynomial Module
open scoped BigOperators

abbrev DegreeExp (n d : ℕ) := {a : Fin n →₀ ℕ // a.degree = d}
instance (n d : ℕ) : Finite (DegreeExp n d) := (Finsupp.finite_of_degree_eq d).to_subtype
instance (n d : ℕ) : Fintype (DegreeExp n d) := Fintype.ofFinite _

variable {R : Type*} [CommRing R]

def homogeneousSupported (n d : ℕ) :
    homogeneousSubmodule (Fin n) R d ≃ₗ[R]
      AddMonoidAlgebra.supported R R {a : Fin n →₀ ℕ | a.degree = d} where
  toFun p := ⟨p.val, by rw [← homogeneousSubmodule_eq_finsupp_supported]; exact p.property⟩
  invFun p := ⟨p.val, by rw [homogeneousSubmodule_eq_finsupp_supported]; exact p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficients (n d : ℕ) : homogeneousSubmodule (Fin n) R d ≃ₗ[R] (DegreeExp n d → R) :=
  (homogeneousSupported n d).trans
    ((AddMonoidAlgebra.supportedEquivFinsupp {a : Fin n →₀ ℕ | a.degree = d}).trans
      (Finsupp.linearEquivFunOnFinite R R (DegreeExp n d)))

@[simp] theorem coefficients_apply (n d : ℕ)
    (p : homogeneousSubmodule (Fin n) R d) (a : DegreeExp n d) :
    coefficients n d p a = p.val.coeff a.val := rfl

def monomialForm (n d : ℕ) (a : DegreeExp n d) : homogeneousSubmodule (Fin n) R d :=
  ⟨monomial a.val 1, isHomogeneous_monomial 1 a.property⟩

theorem span_monomialForm (n d : ℕ) :
    Submodule.span R (Set.range (monomialForm (R := R) n d)) = ⊤ := by
  let V := homogeneousSubmodule (Fin n) R d
  let T := Submodule.span R (Set.range (monomialForm (R := R) n d))
  have hmap : T.map V.subtype = V := by
    dsimp [T]
    rw [Submodule.map_span, ← Set.range_comp]
    change Submodule.span R (Set.range (fun a : DegreeExp n d => monomial a.val (1 : R))) = V
    have hset : Set.range (fun a : DegreeExp n d => monomial a.val (1 : R)) =
        (fun a : Fin n →₀ ℕ => monomial a (1 : R)) '' {a | a.degree = d} := by
      ext p
      constructor
      · rintro ⟨a, rfl⟩; exact ⟨a.val, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩; exact ⟨⟨a, ha⟩, rfl⟩
    rw [hset, ← restrictSupport_eq_span]
    dsimp [V]
    rw [homogeneousSubmodule_eq_finsupp_supported]
    rfl
  apply top_unique
  intro a _
  obtain ⟨b, hb, hba⟩ := (show a.val ∈ T.map V.subtype by rw [hmap]; exact a.property)
  have : b = a := Subtype.ext hba
  exact this ▸ hb

variable {n : ℕ} {κ : Type*}

def multiplyForm (q : κ → MvPolynomial (Fin n) R)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) (s : κ) :
    homogeneousSubmodule (Fin n) R d →ₗ[R] homogeneousSubmodule (Fin n) R (d+2) where
  toFun a := ⟨a.val * q s, a.property.mul (hq s)⟩
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (smul_mul_assoc _ _ _)

def relationMatrix (q : κ → MvPolynomial (Fin n) R) (d : ℕ) :
    Matrix (DegreeExp n (d+2)) (κ × DegreeExp n d) R :=
  fun b a => (monomial a.2.val 1 * q a.1).coeff b.val

section Field
variable {K : Type*} [Field K] [Fintype κ]

theorem map_relations_eq_range (q : κ → MvPolynomial (Fin n) K)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) :
    (ChainMid.quadricRelations q (d+2)).map (coefficients n (d+2)).toLinearMap =
      LinearMap.range (relationMatrix q d).mulVecLin := by
  classical
  rw [Matrix.range_mulVecLin]
  let S := Submodule.span K (Set.range (relationMatrix q d).col)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, ChainMid.quadricRelations, Submodule.span_le]
    rintro p ⟨s, r, hr, a, hp⟩
    have hrd : r = d := Nat.add_right_cancel hr
    subst r
    have hfull : (⊤ : Submodule K (homogeneousSubmodule (Fin n) K d)) ≤
        S.comap ((coefficients n (d+2)).toLinearMap.comp (multiplyForm q hq d s)) := by
      rw [← span_monomialForm n d]
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      change coefficients n (d+2) (multiplyForm q hq d s (monomialForm n d b)) ∈ S
      apply Submodule.subset_span
      refine ⟨(s,b), ?_⟩
      ext e
      simp [relationMatrix, multiplyForm, monomialForm]
    have h := hfull (Submodule.mem_top (x := a))
    change coefficients n (d+2) (multiplyForm q hq d s a) ∈ S at h
    have heq : multiplyForm q hq d s a = p := Subtype.ext hp.symm
    change coefficients n (d+2) p ∈ S
    simpa only [heq] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨s,a⟩, rfl⟩
    refine ⟨multiplyForm q hq d s (monomialForm n d a), ?_, ?_⟩
    · exact Submodule.subset_span ⟨s,d,rfl,monomialForm n d a,rfl⟩
    · ext e
      simp [relationMatrix, multiplyForm, monomialForm]

def relationCokernelEquiv (q : κ → MvPolynomial (Fin n) K)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) :
    (homogeneousSubmodule (Fin n) K (d+2) ⧸ ChainMid.quadricRelations q (d+2)) ≃ₗ[K]
      ((DegreeExp n (d+2) → K) ⧸ LinearMap.range (relationMatrix q d).mulVecLin) :=
  Submodule.Quotient.equiv _ _ (coefficients n (d+2)) (map_relations_eq_range q hq d)

end Field

variable {A k K : Type*} [CommRing A] [Field k] [Field K] [Fintype κ]

omit [Fintype κ] in
theorem relationMatrix_map (q : κ → MvPolynomial (Fin n) A) (d : ℕ) (f : A →+* K) :
    relationMatrix (fun s => MvPolynomial.map f (q s)) d = (relationMatrix q d).map f := by
  ext b a
  simp only [relationMatrix, Matrix.map_apply, ← MvPolynomial.coeff_map,
    map_mul, map_monomial, map_one]

theorem graded_finrank_map_le_add_two (q : κ → MvPolynomial (Fin n) A)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) (ρ : A →+* k) (ι : A →+* K)
    (hι : Function.Injective ι) :
    finrank K (homogeneousSubmodule (Fin n) K (d+2) ⧸
      ChainMid.quadricRelations (fun s => MvPolynomial.map ι (q s)) (d+2)) ≤
    finrank k (homogeneousSubmodule (Fin n) k (d+2) ⧸
      ChainMid.quadricRelations (fun s => MvPolynomial.map ρ (q s)) (d+2)) := by
  rw [(relationCokernelEquiv _ (fun s => (hq s).map ι) d).finrank_eq,
    (relationCokernelEquiv _ (fun s => (hq s).map ρ) d).finrank_eq,
    relationMatrix_map, relationMatrix_map]
  exact Matrix.finrank_quotient_range_map_le (relationMatrix q d) ρ ι hι

omit [Fintype κ] in
theorem relations_eq_bot_of_lt_two (q : κ → MvPolynomial (Fin n) K) (d : ℕ)
    (hd : d < 2) : ChainMid.quadricRelations q d = ⊥ := by
  rw [ChainMid.quadricRelations, Submodule.span_eq_bot]
  rintro p ⟨s,r,hr,a,hp⟩
  omega

/-- Degree-wise semicontinuity from the SAME integral family. No flatness or
identity of Hilbert functions is assumed. -/
theorem graded_finrank_map_le (q : κ → MvPolynomial (Fin n) A)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) (ρ : A →+* k) (ι : A →+* K)
    (hι : Function.Injective ι) :
    finrank K (homogeneousSubmodule (Fin n) K d ⧸
      ChainMid.quadricRelations (fun s => MvPolynomial.map ι (q s)) d) ≤
    finrank k (homogeneousSubmodule (Fin n) k d ⧸
      ChainMid.quadricRelations (fun s => MvPolynomial.map ρ (q s)) d) := by
  by_cases hd : d < 2
  · rw [(Submodule.quotEquivOfEqBot _ (relations_eq_bot_of_lt_two _ d hd)).finrank_eq,
      (Submodule.quotEquivOfEqBot _ (relations_eq_bot_of_lt_two _ d hd)).finrank_eq,
      (coefficients n d).finrank_eq, (coefficients n d).finrank_eq,
      Module.finrank_pi, Module.finrank_pi]
  · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hd)
    rw [Nat.add_comm 2 e]
    exact graded_finrank_map_le_add_two q hq e ρ ι hι

end Option2.NativeStress.BookHilbertCharZero
