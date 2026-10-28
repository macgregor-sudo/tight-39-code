module

public import BookHilbertPermutation

@[expose] public section

noncomputable section
namespace Option2.NativeStress.BookHilbertCharZero
open MvPolynomial Module
open Option2.NativeStress.BookHT

section Renaming
variable {n : ℕ} {κ K : Type*} [Field K]

def renameHomogeneous (e : Fin n ≃ Fin n) (d : ℕ) :
    homogeneousSubmodule (Fin n) K d ≃ₗ[K] homogeneousSubmodule (Fin n) K d where
  toFun p := ⟨rename e p.val, (p.property : p.val.IsHomogeneous d).rename_isHomogeneous⟩
  invFun p := ⟨rename e.symm p.val, (p.property : p.val.IsHomogeneous d).rename_isHomogeneous⟩
  left_inv p := Subtype.ext (by
    change rename e.symm (rename e p.val) = p.val
    rw [rename_rename, e.symm_comp_self, rename_id_apply])
  right_inv p := Subtype.ext (by
    change rename e (rename e.symm p.val) = p.val
    rw [rename_rename, e.self_comp_symm, rename_id_apply])
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem map_relations_rename (e : Fin n ≃ Fin n) (q : κ → MvPolynomial (Fin n) K)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) :
    (ChainMid.quadricRelations q d).map (renameHomogeneous e d).toLinearMap =
      ChainMid.quadricRelations (fun s => rename e (q s)) d := by
  classical
  apply le_antisymm
  · rw [ChainMid.quadricRelations, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨p, ⟨s,r,hr,a,hp⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨s,r,hr,⟨rename e a.val, a.property.rename_isHomogeneous⟩, ?_⟩
    change rename e p.val = rename e a.val * rename e (q s)
    rw [hp,map_mul]
  · rw [ChainMid.quadricRelations, Submodule.span_le]
    rintro p ⟨s,r,hr,a,hp⟩
    let a' : homogeneousSubmodule (Fin n) K r :=
      ⟨rename e.symm a.val, a.property.rename_isHomogeneous⟩
    let p' : homogeneousSubmodule (Fin n) K d :=
      ⟨a'.val * q s, hr ▸ a'.property.mul (hq s)⟩
    refine ⟨p',Submodule.subset_span ⟨s,r,hr,a',rfl⟩,?_⟩
    apply Subtype.ext
    change rename e (rename e.symm a.val * q s) = p.val
    rw [map_mul,rename_rename,e.self_comp_symm,rename_id_apply,hp]

 theorem finrank_relations_rename (e : Fin n ≃ Fin n) (q : κ → MvPolynomial (Fin n) K)
    (hq : ∀ s, (q s).IsHomogeneous 2) (d : ℕ) :
    finrank K (homogeneousSubmodule (Fin n) K d ⧸ ChainMid.quadricRelations q d) =
      finrank K (homogeneousSubmodule (Fin n) K d ⧸
        ChainMid.quadricRelations (fun s => rename e (q s)) d) :=
  (Submodule.Quotient.equiv _ _ (renameHomogeneous e d) (map_relations_rename e q hq d)).finrank_eq
end Renaming

 theorem bookIntegerQuadric_homogeneous (s : Fin 48) : (bookIntegerQuadric s).IsHomogeneous 2 := by
  have hi : rename grevlexEquiv.symm (integerTrinomial s) = bookIntegerQuadric s := by
    rw [← integer_dictionary_binding]
    change rename grevlexEquiv.symm (rename grevlexEquiv (bookIntegerQuadric s)) = _
    rw [rename_rename,grevlexEquiv.symm_comp_self,rename_id_apply]
  rw [← hi]
  exact (integerTrinomial_homogeneous s).rename_isHomogeneous

def bookQuadrics (K : Type*) [CommRing K] : Fin 48 → MvPolynomial (Fin 24) K :=
  fun s => MvPolynomial.map (Int.castRingHom K) (bookIntegerQuadric s)

 theorem rename_bookQuadrics (K : Type*) [CommRing K] :
    (fun s => rename grevlexEquiv (bookQuadrics K s)) = trinomials K := by
  funext s
  rw [bookQuadrics, ← map_rename]
  change MvPolynomial.map (Int.castRingHom K) (rename grevlexIndex (bookIntegerQuadric s)) = _
  rw [integer_dictionary_binding]
  rfl

/-- Universal characteristic-zero Book Hilbert bound, with the actual integral
48-row dictionary and degree-wise quotient, proved from the modular certificate. -/
 theorem book_hilbert_bound (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    finrank K (homogeneousSubmodule (Fin 24) K d ⧸ ChainMid.quadricRelations (bookQuadrics K) d) ≤
      4 * (d+5).choose 5 + 1540 * (d+4).choose 4 := by
  rw [finrank_relations_rename grevlexEquiv (bookQuadrics K)
    (fun s => (bookIntegerQuadric_homogeneous s).map (Int.castRingHom K)) d,
    rename_bookQuadrics]
  exact signed_hilbert_bound K d

 theorem bookQuadrics_complex : bookQuadrics ℂ = Dictionary.quadric := by
  funext s
  simp [bookQuadrics,bookIntegerQuadric,Dictionary.quadric,Dictionary.termPolynomial,
    Fin.sum_univ_succ,add_assoc]

/-- The actual existing complex Book dictionary, with NO Hilbert/rank/phase premise. -/
 theorem dictionary_hilbert_bound (d : ℕ) :
    finrank ℂ (homogeneousSubmodule (Fin 24) ℂ d ⧸ ChainMid.quadricRelations Dictionary.quadric d) ≤
      4 * (d+5).choose 5 + 1540 * (d+4).choose 4 := by
  rw [← bookQuadrics_complex]
  exact book_hilbert_bound ℂ d

#print axioms Option2.NativeStress.BookHilbertCharZero.book_hilbert_bound
#print axioms Option2.NativeStress.BookHilbertCharZero.dictionary_hilbert_bound
end Option2.NativeStress.BookHilbertCharZero
