module

public import SliceDimension
public import SliceLift
public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# The slice lemmas applied to the project's iterated cut relations

Let `g : ι → MvPolynomial (Fin n) K` be the equations, `E : ε → ι` the selected rows,
`weights` the annihilator weights and `cuts` the list of linear cuts. The relation family
`equationIteratedCutRelations g E weights cuts` contains, in every degree `e + 1`, the
products of degree-`e` forms with the linear parts of the selected rows and with the cuts.
Let `W` (`cutLinearSpace`) be the span of these linear forms.

Given a pivoted slice matrix `B : Matrix (Fin n) (Fin m) K` on which every element of `W`
vanishes, and `dim W ≥ n - m`, we obtain:
* `finrank_equationCutPiece_le`: every degree piece of the cut quotient has dimension at most
  `multichoose m d = (m + d - 1).choose d` (the shape of the Hilbert-function premise);
* `equationIteratedCutRelations_sup_eq_top`: if a family `A` of degree-`(e+1)` forms
  restricts onto all degree-`(e+1)` forms on the slice, then the relations together with `A`
  span everything (the shape of the spanning premise).
For the quartic certificate: `n = 1053`, `m = 19`, `K = ℂ`, spanning in degree `4`.
-/

open MvPolynomial Module
open PolynomialJets

namespace SliceLemmas

section IteratedCuts

variable {σ R : Type*} [CommRing R]

/-- Every cut stage contains the family it started from. -/
theorem le_iterate (cuts : List (homogeneousSubmodule σ R 1)) :
    ∀ (D : HomogeneousRelationFamilies.Family σ R) (k : ℕ),
      D k ≤ HomogeneousRelationFamilies.iterate D cuts k := by
  induction cuts with
  | nil => intro D k; exact le_rfl
  | cons z cuts ih =>
    intro D k
    refine le_trans ?_ (ih (HomogeneousRelationFamilies.cut D z) k)
    cases k with
    | zero => exact le_rfl
    | succ k => exact le_sup_left

/-- For every cut `z` in the list, all products `z * a` with `a` of degree `k` lie in the
final cut stage in degree `k + 1`. -/
theorem range_homogeneousLinearMul_le_iterate (cuts : List (homogeneousSubmodule σ R 1)) :
    ∀ (D : HomogeneousRelationFamilies.Family σ R) {z : homogeneousSubmodule σ R 1},
      z ∈ cuts → ∀ k : ℕ, LinearMap.range (homogeneousLinearMul z k) ≤
        HomogeneousRelationFamilies.iterate D cuts (k + 1) := by
  induction cuts with
  | nil => intro D z hz; simp at hz
  | cons z' cuts ih =>
    intro D z hz k
    change _ ≤ HomogeneousRelationFamilies.iterate (HomogeneousRelationFamilies.cut D z') cuts
      (k + 1)
    rcases List.mem_cons.mp hz with rfl | hz
    · have hcut : LinearMap.range (homogeneousLinearMul z k) ≤
          HomogeneousRelationFamilies.cut D z (k + 1) :=
        (le_sup_right : LinearMap.range (homogeneousLinearMul z k) ≤
          D (k + 1) ⊔ LinearMap.range (homogeneousLinearMul z k))
      exact le_trans hcut (le_iterate cuts _ (k + 1))
    · exact ih _ hz k

end IteratedCuts

variable {K : Type*} [Field K] {n m : ℕ}
variable {ι ε κ : Type*} [Fintype ι]

/-- The linear forms used as relations: the linear parts of the selected rows and the cuts. -/
noncomputable def cutLinearSpace (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (cuts : List (homogeneousSubmodule (Fin n) K 1)) : Submodule K (MvPolynomial (Fin n) K) :=
  Submodule.span K (Set.range (fun e => homogeneousComponent 1 (g (E e))) ∪
    {p | ∃ z ∈ cuts, p = z.val})

omit [Fintype ι] in
theorem cutLinearSpace_le_homogeneousSubmodule (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (cuts : List (homogeneousSubmodule (Fin n) K 1)) :
    cutLinearSpace g E cuts ≤ homogeneousSubmodule (Fin n) K 1 := by
  rw [cutLinearSpace, Submodule.span_le]
  rintro _ (⟨e, rfl⟩ | ⟨z, _, rfl⟩)
  · exact homogeneousComponent_mem 1 _
  · exact z.property

/-- The degree-`d` relations, viewed as polynomials. -/
noncomputable def cutRelationsAsPolynomials (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (weights : κ → ι → K) (cuts : List (homogeneousSubmodule (Fin n) K 1)) (d : ℕ) :
    Submodule K (MvPolynomial (Fin n) K) :=
  (equationIteratedCutRelations g E weights cuts d).map
    (homogeneousSubmodule (Fin n) K d).subtype

/-- `W · S_e ⊆ relations_(e+1)`: the products of degree-`e` forms with linear parts of
selected rows and with cuts are relations. -/
theorem sliceRelations_cutLinearSpace_le (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (weights : κ → ι → K) (cuts : List (homogeneousSubmodule (Fin n) K 1)) (e : ℕ) :
    sliceRelations (cutLinearSpace g E cuts) e ≤
      cutRelationsAsPolynomials g E weights cuts (e + 1) := by
  set T := cutRelationsAsPolynomials g E weights cuts (e + 1)
  rw [sliceRelations, Submodule.span_le]
  rintro _ ⟨w, hw, a, ha, rfl⟩
  show w * a ∈ T
  induction hw using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨z, hz, rfl⟩
    · have hmem : a * homogeneousComponent 1 (g (E i)) ∈
          homogeneousSubmodule (Fin n) K (e + 1) :=
        (IsHomogeneous.mul ha (homogeneousComponent_mem 1 (g (E i))))
      refine ⟨⟨_, hmem⟩, ?_, by simp [mul_comm]⟩
      apply le_iterate cuts (equationDegreeRelations g E weights) (e + 1)
      apply Submodule.subset_span
      exact Or.inl ⟨i, e, rfl, ⟨a, ha⟩, rfl⟩
    · refine ⟨homogeneousLinearMul z e ⟨a, ha⟩, ?_, rfl⟩
      exact range_homogeneousLinearMul_le_iterate cuts _ hz e ⟨⟨a, ha⟩, rfl⟩
  | zero => rw [zero_mul]; exact T.zero_mem
  | add x y _ _ hx hy => rw [add_mul]; exact T.add_mem hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact T.smul_mem c hx

theorem sliceRelationsIn_cutLinearSpace_le (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (weights : κ → ι → K) (cuts : List (homogeneousSubmodule (Fin n) K 1)) (e : ℕ) :
    sliceRelationsIn (cutLinearSpace g E cuts) e ≤
      equationIteratedCutRelations g E weights cuts (e + 1) := by
  have h := Submodule.comap_mono (f := (homogeneousSubmodule (Fin n) K (e + 1)).subtype)
    (sliceRelations_cutLinearSpace_le g E weights cuts e)
  rwa [cutRelationsAsPolynomials, Submodule.comap_map_eq_of_injective
    (Submodule.injective_subtype _)] at h

omit [Fintype ι] in
/-- Under the slice hypotheses, the relation linear forms are exactly the annihilator. -/
theorem cutLinearSpace_eq_linearAnnihilator {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {g : ι → MvPolynomial (Fin n) K} {E : ε → ι}
    {cuts : List (homogeneousSubmodule (Fin n) K 1)}
    (hvanish : cutLinearSpace g E cuts ≤ linearAnnihilator B)
    (hdim : n - m ≤ finrank K (cutLinearSpace g E cuts)) :
    cutLinearSpace g E cuts = linearAnnihilator B :=
  eq_linearAnnihilator_of_le_of_finrank_le hB hvanish hdim

/-- Premise-5 shape, positive degrees: if the linear parts of the selected rows and the cuts
vanish on a pivoted slice of dimension `m` and span a space of dimension at least `n - m`,
then the cut quotient in degree `e + 1` has dimension at most `multichoose m (e + 1)`. -/
theorem finrank_equationCutPiece_succ_le {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {g : ι → MvPolynomial (Fin n) K} {E : ε → ι}
    (weights : κ → ι → K) {cuts : List (homogeneousSubmodule (Fin n) K 1)}
    (hvanish : cutLinearSpace g E cuts ≤ linearAnnihilator B)
    (hdim : n - m ≤ finrank K (cutLinearSpace g E cuts)) (e : ℕ) :
    finrank K (equationCutPiece g E weights cuts (e + 1)) ≤ Nat.multichoose m (e + 1) := by
  have hW := cutLinearSpace_eq_linearAnnihilator hB hvanish hdim
  have hle := sliceRelationsIn_cutLinearSpace_le g E weights cuts e
  have hsurj : Function.Surjective (Submodule.factor hle) := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ x, Submodule.factor_mk hle x⟩
  exact (LinearMap.finrank_le_finrank_of_surjective hsurj).trans
    (finrank_quotient_sliceRelations_le hB hW e)

/-- Premise-5 shape, degree zero: the degree-zero piece has dimension at most one. -/
theorem finrank_equationCutPiece_zero_le (g : ι → MvPolynomial (Fin n) K) (E : ε → ι)
    (weights : κ → ι → K) (cuts : List (homogeneousSubmodule (Fin n) K 1)) :
    finrank K (equationCutPiece g E weights cuts 0) ≤ Nat.multichoose m 0 := by
  have h := Submodule.finrank_quotient_le (equationIteratedCutRelations g E weights cuts 0)
  rw [finrank_homogeneousSubmodule] at h
  simpa using h

/-- Premise-5 shape in every degree: `dim (S_d / relations_d) ≤ (m + d - 1).choose d`. -/
theorem finrank_equationCutPiece_le {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {g : ι → MvPolynomial (Fin n) K} {E : ε → ι}
    (weights : κ → ι → K) {cuts : List (homogeneousSubmodule (Fin n) K 1)}
    (hvanish : cutLinearSpace g E cuts ≤ linearAnnihilator B)
    (hdim : n - m ≤ finrank K (cutLinearSpace g E cuts)) (d : ℕ) :
    finrank K (equationCutPiece g E weights cuts d) ≤ (m + d - 1).choose d := by
  rw [← Nat.multichoose_eq]
  cases d with
  | zero => exact finrank_equationCutPiece_zero_le g E weights cuts
  | succ e => exact finrank_equationCutPiece_succ_le hB weights hvanish hdim e

/-- Premise-5 shape with the slice dimension written `k + 1`:
`dim (S_d / relations_d) ≤ (k + d).choose k`; for the quartic certificate `k = 18`. -/
theorem finrank_equationCutPiece_le_choose {k : ℕ} {B : Matrix (Fin n) (Fin (k + 1)) K}
    {piv : Fin (k + 1) → Fin n} (hB : IsPivot B piv) {g : ι → MvPolynomial (Fin n) K}
    {E : ε → ι} (weights : κ → ι → K) {cuts : List (homogeneousSubmodule (Fin n) K 1)}
    (hvanish : cutLinearSpace g E cuts ≤ linearAnnihilator B)
    (hdim : n - (k + 1) ≤ finrank K (cutLinearSpace g E cuts)) (d : ℕ) :
    finrank K (equationCutPiece g E weights cuts d) ≤ (k + d).choose k := by
  have h := finrank_equationCutPiece_le hB weights hvanish hdim d
  rwa [show k + 1 + d - 1 = k + d by omega, ← Nat.choose_symm_add] at h

/-- Premise-4 shape: if a family `A` of degree-`(e+1)` forms restricts onto all degree-`(e+1)`
forms on the slice, the relations together with `A` are everything in degree `e + 1`. -/
theorem equationIteratedCutRelations_sup_eq_top {B : Matrix (Fin n) (Fin m) K}
    {piv : Fin m → Fin n} (hB : IsPivot B piv) {g : ι → MvPolynomial (Fin n) K} {E : ε → ι}
    (weights : κ → ι → K) {cuts : List (homogeneousSubmodule (Fin n) K 1)}
    (hvanish : cutLinearSpace g E cuts ≤ linearAnnihilator B)
    (hdim : n - m ≤ finrank K (cutLinearSpace g E cuts)) {e : ℕ}
    (A : Submodule K (homogeneousSubmodule (Fin n) K (e + 1)))
    (hsurj : homogeneousSubmodule (Fin m) K (e + 1) ≤
      (A.map (homogeneousSubmodule (Fin n) K (e + 1)).subtype).map (restrict B).toLinearMap) :
    equationIteratedCutRelations g E weights cuts (e + 1) ⊔ A = ⊤ := by
  have hW := cutLinearSpace_eq_linearAnnihilator hB hvanish hdim
  have hspan := sliceRelations_sup_eq_homogeneousSubmodule hB
    (cutLinearSpace_le_homogeneousSubmodule g E cuts) hW.ge
    (T := A.map (homogeneousSubmodule (Fin n) K (e + 1)).subtype) (by
      rw [Submodule.map_le_iff_le_comap]
      intro x _
      exact x.property) hsurj
  have hle : sliceRelations (cutLinearSpace g E cuts) e ⊔ A.map (homogeneousSubmodule (Fin n) K (e + 1)).subtype ≤
      (equationIteratedCutRelations g E weights cuts (e + 1) ⊔ A).map (homogeneousSubmodule (Fin n) K (e + 1)).subtype := by
    rw [Submodule.map_sup]
    exact sup_le_sup_right (sliceRelations_cutLinearSpace_le g E weights cuts e) _
  rw [eq_top_iff]
  intro x _
  have hx : (x : MvPolynomial (Fin n) K) ∈
      (equationIteratedCutRelations g E weights cuts (e + 1) ⊔ A).map (homogeneousSubmodule (Fin n) K (e + 1)).subtype :=
    hle (hspan.ge x.property)
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
  rwa [Subtype.ext hyx] at hy

end SliceLemmas
