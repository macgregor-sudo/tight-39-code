module

public import SliceQuotient

@[expose] public section

/-!
# CHAINMID prototype: linear change of variables and free variables (step 5)

* `linSubst A` : `X_i ↦ ∑_j A i j • X_j` for arbitrary finite index types (`restrict B = linSubst B`).
* `finrank_quotient_le_of_linSubst` (change of coordinates + span containment): if `M * N = 1` and
  every target form `t k` lies in the span of the transformed forms `linSubst M (q s)`, then
  `dim (S_d ⧸ (q)_d) ≤ dim (T_d ⧸ (t)_d)`.
* `finrank_quotient_free_le` (free-variable convolution, upper bound):
  `dim (K[c,x]_n ⧸ (t)_n) ≤ ∑_{i+j=n} dim (K[x]_i ⧸ (t)_i) · dim K[c]_j`
  when the forms `t` involve only the `x` variables.
-/

open MvPolynomial Module Finset

namespace ChainMid

variable {K : Type*} [Field K]

instance homogeneousSubmodule_finite' (σ : Type*) [Finite σ] (d : ℕ) :
    Module.Finite K (homogeneousSubmodule σ K d) :=
  Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ d)

/-! ## Linear substitutions -/

/-- Linear substitution of variables. -/
noncomputable def linSubst {σ τ : Type*} [Fintype τ] (A : Matrix σ τ K) :
    MvPolynomial σ K →ₐ[K] MvPolynomial τ K :=
  aeval fun i => ∑ j, C (A i j) * X j

theorem linSubst_isHomogeneous {σ τ : Type*} [Fintype τ] (A : Matrix σ τ K)
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) : (linSubst A f).IsHomogeneous d := by
  have h := hf.aeval (fun j => ∑ t, C (A j t) * X t) (n := 1) fun j =>
    IsHomogeneous.sum _ _ _ fun t _ => isHomogeneous_C_mul_X _ _
  simpa [linSubst] using h

theorem linSubst_comp {ρ σ τ : Type*} [Fintype σ] [Fintype τ] (A : Matrix σ τ K)
    (A' : Matrix ρ σ K) : (linSubst A).comp (linSubst A') = linSubst (A' * A) := by
  apply algHom_ext
  intro k
  simp only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  exact (mul_assoc _ _ _).symm

theorem linSubst_one {σ : Type*} [Fintype σ] [DecidableEq σ] :
    linSubst (1 : Matrix σ σ K) = AlgHom.id K (MvPolynomial σ K) := by
  apply algHom_ext
  intro i
  simp [linSubst, Matrix.one_apply, apply_ite C, ite_mul]

/-- Products with an element of the span of the generators are relations. -/
theorem mul_mem_quadricRelations_of_mem_span {σ κ : Type*} {q : κ → MvPolynomial σ K}
    (hq : ∀ s, (q s).IsHomogeneous 2) {r d : ℕ} (hr : r + 2 = d)
    (b : homogeneousSubmodule σ K r) {y : MvPolynomial σ K}
    (hy : y ∈ Submodule.span K (Set.range q)) :
    b.val * y ∈ (quadricRelations q d).map (homogeneousSubmodule σ K d).subtype := by
  let L : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K b.val
  have hle : Submodule.span K (Set.range q) ≤
      ((quadricRelations q d).map (homogeneousSubmodule σ K d).subtype).comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hh : b.val * q s ∈ homogeneousSubmodule σ K d := by
      have := (b.property : (b.val).IsHomogeneous r).mul (hq s)
      rwa [hr] at this
    exact ⟨⟨_, hh⟩, Submodule.subset_span ⟨s, r, hr, b, rfl⟩, rfl⟩
  exact hle hy

/-- **Change of coordinates.** With `M * N = 1`, if every `t k` lies in the span of the transformed
forms `linSubst M (q s)`, the Hilbert function of `(q)` is bounded by that of `(t)`. -/
theorem finrank_quotient_le_of_linSubst {σ τ κ κ' : Type*} [Fintype σ] [DecidableEq σ]
    [Fintype τ] (M : Matrix σ τ K) (N : Matrix τ σ K) (hMN : M * N = 1)
    (q : κ → MvPolynomial σ K) (hq : ∀ s, (q s).IsHomogeneous 2)
    (t : κ' → MvPolynomial τ K)
    (ht : ∀ k, t k ∈ Submodule.span K (Set.range fun s => linSubst M (q s))) (d : ℕ) :
    finrank K (homogeneousSubmodule σ K d ⧸ quadricRelations q d) ≤
      finrank K (homogeneousSubmodule τ K d ⧸ quadricRelations t d) := by
  have hid : ∀ f, linSubst N (linSubst M f) = f := fun f => by
    have := congrArg (fun φ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K => φ f)
      (linSubst_comp N M)
    simpa [hMN, linSubst_one] using this
  let Γ : homogeneousSubmodule τ K d →ₗ[K] homogeneousSubmodule σ K d :=
    LinearMap.codRestrict _ ((linSubst N).toLinearMap ∘ₗ (homogeneousSubmodule τ K d).subtype)
      fun f => linSubst_isHomogeneous N f.property
  have hΓ : Function.Surjective Γ := fun y =>
    ⟨⟨linSubst M y.val, linSubst_isHomogeneous M y.property⟩, Subtype.ext (hid y.val)⟩
  let Ψ := (quadricRelations q d).mkQ ∘ₗ Γ
  have hΨ : Function.Surjective Ψ := (Submodule.mkQ_surjective _).comp hΓ
  have hspan : ∀ k, linSubst N (t k) ∈ Submodule.span K (Set.range q) := by
    intro k
    have h1 := Submodule.mem_map_of_mem (f := (linSubst N).toLinearMap) (ht k)
    rw [Submodule.map_span, ← Set.range_comp] at h1
    simpa [Function.comp_def, hid] using h1
  have hker : quadricRelations t d ≤ LinearMap.ker Ψ := by
    rw [quadricRelations, Submodule.span_le]
    rintro p ⟨k, r, hr, a, hp⟩
    have hmem := mul_mem_quadricRelations_of_mem_span hq hr
      ⟨linSubst N a.val, linSubst_isHomogeneous N a.property⟩ (hspan k)
    obtain ⟨x, hx, hxe⟩ := hmem
    have hΓp : Γ p = x := by
      apply Subtype.ext
      change linSubst N p.val = x.val
      rw [hp, map_mul]
      exact hxe.symm
    show (quadricRelations q d).mkQ (Γ p) = 0
    rw [hΓp, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  have hsurj : Function.Surjective ((quadricRelations t d).liftQ Ψ hker) := by
    intro y
    obtain ⟨x, rfl⟩ := hΨ y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact LinearMap.finrank_le_finrank_of_surjective hsurj

/-! ## Free variables -/

section Free

variable {τc τx κ : Type*} [Fintype τc] [Fintype τx]

/-- `rename inl P * rename inr q` lies in the relations of the extended forms. -/
theorem mul_rename_mem_quadricRelations {t : κ → MvPolynomial τx K}
    (ht : ∀ s, (t s).IsHomogeneous 2) {P : MvPolynomial τc K}
    {k m n : ℕ} (hP : P.IsHomogeneous k) (hkm : k + m = n)
    {q : homogeneousSubmodule τx K m} (hq : q ∈ quadricRelations t m) :
    rename Sum.inl P * rename Sum.inr q.val ∈
      (quadricRelations (fun s => rename (Sum.inr : τx → τc ⊕ τx) (t s)) n).map
        (homogeneousSubmodule (τc ⊕ τx) K n).subtype := by
  let L : homogeneousSubmodule τx K m →ₗ[K] MvPolynomial (τc ⊕ τx) K :=
    LinearMap.mulLeft K (rename Sum.inl P) ∘ₗ (rename Sum.inr).toLinearMap ∘ₗ
      (homogeneousSubmodule τx K m).subtype
  have hle : quadricRelations t m ≤
      ((quadricRelations (fun s => rename (Sum.inr : τx → τc ⊕ τx) (t s)) n).map
        (homogeneousSubmodule (τc ⊕ τx) K n).subtype).comap L := by
    rw [quadricRelations, Submodule.span_le]
    rintro p ⟨s, r, hr, a, hp⟩
    have ha : (rename Sum.inl P * rename (Sum.inr : τx → τc ⊕ τx) a.val).IsHomogeneous (k + r) :=
      hP.rename_isHomogeneous.mul (a.property : (a.val).IsHomogeneous r).rename_isHomogeneous
    have hpn : (rename Sum.inl P * rename (Sum.inr : τx → τc ⊕ τx) a.val) *
        rename Sum.inr (t s) ∈ homogeneousSubmodule (τc ⊕ τx) K n := by
      have := ha.mul ((ht s).rename_isHomogeneous (f := (Sum.inr : τx → τc ⊕ τx)))
      rwa [show k + r + 2 = n by omega] at this
    refine ⟨⟨_, hpn⟩, Submodule.subset_span ⟨s, k + r, by omega, ⟨_, ha⟩, rfl⟩, ?_⟩
    simp only [L, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply,
      AlgHom.toLinearMap_apply, hp, map_mul, mul_assoc]
  exact hle hq

/-- **Free variables.** If the forms `t` involve only the `x` variables, the Hilbert function in the
`(c, x)` variables is at most the convolution of the `x`-Hilbert function with that of `K[c]`. -/
theorem finrank_quotient_free_le {t : κ → MvPolynomial τx K}
    (ht : ∀ s, (t s).IsHomogeneous 2) (n : ℕ) :
    finrank K (homogeneousSubmodule (τc ⊕ τx) K n ⧸
        quadricRelations (fun s => rename (Sum.inr : τx → τc ⊕ τx) (t s)) n) ≤
      ∑ ij ∈ antidiagonal n,
        finrank K (homogeneousSubmodule τx K ij.1 ⧸ quadricRelations t ij.1) *
          finrank K (homogeneousSubmodule τc K ij.2) := by
  classical
  set Q' := quadricRelations (fun s => rename (Sum.inr : τx → τc ⊕ τx) (t s)) n with hQ'
  let h : ℕ → ℕ := fun i => finrank K (homogeneousSubmodule τx K i ⧸ quadricRelations t i)
  let D : ℕ → ℕ := fun j => finrank K (homogeneousSubmodule τc K j)
  let bx : ∀ i, Basis (Fin (h i)) K (homogeneousSubmodule τx K i ⧸ quadricRelations t i) :=
    fun i => Module.finBasis K _
  let bl : ∀ i, Fin (h i) → homogeneousSubmodule τx K i :=
    fun i a => (Submodule.mkQ_surjective (quadricRelations t i) (bx i a)).choose
  have hbl : ∀ i a, (quadricRelations t i).mkQ (bl i a) = bx i a :=
    fun i a => (Submodule.mkQ_surjective (quadricRelations t i) (bx i a)).choose_spec
  let ec : ∀ j, Basis (Fin (D j)) K (homogeneousSubmodule τc K j) := fun j => Module.finBasis K _
  let J := Σ ij : (antidiagonal n), Fin (h ij.1.1) × Fin (D ij.1.2)
  let vpoly : J → MvPolynomial (τc ⊕ τx) K := fun x =>
    rename Sum.inl (ec x.1.1.2 x.2.2).val * rename Sum.inr (bl x.1.1.1 x.2.1).val
  have hv : ∀ x : J, vpoly x ∈ homogeneousSubmodule (τc ⊕ τx) K n := by
    rintro ⟨⟨⟨i, j⟩, hij⟩, a, b⟩
    have hij' : i + j = n := mem_antidiagonal.mp hij
    have h1 : (rename (Sum.inl : τc → τc ⊕ τx) (ec j b).val).IsHomogeneous j :=
      ((ec j b).property : ((ec j b).val).IsHomogeneous j).rename_isHomogeneous
    have h2 : (rename (Sum.inr : τx → τc ⊕ τx) (bl i a).val).IsHomogeneous i :=
      ((bl i a).property : ((bl i a).val).IsHomogeneous i).rename_isHomogeneous
    have := h1.mul h2
    rwa [show j + i = n by omega] at this
  let v : J → homogeneousSubmodule (τc ⊕ τx) K n := fun x => ⟨vpoly x, hv x⟩
  let V : Submodule K (MvPolynomial (τc ⊕ τx) K) :=
    Submodule.span K (Set.range vpoly) ⊔ Q'.map (homogeneousSubmodule (τc ⊕ τx) K n).subtype
  -- products of a `c`-form and an `x`-form of complementary degrees lie in `V`
  have hkey : ∀ (i j : ℕ) (hij : i + j = n) (P : homogeneousSubmodule τc K j)
      (y : homogeneousSubmodule τx K i), rename Sum.inl P.val * rename Sum.inr y.val ∈ V := by
    intro i j hij P y
    let c := (bx i).repr ((quadricRelations t i).mkQ y)
    have hq : y - ∑ a, c a • bl i a ∈ quadricRelations t i := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp_rw [map_smul, hbl]
      rw [(bx i).sum_repr, sub_self]
    have hy : y = (∑ a, c a • bl i a) + (y - ∑ a, c a • bl i a) := (add_sub_cancel _ _).symm
    let ij : antidiagonal n := ⟨(i, j), mem_antidiagonal.mpr hij⟩
    have hP : P.val = ∑ b, (ec j).repr P b • (ec j b).val := by
      have := congrArg Subtype.val ((ec j).sum_repr P)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hgen : ∀ a, rename Sum.inl P.val * rename Sum.inr (bl i a).val ∈
        Submodule.span K (Set.range vpoly) := by
      intro a
      rw [hP, map_sum, Finset.sum_mul]
      refine Submodule.sum_mem _ fun b _ => ?_
      rw [map_smul, smul_mul_assoc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨ij, a, b⟩, rfl⟩)
    rw [hy, Submodule.coe_add, map_add, mul_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
    · rw [Submodule.coe_sum, map_sum, Finset.mul_sum]
      refine Submodule.sum_mem _ fun a _ => ?_
      rw [Submodule.coe_smul, map_smul, mul_smul_comm]
      exact Submodule.smul_mem _ _ (hgen a)
    · exact mul_rename_mem_quadricRelations ht P.property (by omega) hq
  -- every form of degree `n` lies in `V`
  have hT : homogeneousSubmodule (τc ⊕ τx) K n ≤ V := by
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single,
      Submodule.span_le]
    rintro _ ⟨u, hu, rfl⟩
    have hu' : u.degree = n := hu
    let Pc : MvPolynomial τc K := ∏ a, X a ^ u (Sum.inl a)
    let Px : MvPolynomial τx K := ∏ b, X b ^ u (Sum.inr b)
    have hPc : Pc.IsHomogeneous (∑ a, u (Sum.inl a)) :=
      IsHomogeneous.prod _ _ _ fun a _ => isHomogeneous_X_pow _ _
    have hPx : Px.IsHomogeneous (∑ b, u (Sum.inr b)) :=
      IsHomogeneous.prod _ _ _ fun b _ => isHomogeneous_X_pow _ _
    have hdeg : (∑ b, u (Sum.inr b)) + (∑ a, u (Sum.inl a)) = n := by
      rw [← hu', Finsupp.degree_eq_sum, Fintype.sum_sum_type, add_comm]
    have hmono : (monomial u (1 : K) : MvPolynomial (τc ⊕ τx) K) =
        rename Sum.inl Pc * rename Sum.inr Px := by
      rw [MvPolynomial.monomial_eq, C_1, one_mul,
        Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sum_type]
      simp [Pc, Px, map_prod, map_pow, rename_X]
    change monomial u (1 : K) ∈ V
    rw [hmono]
    exact hkey _ _ hdeg ⟨Pc, hPc⟩ ⟨Px, hPx⟩
  -- hence the images of `v` span the quotient
  have hspan : Submodule.span K (Set.range (Q'.mkQ ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective Q' z
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp (hT f.property)
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hf : f = ∑ x, cf x • v x + y' := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_sum, ← hxy, ← hcf]
      simp [v]
    rw [hf, map_add, Submodule.mkQ_apply Q' y', (Submodule.Quotient.mk_eq_zero Q').mpr hy',
      add_zero, map_sum]
    exact Submodule.sum_mem _ fun x _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have hcard := finrank_range_le_card (R := K) (Q'.mkQ ∘ v)
  rw [Set.finrank, hspan, finrank_top] at hcard
  refine hcard.trans (le_of_eq ?_)
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  exact Finset.sum_coe_sort (antidiagonal n) (fun ij => h ij.1 * D ij.2)

end Free

end ChainMid
