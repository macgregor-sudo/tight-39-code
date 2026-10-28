module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Order.WellFoundedSet
public import QuadricRelations

@[expose] public section

/-!
# MONO prototype: leading monomials bound the Hilbert function (step 6)

Generic over a field `K`, a finite variable type `σ` and quadrics `t : κ → K[σ]` homogeneous of degree 2.
`r` is any strict order on exponents that is translation invariant (`r a b → r (a+c) (b+c)`); it is only used on
the finite set of degree-`d` exponents, so it need not be a Mathlib `MonomialOrder` (grevlex restricted to one degree
is the opposite of lex in reversed variables, see `revLexLT` below; no `MonomialOrder` instance is needed).

If every `μ ∈ G` is the `r`-leading exponent of an explicit `g ∈ relSpan t |μ|` (all other support exponents
`r`-smaller and of the same degree), then for every `d` and every finset `S` containing the degree-`d` exponents not
divisible by any `μ ∈ G`: `finrank K (K[σ]_d ⧸ (t)_d) ≤ S.card`. `quadricRelations` is CHAINMID's definition, verbatim.
-/

open MvPolynomial Module
open ChainMid (quadricRelations)

namespace Mono

variable {K : Type*} [Field K]

variable {σ κ : Type*}

/-- Degree-`n` span of monomial multiples of the quadrics (the certificate side). -/
noncomputable def relSpan (t : κ → MvPolynomial σ K) (n : ℕ) : Submodule K (MvPolynomial σ K) :=
  Submodule.span K {f | ∃ (m : σ →₀ ℕ) (s : κ), m.degree + 2 = n ∧ f = monomial m 1 * t s}

theorem monomial_mul_mem_relSpan (t : κ → MvPolynomial σ K) {n : ℕ} (k : σ →₀ ℕ) {f : MvPolynomial σ K}
    (hf : f ∈ relSpan t n) : monomial k (1 : K) * f ∈ relSpan t (k.degree + n) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, s, hm, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨k + m, s, ?_, ?_⟩
    · rw [map_add]; omega
    · rw [← mul_assoc, monomial_mul_monomial, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hx

theorem relSpan_le_map (t : κ → MvPolynomial σ K) (ht : ∀ s, (t s).IsHomogeneous 2) (d : ℕ) :
    relSpan t d ≤ (quadricRelations t d).map (homogeneousSubmodule σ K d).subtype := by
  rw [relSpan, Submodule.span_le]
  rintro _ ⟨m, s, hm, rfl⟩
  have hmh : (monomial m (1 : K)).IsHomogeneous m.degree := isHomogeneous_monomial _ rfl
  have hd : (monomial m (1 : K) * t s) ∈ homogeneousSubmodule σ K d := by
    have := hmh.mul (ht s); rwa [hm] at this
  exact ⟨⟨_, hd⟩, Submodule.subset_span ⟨s, m.degree, hm, ⟨_, hmh⟩, rfl⟩, rfl⟩

/-- The certificate for one leading exponent `μ`: an element of the degree-`|μ|` relation span whose support is
`μ` plus `r`-smaller exponents of the same degree. -/
def LeadCert (t : κ → MvPolynomial σ K) (r : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop) (μ : σ →₀ ℕ) : Prop :=
  ∃ g ∈ relSpan t μ.degree, g.coeff μ ≠ 0 ∧ ∀ s ∈ g.support, s ≠ μ → r s μ ∧ s.degree = μ.degree

theorem finrank_le_card_of_leadCerts [DecidableEq σ] [Finite σ] (t : κ → MvPolynomial σ K)
    (ht : ∀ s, (t s).IsHomogeneous 2)
    (r : (σ →₀ ℕ) → (σ →₀ ℕ) → Prop) [IsStrictOrder (σ →₀ ℕ) r]
    (hr : ∀ a b c, r a b → r (a + c) (b + c))
    (G : Set (σ →₀ ℕ)) (hG : ∀ μ ∈ G, LeadCert t r μ)
    (d : ℕ) (S : Finset (σ →₀ ℕ)) (hS : ∀ s : σ →₀ ℕ, s.degree = d → (∀ μ ∈ G, ¬ μ ≤ s) → s ∈ S) :
    finrank K (homogeneousSubmodule σ K d ⧸ quadricRelations t d) ≤ S.card := by
  classical
  set V := homogeneousSubmodule σ K d
  set Q := quadricRelations t d
  let ι := ↥(S.filter fun s => s.degree = d)
  let b : ι → V := fun s => ⟨monomial s.1 1, isHomogeneous_monomial _ (Finset.mem_filter.mp s.2).2⟩
  set B : Submodule K V := Submodule.span K (Set.range b)
  set W : Submodule K (MvPolynomial σ K) := (Q ⊔ B).map V.subtype
  -- every degree-d monomial lies in W
  have key : ∀ s : σ →₀ ℕ, s.degree = d → monomial s (1 : K) ∈ W := by
    intro s hs
    refine Set.WellFoundedOn.induction (P := fun s => monomial s (1 : K) ∈ W)
      ((Finsupp.finite_of_degree_eq (σ := σ) d).wellFoundedOn (r := r)) hs ?_
    intro s hs IH
    by_cases hstd : ∀ μ ∈ G, ¬ μ ≤ s
    · have hsS : s ∈ S.filter fun s => s.degree = d := Finset.mem_filter.mpr ⟨hS s hs hstd, hs⟩
      exact ⟨b ⟨s, hsS⟩, Submodule.mem_sup_right (Submodule.subset_span ⟨⟨s, hsS⟩, rfl⟩), rfl⟩
    push Not at hstd
    obtain ⟨μ, hμG, hμs⟩ := hstd
    obtain ⟨g, hgI, hc, hlow⟩ := hG μ hμG
    set k := s - μ
    have hks : k + μ = s := tsub_add_cancel_of_le hμs
    have hdeg : k.degree + μ.degree = d := by rw [← map_add, hks]; exact hs
    -- h := X^k * g lies in Q (as an element of V)
    have hh : monomial k (1 : K) * g ∈ W := by
      have h1 := monomial_mul_mem_relSpan t k hgI
      rw [hdeg] at h1
      obtain ⟨y, hy, hyv⟩ := relSpan_le_map t ht d h1
      exact ⟨y, Submodule.mem_sup_left hy, hyv⟩
    -- expand h
    have hexp : monomial k (1 : K) * g =
        g.coeff μ • monomial s 1 + ∑ u ∈ g.support.erase μ, g.coeff u • monomial (k + u) 1 := by
      conv_lhs => rw [g.as_sum]
      rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (mem_support_iff.mpr hc)]
      simp only [monomial_mul_monomial, one_mul, smul_monomial, smul_eq_mul, mul_one, hks]
    have hrest : ∑ u ∈ g.support.erase μ, g.coeff u • monomial (k + u) (1 : K) ∈ W := by
      refine Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ ?_
      obtain ⟨hne, hu⟩ := Finset.mem_erase.mp hu
      obtain ⟨hlt, hud⟩ := hlow u hu hne
      have hkd : (k + u).degree = d := by rw [map_add, hud, hdeg]
      refine IH (k + u) hkd ?_
      have := hr u μ k hlt
      rwa [add_comm u k, add_comm μ k, hks] at this
    have : g.coeff μ • monomial s (1 : K) ∈ W := by
      have := Submodule.sub_mem _ hh hrest
      rwa [hexp, add_sub_cancel_right] at this
    have := Submodule.smul_mem W (g.coeff μ)⁻¹ this
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  -- hence Q ⊔ B = ⊤
  have htop : Q ⊔ B = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨v, hv⟩ -
    have hvW : v ∈ W := by
      rw [v.as_sum]
      refine Submodule.sum_mem _ fun u hu => ?_
      have hud : u.degree = d := by
        have := (mem_homogeneousSubmodule d v).mp hv (mem_support_iff.mp hu)
        rw [Finsupp.degree_eq_weight_one]; exact this
      have := Submodule.smul_mem W (v.coeff u) (key u hud)
      rwa [smul_monomial, smul_eq_mul, mul_one] at this
    obtain ⟨y, hy, hyv⟩ := hvW
    have : y = ⟨v, hv⟩ := Subtype.ext hyv
    rwa [← this]
  -- the composite B → V ⧸ Q is surjective
  let f : B →ₗ[K] V ⧸ Q := Q.mkQ ∘ₗ B.subtype
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := Q.mkQ_surjective q
    have hv : v ∈ Q ⊔ B := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, c, hcB, rfl⟩ := Submodule.mem_sup.mp hv
    refine ⟨⟨c, hcB⟩, ?_⟩
    simp only [f, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, map_add,
      (Submodule.Quotient.mk_eq_zero Q).mpr ha, zero_add, Submodule.mkQ_apply]
  have : FiniteDimensional K B := FiniteDimensional.span_of_finite K (Set.finite_range b)
  have h1 : finrank K (V ⧸ Q) ≤ finrank K B := by
    have := LinearMap.finrank_range_le f
    rwa [LinearMap.range_eq_top.mpr hf, finrank_top] at this
  have h2 : finrank K B ≤ Fintype.card ι := finrank_range_le_card b
  have h3 : Fintype.card ι ≤ S.card := by
    simp only [ι, Fintype.card_coe]; exact Finset.card_filter_le _ _
  exact h1.trans (h2.trans h3)

end Mono
