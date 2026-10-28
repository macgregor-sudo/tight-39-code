module

/-
First-party interfaces and proof scripts; no upstream proof body is copied
or adapted. This is classical finite-filtration dimension additivity, not
new associated-graded mathematics. Background: Stacks Project Sections 10.52
and 10.59, tags 00IV and 00K4, on additivity and graded length decomposition:
https://stacks.math.columbia.edu/tag/00IV
https://stacks.math.columbia.edu/tag/00K4

Import-only provenance at mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55,
Lean v4.35.0-rc2: Quotient/Basic and Isomorphisms (Johannes Hölzl,
Mario Carneiro, Kevin Buzzard, Yury Kudryashov); Submodule/Equiv (the same
authors, Frédéric Dupuis, Heather Macbeth); Dimension/RankNullity (Andrew
Yang); RingTheory/Finiteness/Basic (Johan Commelin). These file headers and
the root LICENSE specify Apache-2.0. APIs are imported and called by name,
not copied. Existing monomial-section and actual ideal-power provenance is
retained in the unchanged passed predecessors and attribution ledger.
Thank you to these authors and all Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

public import PolynomialJetPrerequisitesModule

@[expose] public section

/-!
# The literal finite polynomial jets and their actual degree layers

Every quotient uses the same actual equation family g and the genuine
variable-ideal power. Canonical projection kernels are derived, not assumed.
The finite coefficient-domain surjection proves finiteness without treating
the ambient polynomial ring or an ideal power as finite-dimensional.

No point, quadratic-degree, annihilator, rank, terminal-plane or geometric
hypothesis enters this filtration. The eventual covering-relation bound is
a separate application of these exact dimension identities.
-/

namespace PolynomialJets

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ ι R : Type*} [CommRing R]

/-- Transparent notation for the existing literal original-ideal jet quotient. -/
abbrev equationJet (g : ι → MvPolynomial σ R) (N : ℕ) :=
  MvPolynomial σ R ⧸ equationJetSubmodule g N

/-- The higher variable-ideal power gives the smaller actual relation submodule. -/
theorem equationJetSubmodule_succ_le (g : ι → MvPolynomial σ R) (n : ℕ) :
    equationJetSubmodule g (n+1) ≤ equationJetSubmodule g n := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range g)
  let a : Ideal (MvPolynomial σ R) := Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  have hPower : a ^ ((n+1)+1) ≤ a ^ (n+1) :=
    Ideal.pow_le_pow_right (Nat.le_succ (n+1))
  intro p hp
  change p ∈ I ⊔ a ^ ((n+1)+1) at hp
  change p ∈ I ⊔ a ^ (n+1)
  exact (sup_le_sup_left hPower I) hp

/-- Canonical projection sends the actual polynomial class to the same class. -/
def equationJetProjection (g : ι → MvPolynomial σ R) (n : ℕ) :
    equationJet g (n+1) →ₗ[R] equationJet g n :=
  Submodule.factor (equationJetSubmodule_succ_le g n)

@[simp] theorem equationJetProjection_apply_mk
    (g : ι → MvPolynomial σ R) (n : ℕ) (p : MvPolynomial σ R) :
    equationJetProjection g n (Submodule.Quotient.mk p) = Submodule.Quotient.mk p := rfl

theorem equationJetProjection_surjective (g : ι → MvPolynomial σ R) (n : ℕ) :
    Function.Surjective (equationJetProjection g n) :=
  Submodule.factor_surjective (equationJetSubmodule_succ_le g n)

/-- The projection kernel is exactly the previously defined actual degree
layer inside the higher jet, not an abstract equivalent or assumed exactness. -/
theorem equationJetProjection_ker (g : ι → MvPolynomial σ R) (n : ℕ) :
    LinearMap.ker (equationJetProjection g n) = equationDegreeLayer g (n+1) := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range g)
  let a : Ideal (MvPolynomial σ R) := Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  have hI : I.restrictScalars R ≤ equationJetSubmodule g (n+1) := by
    intro p hp
    exact (le_sup_left : I ≤ I ⊔ a ^ ((n+1)+1)) hp
  have hKilled : (I.restrictScalars R).map (equationJetSubmodule g (n+1)).mkQ = ⊥ := by
    apply le_antisymm _ bot_le
    calc
      _ ≤ (equationJetSubmodule g (n+1)).map (equationJetSubmodule g (n+1)).mkQ :=
        Submodule.map_mono hI
      _ = ⊥ := Submodule.mkQ_map_self _
  have hLower : equationJetSubmodule g n =
      I.restrictScalars R ⊔ (a ^ (n+1)).restrictScalars R := by
    change (I ⊔ a ^ (n+1)).restrictScalars R = _
    rw [Submodule.restrictScalars_sup]
  change LinearMap.ker
    ((equationJetSubmodule g (n+1)).mapQ (equationJetSubmodule g n)
      LinearMap.id (equationJetSubmodule_succ_le g n)) = _
  rw [Submodule.ker_mapQ, Submodule.comap_id, hLower, Submodule.map_sup, hKilled,
    bot_sup_eq]
  rfl

/-- The zero-th layer is the whole actual zero-th jet, even for a zero quotient. -/
theorem equationDegreeLayer_zero_eq_top (g : ι → MvPolynomial σ R) :
    equationDegreeLayer g 0 = ⊤ := by
  rw [equationDegreeLayer, pow_zero, Ideal.one_eq_top, Submodule.restrictScalars_top,
    Submodule.map_top, Submodule.range_mkQ]

/-- Identify the actual zero-th jet with its actual full degree-zero layer. -/
def equationJetZeroEquivLayer (g : ι → MvPolynomial σ R) :
    equationJet g 0 ≃ₗ[R] equationDegreeLayer g 0 :=
  (LinearEquiv.ofTop (equationDegreeLayer g 0) (equationDegreeLayer_zero_eq_top g)).symm

/-- The base equivalence keeps the same polynomial class after layer coercion. -/
@[simp] theorem equationJetZeroEquivLayer_apply_mk
    (g : ι → MvPolynomial σ R) (p : MvPolynomial σ R) :
    (equationJetZeroEquivLayer g (Submodule.Quotient.mk p) : equationJet g 0) =
      Submodule.Quotient.mk p := rfl

section FiniteVariables

variable [Finite σ]

/-- The actual finite coefficient-domain presentation; only its surjectivity
is asserted here, not an additional computation of its kernel. -/
def equationJetCoefficientPresentation (g : ι → MvPolynomial σ R) (N : ℕ) :
    (MonomialsUpTo σ N → R) →ₗ[R] equationJet g N :=
  (equationJetSubmodule g N).mkQ.comp (monomialSection N)

@[simp] theorem equationJetCoefficientPresentation_apply
    (g : ι → MvPolynomial σ R) (N : ℕ) (v : MonomialsUpTo σ N → R) :
    equationJetCoefficientPresentation g N v =
      (equationJetSubmodule g N).mkQ (monomialSection N v) := rfl

/-- Actual truncation differs by the genuine ideal power killed in this jet. -/
theorem equationJetCoefficientPresentation_lowCoeff
    (g : ι → MvPolynomial σ R) (N : ℕ) (p : MvPolynomial σ R) :
    equationJetCoefficientPresentation g N (lowCoeff N p) =
      (equationJetSubmodule g N).mkQ p := by
  change (equationJetSubmodule g N).mkQ (monomialSection N (lowCoeff N p)) =
    (equationJetSubmodule g N).mkQ p
  symm
  apply (Submodule.Quotient.eq (equationJetSubmodule g N)).mpr
  change p - monomialSection N (lowCoeff N p) ∈
    Ideal.span (Set.range g) ⊔
      (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1)
  exact (le_sup_right :
    (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1) ≤
      Ideal.span (Set.range g) ⊔
        (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1))
    (truncation_difference_mem_variableIdeal_pow N p)

theorem equationJetCoefficientPresentation_surjective
    (g : ι → MvPolynomial σ R) (N : ℕ) :
    Function.Surjective (equationJetCoefficientPresentation g N) := by
  intro x
  obtain ⟨p, rfl⟩ := (equationJetSubmodule g N).mkQ_surjective x
  exact ⟨lowCoeff N p, equationJetCoefficientPresentation_lowCoeff g N p⟩

/-- Actual jets are finite modules by the proved finite coefficient-domain
surjection. The polynomial ambient module is never assumed finite. -/
instance equationJet_finite (g : ι → MvPolynomial σ R) (N : ℕ) :
    Module.Finite R (equationJet g N) :=
  Module.Finite.of_surjective (equationJetCoefficientPresentation g N)
    (equationJetCoefficientPresentation_surjective g N)

end FiniteVariables

section Field

variable {K : Type*} [Field K] [Finite σ]

/-- Each actual layer is finite through its homogeneous representative map. -/
theorem equationDegreeLayer_finiteDimensional (g : ι → MvPolynomial σ K) (d : ℕ) :
    FiniteDimensional K (equationDegreeLayer g d) :=
  Module.Finite.of_surjective (homogeneousToEquationLayer g d)
    (homogeneousToEquationLayer_surjective g d)

/-- Exact finite-jet dimension additivity from the actual projection/kernel. -/
theorem equationJet_finrank_succ (g : ι → MvPolynomial σ K) (n : ℕ) :
    Module.finrank K (equationJet g (n+1)) =
      Module.finrank K (equationJet g n) +
        Module.finrank K (equationDegreeLayer g (n+1)) := by
  let q : equationJet g (n+1) →ₗ[K] equationJet g n := equationJetProjection g n
  have hq : Function.Surjective q := equationJetProjection_surjective g n
  let e : (equationJet g (n+1) ⧸ LinearMap.ker q) ≃ₗ[K] equationJet g n :=
    q.quotKerEquivOfSurjective hq
  let eLayer : LinearMap.ker q ≃ₗ[K] equationDegreeLayer g (n+1) :=
    LinearEquiv.ofEq _ _ (equationJetProjection_ker g n)
  have hRank := (LinearMap.ker q).finrank_quotient_add_finrank
  rw [e.finrank_eq, eLayer.finrank_eq] at hRank
  exact hRank.symm

/-- The exact finite sum of actual layer dimensions equals the actual jet
dimension. No covering relation or terminal-data hypothesis enters. -/
theorem equationJet_finrank_eq_sum_layers (g : ι → MvPolynomial σ K) (N : ℕ) :
    Module.finrank K (equationJet g N) =
      ∑ d ∈ Finset.range (N+1), Module.finrank K (equationDegreeLayer g d) := by
  induction N with
  | zero =>
      simpa only [Nat.zero_add, Finset.sum_range_one] using
        (equationJetZeroEquivLayer g).finrank_eq
  | succ n ih =>
      calc
        Module.finrank K (equationJet g (n+1)) =
            Module.finrank K (equationJet g n) +
              Module.finrank K (equationDegreeLayer g (n+1)) := equationJet_finrank_succ g n
        _ = (∑ d ∈ Finset.range (n+1), Module.finrank K (equationDegreeLayer g d)) +
              Module.finrank K (equationDegreeLayer g (n+1)) := by rw [ih]
        _ = _ := (Finset.sum_range_succ
          (fun d => Module.finrank K (equationDegreeLayer g d)) (n+1)).symm

end Field

end
end PolynomialJets
