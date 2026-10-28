module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.NormNum
public import Lean.Elab.Tactic.Omega

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.Algebra.Operations

public import Mathlib.LinearAlgebra.Isomorphisms

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-
First-party interfaces and proof scripts; no upstream implementation is copied
or adapted. Imports only, at mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.

Imported API provenance:
https://github.com/leanprover-community/mathlib4
Mathlib/Algebra/MvPolynomial/Eval.lean :: map_eval₂, coeff_map, map_monomial;
header authors Johannes Hölzl, Johan Commelin, Mario Carneiro.
Mathlib/Data/Finsupp/Weight.lean :: finite_of_degree_le;
header authors Antoine Chambert-Loir, María Inés de Frutos-Fernández.
Mathlib/Data/Matrix/Basic.lean supplies only the standard matrix carrier.
Inspected upstream file headers and root LICENSE: Apache-2.0.
No source changes and no copied source body; existing complete license evidence
is retained by the architecture task, experimental/jet-budget/ATTRIBUTION.md.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Matrix.Basic

@[expose] public section

/-!
# Coefficient specialization for finite polynomial jets

This module constructs the literal finite matrix of translated generator
multiples. Coefficient specialization preserves that matrix. This is the
functoriality step in the classical determinantal specialization argument
(Stacks Project, Section 15.8, tag 07Z6, Lemmas 15.8.2 and 15.8.4(3)).
The linear algebra and mathematics are established background; the interfaces
and Lean proof scripts below are independently written.

The module does not assert a cokernel presentation, rank comparison, analytic
jet comparison or any Albert-configuration bound. In an application the input
polynomials and point must be the actual original equations and actual point.
-/

namespace PolynomialJets

open MvPolynomial

noncomputable section

/-- Monomial exponents of total degree at most `N`; no ordering is needed. -/
abbrev MonomialsUpTo (σ : Type*) (N : ℕ) :=
  {d : σ →₀ ℕ // Finsupp.degree d ≤ N}

/-- A finite variable type makes every finite-degree monomial index finite. -/
noncomputable instance monomialsUpToFintype (σ : Type*) [Finite σ] (N : ℕ) :
    Fintype (MonomialsUpTo σ N) :=
  (Finsupp.finite_of_degree_le (σ := σ) N).fintype

variable {σ ι R S : Type*} [CommSemiring R] [CommSemiring S]

/-- Substitute `X_j + P_j` into the actual polynomial. -/
def translate (P : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  MvPolynomial.eval₂ MvPolynomial.C (fun j => X j + C (P j)) f

/-- Translation commutes with every coefficient map, including residue maps. -/
theorem map_translate (φ : R →+* S) (P : σ → R) (f : MvPolynomial σ R) :
    MvPolynomial.map φ (translate P f) =
      translate (fun j => φ (P j)) (MvPolynomial.map φ f) := by
  unfold translate
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext j
  simp only [Function.comp_apply, (MvPolynomial.map φ).map_add,
    MvPolynomial.map_X, MvPolynomial.map_C]

/-- Rows retain all coefficients through degree `N`; columns are all truncated
monomial multiples of the original translated generators. -/
def presentationMatrix (f : ι → MvPolynomial σ R) (P : σ → R) (N : ℕ) :
    Matrix (MonomialsUpTo σ N) (ι × MonomialsUpTo σ N) R :=
  fun β col => (monomial col.2.val 1 * translate P (f col.1)).coeff β.val

/-- Every matrix entry is the specialization of the corresponding original
coefficient. No rank, flatness or point-vanishing premise is hidden here. -/
theorem presentationMatrix_map (φ : R →+* S)
    (f : ι → MvPolynomial σ R) (P : σ → R) (N : ℕ) :
    presentationMatrix (fun i => MvPolynomial.map φ (f i)) (fun j => φ (P j)) N =
      fun β col => φ (presentationMatrix f P N β col) := by
  funext β col
  change (monomial col.2.val 1 *
      translate (fun j => φ (P j)) (MvPolynomial.map φ (f col.1))).coeff β.val =
    φ ((monomial col.2.val 1 * translate P (f col.1)).coeff β.val)
  calc
    _ = (MvPolynomial.map φ
        (monomial col.2.val 1 * translate P (f col.1))).coeff β.val := by
      rw [(MvPolynomial.map φ).map_mul, MvPolynomial.map_monomial,
        φ.map_one, map_translate]
    _ = _ := MvPolynomial.coeff_map φ _ _

/-- Actual point vanishing passes through coefficient specialization. It is
separate from matrix functoriality, which needs no vanishing hypothesis. -/
theorem eval_map_eq_zero (φ : R →+* S) (P : σ → R) (f : MvPolynomial σ R)
    (hf : MvPolynomial.eval P f = 0) :
    MvPolynomial.eval (fun j => φ (P j)) (MvPolynomial.map φ f) = 0 := by
  simpa only [Function.comp_def, hf, map_zero] using
    (MvPolynomial.map_eval φ P f).symm

end
end PolynomialJets

/-
First-party finite polynomial interfaces and proof scripts. No upstream source
body is copied or adapted. The previous passed FiniteJetCoefficients.lean is
unchanged; the combined audit inlines its exact source to avoid local-object
linkage assumptions.

Import-only provenance, mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2:
https://github.com/leanprover-community/mathlib4
Mathlib/Algebra/MvPolynomial/Basic.lean :: lcoeff, monomial, as_sum,
coeff_monomial_mul'; header authors Johannes Hölzl, Johan Commelin,
Mario Carneiro.
Mathlib/Data/Finsupp/Weight.lean :: degree_mono; header authors
Antoine Chambert-Loir, María Inés de Frutos-Fernández.
Mathlib/RingTheory/Ideal/Span.lean :: Ideal.span; header authors
Kenny Lau, Chris Hughes, Mario Carneiro.
Mathlib/LinearAlgebra/Matrix/ToLin.lean :: Matrix.range_mulVecLin;
header authors Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen.
The exact inspected root and file headers specify Apache-2.0. Imports do not
copy source. Existing complete license evidence is retained by the architecture
task; the new definitions and proof scripts are independently written.
Thank you to the named authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Low polynomial coefficients and the image of the actual ideal

This is finite-presentation mathematics for polynomial jets, not a new theorem
of local geometry. The image theorem uses the actual ideal generated by the
input polynomials. Its proof expands polynomial multipliers and discards only
monomial multiples that have no coefficient of the retained total degrees.

Coefficient functions carry their usual R-module structure. No multiplication
is invented on them. The unavailable MvPolynomial.Ideal cached object is not
required for this image theorem; the separate idealOfVars kernel/cokernel
wrapper remains an explicit successor obligation.
-/

namespace PolynomialJets

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ ι R : Type*} [CommSemiring R]

/-- The actual coefficients of total degree at most N, bundled linearly. -/
def lowCoeff (N : ℕ) :
    MvPolynomial σ R →ₗ[R] (MonomialsUpTo σ N → R) :=
  LinearMap.pi fun β => MvPolynomial.lcoeff R β.val

@[simp] theorem lowCoeff_apply (N : ℕ) (q : MvPolynomial σ R)
    (β : MonomialsUpTo σ N) : lowCoeff N q β = q.coeff β.val := rfl

/-- The kernel criterion exposes every retained coefficient. -/
theorem lowCoeff_eq_zero_iff (N : ℕ) (q : MvPolynomial σ R) :
    lowCoeff N q = 0 ↔ ∀ d : σ →₀ ℕ, Finsupp.degree d ≤ N → q.coeff d = 0 := by
  constructor
  · intro h d hd
    exact congrFun h ⟨d, hd⟩
  · intro h
    funext β
    exact h β.val β.property

section FiniteVariables

variable [Finite σ]

/-- A finite monomial section of the coefficient map, as an R-linear map. -/
def monomialSection (N : ℕ) :
    (MonomialsUpTo σ N → R) →ₗ[R] MvPolynomial σ R :=
  ∑ β : MonomialsUpTo σ N,
    (MvPolynomial.monomial β.val).comp (LinearMap.proj β)

@[simp] theorem monomialSection_apply (N : ℕ) (v : MonomialsUpTo σ N → R) :
    monomialSection N v = ∑ β : MonomialsUpTo σ N, monomial β.val (v β) := by
  simp only [monomialSection, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]

/-- Every finite coefficient tuple is realized by its finite polynomial. -/
theorem lowCoeff_monomialSection (N : ℕ) (v : MonomialsUpTo σ N → R) :
    lowCoeff N (monomialSection N v) = v := by
  classical
  funext β
  simp only [lowCoeff_apply, monomialSection_apply, coeff_sum,
    coeff_monomial, Subtype.val_inj, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem lowCoeff_surjective (N : ℕ) :
    Function.Surjective (lowCoeff (σ := σ) (R := R) N) := by
  intro v
  exact ⟨monomialSection N v, lowCoeff_monomialSection N v⟩

/-- Truncation keeps exactly the original coefficients in the retained degrees. -/
theorem coeff_monomialSection_lowCoeff (N : ℕ) (q : MvPolynomial σ R)
    (β : MonomialsUpTo σ N) :
    (monomialSection N (lowCoeff N q)).coeff β.val = q.coeff β.val := by
  exact congrFun (lowCoeff_monomialSection N (lowCoeff N q)) β

end FiniteVariables

/-- High-degree monomial multiples contribute no retained coefficients,
regardless of the other polynomial's degrees or constant term. -/
theorem lowCoeff_monomial_mul_eq_zero (N : ℕ) (d : σ →₀ ℕ)
    (a : R) (q : MvPolynomial σ R) (hd : N < Finsupp.degree d) :
    lowCoeff N (monomial d a * q) = 0 := by
  funext β
  change (monomial d a * q).coeff β.val = 0
  rw [MvPolynomial.coeff_monomial_mul']
  apply if_neg
  intro hle
  exact (Nat.not_le_of_gt hd) ((Finsupp.degree_mono hle).trans β.property)

/-- Scalar coefficients of a monomial multiplier are ordinary R-module scalars. -/
theorem monomial_mul_eq_smul (d : σ →₀ ℕ) (a : R) (q : MvPolynomial σ R) :
    monomial d a * q = a • (monomial d 1 * q) := by
  rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, MvPolynomial.C_mul_monomial, mul_one]

/-- The column span of the actual truncated monomial multiples. -/
def coefficientSpan (g : ι → MvPolynomial σ R) (N : ℕ) :
    Submodule R (MonomialsUpTo σ N → R) :=
  Submodule.span R (Set.range fun col : ι × MonomialsUpTo σ N =>
    lowCoeff N (monomial col.2.val 1 * g col.1))

/-- Every polynomial multiple of an actual generator is already in the finite
column span after taking the retained coefficients. No image equality is assumed. -/
theorem lowCoeff_mul_generator_mem (g : ι → MvPolynomial σ R) (N : ℕ)
    (i : ι) (h : MvPolynomial σ R) :
    lowCoeff N (h * g i) ∈ coefficientSpan g N := by
  classical
  have hexpand : h * g i =
      ∑ d ∈ h.support, monomial d (h.coeff d) * g i := by
    simpa only [Finset.sum_mul] using
      congrArg (fun q : MvPolynomial σ R => q * g i) (MvPolynomial.as_sum h)
  rw [hexpand, map_sum]
  apply (coefficientSpan g N).sum_mem
  intro d _
  by_cases hd : Finsupp.degree d ≤ N
  · rw [monomial_mul_eq_smul, map_smul]
    apply (coefficientSpan g N).smul_mem
    exact Submodule.subset_span ⟨(i, ⟨d, hd⟩), rfl⟩
  · rw [lowCoeff_monomial_mul_eq_zero N d (h.coeff d) (g i) (Nat.lt_of_not_ge hd)]
    exact (coefficientSpan g N).zero_mem

/-- The finite column span is exactly the low-coefficient image of the actual
polynomial ideal. This includes arbitrary polynomial multipliers, not merely
the particular low-degree multiples used to define the matrix columns. -/
theorem coefficientSpan_eq_ideal_image (g : ι → MvPolynomial σ R) (N : ℕ) :
    coefficientSpan g N =
      ((Ideal.span (Set.range g)).restrictScalars R).map (lowCoeff N) := by
  have hideal : ∀ q ∈ Ideal.span (Set.range g),
      ∀ h : MvPolynomial σ R, lowCoeff N (h * q) ∈ coefficientSpan g N := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem q hq =>
        rcases hq with ⟨i, rfl⟩
        intro h
        exact lowCoeff_mul_generator_mem g N i h
    | zero =>
        intro h
        simpa only [mul_zero, map_zero] using (coefficientSpan g N).zero_mem
    | add q r _ _ ihq ihr =>
        intro h
        rw [mul_add, map_add]
        exact (coefficientSpan g N).add_mem (ihq h) (ihr h)
    | smul a q _ ih =>
        intro h
        change lowCoeff N (h * (a * q)) ∈ coefficientSpan g N
        rw [← mul_assoc]
        exact ih (h * a)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, d⟩, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨monomial d.val 1 * g i, ?_, rfl⟩
    change monomial d.val 1 * g i ∈ Ideal.span (Set.range g)
    exact (Ideal.span (Set.range g)).mul_mem_left _
      (Ideal.subset_span ⟨i, rfl⟩)
  · intro v hv
    rcases Submodule.mem_map.mp hv with ⟨q, hq, rfl⟩
    change q ∈ Ideal.span (Set.range g) at hq
    simpa only [one_mul] using hideal q hq 1

/-- The checked original presentation matrix presents the image of its actual
translated ideal. No point-vanishing, degree or rank hypothesis is inserted. -/
theorem presentationMatrix_range [Finite σ] [Fintype ι]
    (f : ι → MvPolynomial σ R) (P : σ → R) (N : ℕ) :
    LinearMap.range (presentationMatrix f P N).mulVecLin =
      ((Ideal.span (Set.range fun i => translate P (f i))).restrictScalars R).map
        (lowCoeff N) := by
  rw [Matrix.range_mulVecLin]
  change coefficientSpan (fun i => translate P (f i)) N = _
  exact coefficientSpan_eq_ideal_image (fun i => translate P (f i)) N

end
end PolynomialJets


-- Exact-source combined audit. The passed coefficient source is inlined unchanged;
-- the image source body is inlined with only its three import lines hoisted/removed.
#check @PolynomialJets.lowCoeff
#check @PolynomialJets.monomialSection
#check @PolynomialJets.lowCoeff_eq_zero_iff
#check @PolynomialJets.lowCoeff_monomialSection
#check @PolynomialJets.lowCoeff_surjective
#check @PolynomialJets.coeff_monomialSection_lowCoeff
#check @PolynomialJets.lowCoeff_monomial_mul_eq_zero
#check @PolynomialJets.coefficientSpan_eq_ideal_image
#check @PolynomialJets.presentationMatrix_range
#print axioms PolynomialJets.lowCoeff_eq_zero_iff
#print axioms PolynomialJets.lowCoeff_monomialSection
#print axioms PolynomialJets.lowCoeff_surjective
#print axioms PolynomialJets.coeff_monomialSection_lowCoeff
#print axioms PolynomialJets.lowCoeff_monomial_mul_eq_zero
#print axioms PolynomialJets.monomial_mul_eq_smul
#print axioms PolynomialJets.lowCoeff_mul_generator_mem
#print axioms PolynomialJets.coefficientSpan_eq_ideal_image
#print axioms PolynomialJets.presentationMatrix_range

/-
First-party wrappers around imported module isomorphism theorems. No upstream
proof body is copied or adapted. All earlier passed coefficient/image sources
remain unchanged.

Import-only provenance:
https://github.com/leanprover-community/mathlib4
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Mathlib/LinearAlgebra/Isomorphisms.lean :: quotKerEquivOfSurjective;
file-header authors Johannes Hölzl, Mario Carneiro, Kevin Buzzard,
Yury Kudryashov. Its imported Submodule.comap_map_eq and quotEquivOfEq
are used by name, not copied. The inspected root and file headers specify
Apache-2.0; no source modifications. Complete license evidence is retained
in the architecture task's existing attribution material.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Module quotients and polynomial coefficient presentations

The background section is an application of the classical first isomorphism
theorem for modules (Noether's isomorphism theorems), explicitly identified as
such in mathlib's LinearAlgebra/Isomorphisms.lean. The Lean wrappers below are
independently written, not a claim of new mathematics.

The concrete application uses the actual translated polynomial ideal, the
actual coefficient-map kernel and the actual matrix range already proved in
FiniteJetImage. No power of idealOfVars, analytic jet or dimension result is
asserted. The coefficient functions are used only as a module.
-/

namespace ModuleQuotients

noncomputable section

section FirstIsomorphism

variable {R M V : Type*} [Ring R] [AddCommGroup M] [AddCommGroup V]
  [Module R M] [Module R V]

/-- The actual composite from M to the quotient of V by the image of J. -/
def quotientComposite (L : M →ₗ[R] V) (J : Submodule R M) :
    M →ₗ[R] V ⧸ J.map L :=
  (J.map L).mkQ.comp L

/-- The kernel formula for the first-isomorphism application is proved from
the actual image; it is not supplied as a hypothesis. -/
theorem ker_quotientComposite (L : M →ₗ[R] V) (J : Submodule R M) :
    LinearMap.ker (quotientComposite L J) = J ⊔ LinearMap.ker L := by
  rw [quotientComposite, LinearMap.ker_comp, Submodule.ker_mkQ,
    Submodule.comap_map_eq]

theorem quotientComposite_surjective (L : M →ₗ[R] V)
    (hL : Function.Surjective L) (J : Submodule R M) :
    Function.Surjective (quotientComposite L J) :=
  (J.map L).mkQ_surjective.comp hL

/-- Classical first isomorphism theorem applied after quotienting the target
by the actual image of J. The representative m maps to the class of L(m). -/
def quotientByImageEquiv (L : M →ₗ[R] V) (hL : Function.Surjective L)
    (J : Submodule R M) :
    (M ⧸ (J ⊔ LinearMap.ker L)) ≃ₗ[R] V ⧸ J.map L :=
  (Submodule.quotEquivOfEq _ _ (ker_quotientComposite L J).symm).trans
    ((quotientComposite L J).quotKerEquivOfSurjective
      (quotientComposite_surjective L hL J))

/-- The first-isomorphism equivalence preserves the intended representatives. -/
@[simp] theorem quotientByImageEquiv_apply_mk (L : M →ₗ[R] V)
    (hL : Function.Surjective L) (J : Submodule R M) (m : M) :
    quotientByImageEquiv L hL J (Submodule.Quotient.mk m) =
      Submodule.Quotient.mk (L m) := by
  -- The equality transport is identity on representatives. The remaining map
  -- is the imported first-isomorphism map applied to this actual representative.
  change ((quotientComposite L J).quotKerEquivOfSurjective
    (quotientComposite_surjective L hL J)) (Submodule.Quotient.mk m) = _
  rfl

end FirstIsomorphism
end
end ModuleQuotients

namespace PolynomialJets

noncomputable section

variable {σ ι R : Type*} [CommRing R] [Finite σ] [Fintype ι]

/-- The cokernel of the actual truncated presentation matrix is the quotient
by the actual translated ideal and the actual low-coefficient kernel. This
is an R-linear equivalence; the named idealOfVars-power identity is separate. -/
def presentationCokernelEquiv (f : ι → MvPolynomial σ R) (P : σ → R) (N : ℕ) :
    (MvPolynomial σ R ⧸
      ((Ideal.span (Set.range fun i => translate P (f i))).restrictScalars R ⊔
        LinearMap.ker (lowCoeff N))) ≃ₗ[R]
      (MonomialsUpTo σ N → R) ⧸
        LinearMap.range (presentationMatrix f P N).mulVecLin := by
  -- Explicit types keep elaboration at this natural representation boundary.
  let L : MvPolynomial σ R →ₗ[R] (MonomialsUpTo σ N → R) := lowCoeff N
  let J : Submodule R (MvPolynomial σ R) :=
    (Ideal.span (Set.range fun i => translate P (f i))).restrictScalars R
  let T : Submodule R (MonomialsUpTo σ N → R) :=
    LinearMap.range (presentationMatrix f P N).mulVecLin
  have hL : Function.Surjective L := lowCoeff_surjective (σ := σ) (R := R) N
  have hT : T = J.map L :=
    presentationMatrix_range (σ := σ) (ι := ι) (R := R) f P N
  let e : (MvPolynomial σ R ⧸ (J ⊔ LinearMap.ker L)) ≃ₗ[R]
      (MonomialsUpTo σ N → R) ⧸ J.map L :=
    ModuleQuotients.quotientByImageEquiv (R := R) (M := MvPolynomial σ R)
      (V := MonomialsUpTo σ N → R) L hL J
  let c : ((MonomialsUpTo σ N → R) ⧸ J.map L) ≃ₗ[R]
      (MonomialsUpTo σ N → R) ⧸ T :=
    Submodule.quotEquivOfEq (J.map L) T hT.symm
  exact e.trans c

/-- A polynomial's class maps to the class of its actual retained coefficients,
not to a separately chosen coordinate tuple or asserted quotient identification. -/
@[simp] theorem presentationCokernelEquiv_apply_mk
    (f : ι → MvPolynomial σ R) (P : σ → R) (N : ℕ) (q : MvPolynomial σ R) :
    presentationCokernelEquiv f P N (Submodule.Quotient.mk q) =
      Submodule.Quotient.mk (lowCoeff N q) := by
  -- Both equality transports are identity on representatives, and the
  -- first-isomorphism map sends q to its actual retained coefficients.
  rfl

end
end PolynomialJets


-- Exact passed image audit prefix, then the quotient source body with imports hoisted.
#check @ModuleQuotients.quotientComposite
#check @ModuleQuotients.ker_quotientComposite
#check @ModuleQuotients.quotientComposite_surjective
#check @ModuleQuotients.quotientByImageEquiv
#check @ModuleQuotients.quotientByImageEquiv_apply_mk
#check @PolynomialJets.presentationCokernelEquiv
#check @PolynomialJets.presentationCokernelEquiv_apply_mk
#print axioms ModuleQuotients.ker_quotientComposite
#print axioms ModuleQuotients.quotientComposite_surjective
#print axioms ModuleQuotients.quotientByImageEquiv
#print axioms ModuleQuotients.quotientByImageEquiv_apply_mk
#print axioms PolynomialJets.presentationCokernelEquiv
#print axioms PolynomialJets.presentationCokernelEquiv_apply_mk

/-
First-party proof scripts composing cached mathlib APIs; no upstream source
body is copied or adapted. The mathematical identity is established background,
explicitly present as MvPolynomial.pow_idealOfVars_eq_span and
mem_pow_idealOfVars_iff' in the source-inspected file below. The variable ideal
is written literally, so the unavailable compiled alias is not needed.

Import/mathematical provenance:
https://github.com/leanprover-community/mathlib4
commit 065356127b1dc0016f66b7283ce0ce2c4055aa55, Lean v4.35.0-rc2.
Mathlib/RingTheory/MvPolynomial/Ideal.lean :: pow_idealOfVars_eq_span:97,
mem_pow_idealOfVars_iff':109; source-inspected background, header Eric Wieser.
Mathlib/RingTheory/MvPolynomial/Basic.lean :: restrictSupportIdeal,
mem_restrictSupport_iff; imported, header Johannes Hölzl.
Mathlib/Algebra/Algebra/Operations.lean :: Submodule.span_pow;
imported, header Kenny Lau.
Mathlib/Data/Finsupp/Weight.lean :: exists_le_degree_eq,
image_pow_eq_finsuppProd_image; imported through the existing coefficient
source, headers Antoine Chambert-Loir and María Inés de Frutos-Fernández.
Exact file headers and root LICENSE: Apache-2.0. No source modifications.
Complete license evidence remains in the architecture task's attribution files.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Polynomial coefficient kernels are genuine variable-ideal powers

The background argument identifies upper-support ideals, degree-n monomial
ideals, and powers of the ideal generated by the actual variables. These are
classical polynomial identities, not a new filtration or a new jet definition.

All statements use the actual polynomial ring. Coefficient functions retain
their module structure. No analytic result, rank specialization, point equation,
or geometric bound is asserted. No missing dependency is built or inlined.
-/

namespace PolynomialJets

open MvPolynomial
open scoped BigOperators Pointwise

noncomputable section

variable {σ R : Type*} [CommRing R]

section MonomialIdeals

/-- The existing polynomial upper-support ideal, for total degrees at least n. -/
def degreeTailIdeal (n : ℕ) : Ideal (MvPolynomial σ R) :=
  MvPolynomial.restrictSupportIdeal R
    (Finsupp.degree (σ := σ) (R := ℕ) ⁻¹' Set.Ici n)
    ((isUpperSet_Ici n).preimage Finsupp.degree_mono)

theorem mem_degreeTailIdeal (n : ℕ) (q : MvPolynomial σ R) :
    q ∈ degreeTailIdeal n ↔ ∀ d ∈ q.support, n ≤ Finsupp.degree d := by
  change q ∈ MvPolynomial.restrictSupport R
    (Finsupp.degree (σ := σ) (R := ℕ) ⁻¹' Set.Ici n) ↔ _
  rw [MvPolynomial.mem_restrictSupport_iff]
  rfl

/-- Every high-degree monomial has a degree-n monomial factor, so the genuine
upper-support ideal is generated by its degree-n monomials. -/
theorem degreeTailIdeal_eq_monomialSpan (n : ℕ) :
    degreeTailIdeal (σ := σ) (R := R) n =
      Ideal.span ((fun d : σ →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.degree d = n}) := by
  classical
  let I : Ideal (MvPolynomial σ R) :=
    Ideal.span ((fun d : σ →₀ ℕ => monomial d (1 : R)) ''
      {d | Finsupp.degree d = n})
  change degreeTailIdeal n = I
  apply le_antisymm
  · intro q hq
    have hsupport := (mem_degreeTailIdeal n q).mp hq
    have hsum : (∑ d ∈ q.support, monomial d (q.coeff d)) ∈ I := by
      apply I.sum_mem
      intro d hd
      obtain ⟨a, had, ha⟩ := Finsupp.exists_le_degree_eq d n (hsupport d hd)
      have hgen : (monomial a (1 : R) : MvPolynomial σ R) ∈ I :=
        Ideal.subset_span ⟨a, ha, rfl⟩
      have hfactor : (monomial d (q.coeff d) : MvPolynomial σ R) =
          monomial (d-a) (q.coeff d) * monomial a 1 := by
        rw [monomial_mul_monomial, mul_one, tsub_add_cancel_of_le had]
      rw [hfactor]
      exact I.mul_mem_left _ hgen
    simpa only [MvPolynomial.support_sum_monomial_coeff] using hsum
  · apply Ideal.span_le.mpr
    rintro _ ⟨d, hd, rfl⟩
    change Finsupp.degree d = n at hd
    apply (mem_degreeTailIdeal n (monomial d (1 : R))).mpr
    intro e he
    have heq : e = d := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    subst e
    exact hd.ge

/-- A power of the actual variable ideal is generated by degree-n monomials.
The span_pow scalar ring here is the polynomial ring itself, as required for
an ideal; it is not the R-linear span of the variables. -/
theorem variableIdeal_pow_eq_monomialSpan (n : ℕ) :
    (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ n =
      Ideal.span ((fun d : σ →₀ ℕ => monomial d (1 : R)) ''
        {d | Finsupp.degree d = n}) := by
  have hproducts : (Set.range (X : σ → MvPolynomial σ R)) ^ n =
      (fun d : σ →₀ ℕ => monomial d (1 : R)) '' {d | Finsupp.degree d = n} := by
    simpa only [Set.image_univ, Set.subset_univ, and_true,
      ← MvPolynomial.monic_monomial_eq] using
      (Finsupp.image_pow_eq_finsuppProd_image
        (f := (X : σ → MvPolynomial σ R)) (s := Set.univ) (n := n))
  rw [Ideal.span, Submodule.span_pow, hproducts]

end MonomialIdeals

/-- The exact coefficient kernel is the scalar restriction of the genuine
polynomial upper-support ideal. No finiteness, rank or point hypothesis occurs. -/
theorem lowCoeff_ker_eq_degreeTailIdeal (N : ℕ) :
    LinearMap.ker (lowCoeff (σ := σ) (R := R) N) =
      (degreeTailIdeal (σ := σ) (R := R) (N+1)).restrictScalars R := by
  classical
  ext q
  change lowCoeff N q = 0 ↔ q ∈ degreeTailIdeal (N+1)
  rw [lowCoeff_eq_zero_iff, mem_degreeTailIdeal]
  constructor
  · intro h d hd
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hd)
      (h d (Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)))
  · intro h d hd
    by_contra hc
    have hdegree := h d (MvPolynomial.mem_support_iff.mpr hc)
    exact (Nat.not_succ_le_self N) (hdegree.trans hd)

/-- Public kernel endpoint: the ideal is literally generated by the actual
variables. It is definitionally mathlib's idealOfVars once that alias is imported. -/
theorem lowCoeff_ker_eq_variableIdeal_pow (N : ℕ) :
    LinearMap.ker (lowCoeff (σ := σ) (R := R) N) =
      ((Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1)).restrictScalars R := by
  rw [lowCoeff_ker_eq_degreeTailIdeal, degreeTailIdeal_eq_monomialSpan,
    variableIdeal_pow_eq_monomialSpan]

/-- Two polynomial representatives have the same retained coefficients exactly
when their difference lies in the genuine (N+1)st variable-ideal power. -/
theorem lowCoeff_eq_iff_sub_mem_variableIdeal_pow (N : ℕ)
    (q r : MvPolynomial σ R) :
    lowCoeff N q = lowCoeff N r ↔
      q-r ∈ (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1) := by
  change lowCoeff N q = lowCoeff N r ↔
    q-r ∈ ((Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1)).restrictScalars R
  rw [← lowCoeff_ker_eq_variableIdeal_pow, LinearMap.mem_ker, map_sub, sub_eq_zero]

/-- Finite monomial truncation represents the original polynomial modulo the
actual variable-ideal power, including N=0 and an empty variable type. -/
theorem truncation_difference_mem_variableIdeal_pow [Finite σ] (N : ℕ)
    (q : MvPolynomial σ R) :
    q - monomialSection N (lowCoeff N q) ∈
      (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1) := by
  apply (lowCoeff_eq_iff_sub_mem_variableIdeal_pow N q _).mp
  exact (lowCoeff_monomialSection N (lowCoeff N q)).symm

end
end PolynomialJets


-- Exact passed quotient audit retained; kernel source imports hoisted/removed.
#check @PolynomialJets.degreeTailIdeal
#check @PolynomialJets.mem_degreeTailIdeal
#check @PolynomialJets.degreeTailIdeal_eq_monomialSpan
#check @PolynomialJets.variableIdeal_pow_eq_monomialSpan
#check @PolynomialJets.lowCoeff_ker_eq_degreeTailIdeal
#check @PolynomialJets.lowCoeff_ker_eq_variableIdeal_pow
#check @PolynomialJets.lowCoeff_eq_iff_sub_mem_variableIdeal_pow
#check @PolynomialJets.truncation_difference_mem_variableIdeal_pow
#print axioms PolynomialJets.mem_degreeTailIdeal
#print axioms PolynomialJets.degreeTailIdeal_eq_monomialSpan
#print axioms PolynomialJets.variableIdeal_pow_eq_monomialSpan
#print axioms PolynomialJets.lowCoeff_ker_eq_degreeTailIdeal
#print axioms PolynomialJets.lowCoeff_ker_eq_variableIdeal_pow
#print axioms PolynomialJets.lowCoeff_eq_iff_sub_mem_variableIdeal_pow
#print axioms PolynomialJets.truncation_difference_mem_variableIdeal_pow
/-
First-party interfaces and proof scripts; no upstream source body is copied
or adapted. This is classical polynomial filtration mathematics, not a claim
of a new associated-graded theorem. The canonical polynomial-to-graded-piece
surjection is the elementary degree-wise construction underlying Stacks
Project, Section 10.69, equation (10.69.0.1), tag 061M:
https://stacks.math.columbia.edu/tag/061M . Here the target is written directly
as the image of the degree-d variable-ideal power in the actual finite jet.

Import-only provenance, mathlib commit
065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2:
Mathlib/RingTheory/MvPolynomial/Homogeneous.lean :: homogeneousSubmodule,
homogeneousComponent, coeff_homogeneousComponent,
homogeneousComponent_eq_self, support_homogeneousComponent;
header authors Johan Commelin, Eric Wieser; Apache-2.0.
Mathlib/Data/Finsupp/Weight.lean :: degree_eq_zero_iff, range_single_one;
header authors Antoine Chambert-Loir, María Inés de Frutos-Fernández.
The existing first-party ideal-power/coefficient source is imported unchanged.
The exact root/file license evidence is retained in the architecture ledger.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Homogeneous polynomials and the degree layer of the actual polynomial jet

The equations `g` generate the actual ideal throughout. The degree-layer map
does not assume an ideal presentation, surjectivity, initial ideal, point
condition or rank assertion. Its surjectivity is proved here. For quadratic
equations with zero constant term, the source also proves the actual linear
and quadratic decomposition and turns coefficient-level annihilation of their
linear parts into homogeneous quadratic members of the same original ideal.

This module does not yet factor the degree map by the homogeneous ideal
generated by selected linear parts and annihilator quadrics. That next step
requires the degree-sensitive homogeneous-multiplier argument, not merely
membership of every selected linear part in `I + a^2`. No dimension, all-order
growth, analytic or geometric bound is claimed here.
-/

namespace PolynomialJets

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ ι R : Type*} [CommRing R]

/-- The actual variable-ideal power, characterized by its monomial support. -/
theorem mem_variableIdeal_pow_iff (d : ℕ) (p : MvPolynomial σ R) :
    p ∈ (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ d ↔
      ∀ e ∈ p.support, d ≤ Finsupp.degree e := by
  rw [variableIdeal_pow_eq_monomialSpan, ← degreeTailIdeal_eq_monomialSpan,
    mem_degreeTailIdeal]

/-- A degree-d homogeneous polynomial belongs to the genuine d-th variable
ideal power. This includes degree zero and an empty variable type. -/
theorem homogeneous_mem_variableIdeal_pow (d : ℕ) (p : MvPolynomial σ R)
    (hp : p.IsHomogeneous d) :
    p ∈ (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ d := by
  rw [← homogeneousComponent_eq_self hp]
  apply (mem_variableIdeal_pow_iff d _).mpr
  intro e he
  rw [support_homogeneousComponent] at he
  exact (Finset.mem_filter.mp he).2.ge

/-- For a polynomial already of order at least d, removing its degree-d part
raises its order. No finite-variable, field or Noetherian hypothesis is used. -/
theorem sub_homogeneousComponent_mem_variableIdeal_pow (d : ℕ)
    (p : MvPolynomial σ R)
    (hp : p ∈ (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ d) :
    p - homogeneousComponent d p ∈
      (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (d+1) := by
  classical
  apply (mem_variableIdeal_pow_iff (d+1) _).mpr
  intro e he
  have hc := MvPolynomial.mem_support_iff.mp he
  have hsub : (p - homogeneousComponent d p).coeff e =
      p.coeff e - (homogeneousComponent d p).coeff e :=
    map_sub (MvPolynomial.lcoeff R e) p (homogeneousComponent d p)
  rw [hsub, coeff_homogeneousComponent] at hc
  by_cases hed : Finsupp.degree e = d
  · simp only [if_pos hed, sub_self, ne_eq, not_true_eq_false] at hc
  · have hep : p.coeff e ≠ 0 := by
      simpa only [if_neg hed, sub_zero] using hc
    have hle := (mem_variableIdeal_pow_iff d p).mp hp e
      (MvPolynomial.mem_support_iff.mpr hep)
    exact Nat.succ_le_iff.mpr (lt_of_le_of_ne hle (Ne.symm hed))

/-- The literal original equation ideal plus the (N+1)-st variable-ideal power,
viewed only as an R-submodule to form the actual polynomial module quotient. -/
def equationJetSubmodule (g : ι → MvPolynomial σ R) (N : ℕ) :
    Submodule R (MvPolynomial σ R) :=
  ((Ideal.span (Set.range g)) ⊔
    (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (N+1)).restrictScalars R

/-- The degree-d layer realized inside the actual order-d jet. It is the image
of a^d modulo I+a^(d+1), without assuming that a^d itself is finite-dimensional. -/
def equationDegreeLayer (g : ι → MvPolynomial σ R) (d : ℕ) :
    Submodule R (MvPolynomial σ R ⧸ equationJetSubmodule g d) :=
  (((Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ d).restrictScalars R).map
    (equationJetSubmodule g d).mkQ

/-- Send a homogeneous polynomial to its class in the actual equation jet. -/
def homogeneousToEquationLayer (g : ι → MvPolynomial σ R) (d : ℕ) :
    homogeneousSubmodule σ R d →ₗ[R] equationDegreeLayer g d :=
  LinearMap.codRestrict (equationDegreeLayer g d)
    ((equationJetSubmodule g d).mkQ.comp (homogeneousSubmodule σ R d).subtype)
    (fun p => Submodule.mem_map.mpr
      ⟨p.val, homogeneous_mem_variableIdeal_pow d p.val p.property, rfl⟩)

/-- The representative action is the actual polynomial quotient class. -/
theorem homogeneousToEquationLayer_apply (g : ι → MvPolynomial σ R) (d : ℕ)
    (p : homogeneousSubmodule σ R d) :
    (homogeneousToEquationLayer g d p :
      MvPolynomial σ R ⧸ equationJetSubmodule g d) =
        (equationJetSubmodule g d).mkQ p.val := rfl

/-- Every element of the degree layer has a homogeneous polynomial
representative. Surjectivity is proved from actual representatives and the
coefficient/ideal-power identity, rather than supplied as a premise. -/
theorem homogeneousToEquationLayer_surjective (g : ι → MvPolynomial σ R) (d : ℕ) :
    Function.Surjective (homogeneousToEquationLayer g d) := by
  intro x
  obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.property
  let q : homogeneousSubmodule σ R d :=
    ⟨homogeneousComponent d p, homogeneousComponent_mem d p⟩
  refine ⟨q, Subtype.ext ?_⟩
  change (equationJetSubmodule g d).mkQ (homogeneousComponent d p) = x.val
  calc
    _ = (equationJetSubmodule g d).mkQ p := by
      symm
      apply (Submodule.Quotient.eq (equationJetSubmodule g d)).mpr
      change p - homogeneousComponent d p ∈
        (Ideal.span (Set.range g)) ⊔
          (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (d+1)
      exact (le_sup_right :
        (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (d+1) ≤
          (Ideal.span (Set.range g)) ⊔
            (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (d+1))
        (sub_homogeneousComponent_mem_variableIdeal_pow d p hp)
    _ = x.val := hpx

section QuadraticEquations

/-- A quadratic polynomial vanishing at zero is exactly its linear part plus
its quadratic part. Both parts are computed from the actual polynomial. -/
theorem quadratic_eq_linear_add_quadratic (p : MvPolynomial σ R)
    (hdegree : p.totalDegree ≤ 2) (hzero : p.coeff 0 = 0) :
    p = homogeneousComponent 1 p + homogeneousComponent 2 p := by
  classical
  ext e
  have hadd : (homogeneousComponent 1 p + homogeneousComponent 2 p).coeff e =
      (homogeneousComponent 1 p).coeff e + (homogeneousComponent 2 p).coeff e :=
    map_add (MvPolynomial.lcoeff R e) (homogeneousComponent 1 p) (homogeneousComponent 2 p)
  rw [hadd, coeff_homogeneousComponent, coeff_homogeneousComponent]
  by_cases he0 : Finsupp.degree e = 0
  · have he : e = 0 := (Finsupp.degree_eq_zero_iff e).mp he0
    subst e
    simp [hzero]
  · by_cases he1 : Finsupp.degree e = 1
    · simp [he1]
    · by_cases he2 : Finsupp.degree e = 2
      · simp [he2]
      · have hhigh : p.totalDegree < Finsupp.degree e := by omega
        have hc : p.coeff e = 0 := coeff_eq_zero_of_totalDegree_lt hhigh
        simp only [if_neg he1, if_neg he2, hc, add_zero]

/-- The actual degree-one coefficient matrix, before any row/column selection. -/
def equationLinearMatrix (g : ι → MvPolynomial σ R) (i : ι) (j : σ) : R :=
  (g i).coeff (Finsupp.single j 1)

variable [Fintype ι]

/-- Coefficient-wise annihilation of the actual linear matrix annihilates the
whole linear polynomial combination, including every degree-one monomial. -/
theorem annihilator_linearCombination_eq_zero (g : ι → MvPolynomial σ R)
    (weights : ι → R)
    (hAnnihilates : ∀ j, ∑ i, weights i * equationLinearMatrix g i j = 0) :
    (∑ i, weights i • homogeneousComponent 1 (g i)) = 0 := by
  classical
  ext e
  have hzeroCoeff : (0 : MvPolynomial σ R).coeff e = 0 :=
    map_zero (MvPolynomial.lcoeff R e)
  rw [coeff_sum, hzeroCoeff]
  by_cases he : Finsupp.degree e = 1
  · simp only [coeff_smul, coeff_homogeneousComponent, if_pos he, smul_eq_mul]
    obtain ⟨j, hj⟩ : e ∈ Set.range (fun j : σ => Finsupp.single j 1) := by
      rw [Finsupp.range_single_one]
      exact he
    rw [← hj]
    exact hAnnihilates j
  · simp only [coeff_smul, coeff_homogeneousComponent, if_neg he, smul_zero,
      Finset.sum_const_zero]

/-- The quadratic relation computed from an actual full annihilator. -/
def equationAnnihilatorQuadric (g : ι → MvPolynomial σ R) (weights : ι → R) :
    MvPolynomial σ R := ∑ i, weights i • homogeneousComponent 2 (g i)

/-- The actual annihilator relation is homogeneous of degree two, including
the possibility that the relation is the zero polynomial. -/
theorem equationAnnihilatorQuadric_isHomogeneous (g : ι → MvPolynomial σ R)
    (weights : ι → R) : (equationAnnihilatorQuadric g weights).IsHomogeneous 2 := by
  change (∑ i, weights i • homogeneousComponent 2 (g i)) ∈ homogeneousSubmodule σ R 2
  apply (homogeneousSubmodule σ R 2).sum_mem
  intro i _
  exact (homogeneousSubmodule σ R 2).smul_mem (weights i) (homogeneousComponent_mem 2 (g i))

/-- A full annihilator supplies a genuine quadratic member of the original
equation ideal. The relation is not inferred from a reduced tangent table. -/
theorem equationAnnihilatorQuadric_mem (g : ι → MvPolynomial σ R) (weights : ι → R)
    (hdegree : ∀ i, (g i).totalDegree ≤ 2) (hzero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ j, ∑ i, weights i * equationLinearMatrix g i j = 0) :
    equationAnnihilatorQuadric g weights ∈ Ideal.span (Set.range g) := by
  classical
  have hsum : (∑ i, weights i • g i) ∈ Ideal.span (Set.range g) := by
    apply ((Ideal.span (Set.range g)).restrictScalars R).sum_mem
    intro i _
    exact ((Ideal.span (Set.range g)).restrictScalars R).smul_mem (weights i)
      (Ideal.subset_span ⟨i, rfl⟩)
  have heq : (∑ i, weights i • g i) = equationAnnihilatorQuadric g weights := by
    calc
      _ = ∑ i, (weights i • homogeneousComponent 1 (g i) +
          weights i • homogeneousComponent 2 (g i)) := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          weights i • g i = weights i • (homogeneousComponent 1 (g i) +
              homogeneousComponent 2 (g i)) :=
            congrArg (fun p : MvPolynomial σ R => weights i • p)
              (quadratic_eq_linear_add_quadratic (g i) (hdegree i) (hzero i))
          _ = _ := smul_add _ _ _
      _ = (∑ i, weights i • homogeneousComponent 1 (g i)) +
          (∑ i, weights i • homogeneousComponent 2 (g i)) := Finset.sum_add_distrib
      _ = equationAnnihilatorQuadric g weights := by
        rw [annihilator_linearCombination_eq_zero g weights hAnnihilates, zero_add]
        rfl
  exact heq ▸ hsum

/-- Each actual linear part is an original equation modulo order two. This
alone does not prove the later degree-sensitive ideal-kernel inclusion. -/
theorem equationLinearPart_mem_ideal_sup_square (g : ι → MvPolynomial σ R) (i : ι)
    (hdegree : (g i).totalDegree ≤ 2) (hzero : (g i).coeff 0 = 0) :
    homogeneousComponent 1 (g i) ∈ (Ideal.span (Set.range g)) ⊔
      (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ 2 := by
  have hsplit := quadratic_eq_linear_add_quadratic (g i) hdegree hzero
  have heq : homogeneousComponent 1 (g i) = g i - homogeneousComponent 2 (g i) :=
    (eq_sub_iff_add_eq).mpr hsplit.symm
  rw [heq]
  apply Submodule.sub_mem
  · have hIncludeIdeal : Ideal.span (Set.range g) ≤
        (Ideal.span (Set.range g)) ⊔
          (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ 2 := le_sup_left
    exact hIncludeIdeal (Ideal.subset_span ⟨i, rfl⟩)
  · have hIncludeSquare : (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ 2 ≤
        (Ideal.span (Set.range g)) ⊔
          (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ 2 := le_sup_right
    exact hIncludeSquare (homogeneous_mem_variableIdeal_pow 2 _
      (homogeneousComponent_isHomogeneous 2 (g i)))

end QuadraticEquations

end
end PolynomialJets

#check @PolynomialJets.mem_variableIdeal_pow_iff
#check @PolynomialJets.homogeneous_mem_variableIdeal_pow
#check @PolynomialJets.sub_homogeneousComponent_mem_variableIdeal_pow
#check @PolynomialJets.equationJetSubmodule
#check @PolynomialJets.equationDegreeLayer
#check @PolynomialJets.homogeneousToEquationLayer
#check @PolynomialJets.homogeneousToEquationLayer_apply
#check @PolynomialJets.homogeneousToEquationLayer_surjective
#check @PolynomialJets.quadratic_eq_linear_add_quadratic
#check @PolynomialJets.equationLinearMatrix
#check @PolynomialJets.annihilator_linearCombination_eq_zero
#check @PolynomialJets.equationAnnihilatorQuadric
#check @PolynomialJets.equationAnnihilatorQuadric_isHomogeneous
#check @PolynomialJets.equationAnnihilatorQuadric_mem
#check @PolynomialJets.equationLinearPart_mem_ideal_sup_square

#print axioms PolynomialJets.mem_variableIdeal_pow_iff
#print axioms PolynomialJets.homogeneous_mem_variableIdeal_pow
#print axioms PolynomialJets.sub_homogeneousComponent_mem_variableIdeal_pow
#print axioms PolynomialJets.homogeneousToEquationLayer_apply
#print axioms PolynomialJets.homogeneousToEquationLayer_surjective
#print axioms PolynomialJets.quadratic_eq_linear_add_quadratic
#print axioms PolynomialJets.annihilator_linearCombination_eq_zero
#print axioms PolynomialJets.equationAnnihilatorQuadric_isHomogeneous
#print axioms PolynomialJets.equationAnnihilatorQuadric_mem
#print axioms PolynomialJets.equationLinearPart_mem_ideal_sup_square
/-
First-party interfaces and proof scripts; no upstream source body is copied
or adapted. The mathematics is the elementary homogeneous-relation quotient
map in the degree filtration, underlying the canonical surjection of Stacks
Project, Section 10.69, equation (10.69.0.1), tag 061M:
https://stacks.math.columbia.edu/tag/061M . This source proves a restricted
degree-wise factor map; it does not identify a complete initial ideal.

Import-only provenance: unchanged first-party PolynomialFilteredDegree,
with mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55 and Lean
v4.35.0-rc2. Its cached upstream closure supplies Ideal.mul_mem_mul,
Ideal.mul_mem_left, Submodule.span_le and Submodule.liftQ. File headers and
the root mathlib LICENSE specify Apache-2.0; no upstream modification.
Ideal.Operations/Defs authors Kenny Lau, Chris Hughes, Mario Carneiro;
the polynomial homogeneous APIs credit Johan Commelin and Eric Wieser.
The preceding module retains the complete import/math provenance.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Actual homogeneous relation multiples in the polynomial degree layer

All generators, linear parts, coefficient matrices and annihilator quadrics
come from the same actual equation family `g`. The relation subspace is
defined as the span of explicit products with homogeneous multiplier witnesses.
Its kernel inclusion is proved using the actual ideal and actual variable-ideal
powers, not assumed as a certificate field.

No equality with `H_d ∩ B`, where B is the full homogeneous relation ideal,
is asserted. Calling this the full degree piece of that polynomial quotient
would require the separate homogeneous-multiplier theorem. A direct cut
recurrence instead needs proved multiplication compatibility for these spans
and the actual terminal substitution kernel; neither is assumed here.
No dimension, all-order, analytic or geometric result is claimed.
-/

namespace PolynomialJets

open MvPolynomial
open scoped BigOperators

noncomputable section

variable {σ ι ε κ R : Type*} [CommRing R] [Fintype ι]

/-- Literal selected-linear-part products in degree d. The equation r+1=d
ensures the correct degree and makes the degree-zero family empty. -/
def selectedLinearDegreeRelations (g : ι → MvPolynomial σ R) (E : ε → ι) (d : ℕ) :
    Set (homogeneousSubmodule σ R d) :=
  {p | ∃ e : ε, ∃ r : ℕ, r+1=d ∧ ∃ a : homogeneousSubmodule σ R r,
    p.val = a.val * homogeneousComponent 1 (g (E e))}

/-- Literal annihilator-quadric products in degree d. The equation r+2=d
automatically excludes these relations in degrees zero and one. -/
def annihilatorQuadricDegreeRelations (g : ι → MvPolynomial σ R)
    (weights : κ → ι → R) (d : ℕ) : Set (homogeneousSubmodule σ R d) :=
  {p | ∃ s : κ, ∃ r : ℕ, r+2=d ∧ ∃ a : homogeneousSubmodule σ R r,
    p.val = a.val * equationAnnihilatorQuadric g (weights s)}

/-- The explicit degree-d relation span. This name does not assert equality
with the degree-d intersection of a polynomial ideal. -/
def equationDegreeRelations (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (d : ℕ) : Submodule R (homogeneousSubmodule σ R d) :=
  Submodule.span R (selectedLinearDegreeRelations g E d ∪
    annihilatorQuadricDegreeRelations g weights d)

/-- A homogeneous multiplier times an actual linear part is an original
equation multiple modulo the exact next variable-ideal power. -/
theorem homogeneous_mul_linearPart_mem_equationJetSubmodule
    (g : ι → MvPolynomial σ R) (i : ι) (r d : ℕ)
    (a : homogeneousSubmodule σ R r) (hDegree : r+1=d)
    (hQuadratic : (g i).totalDegree ≤ 2) (hZero : (g i).coeff 0 = 0) :
    a.val * homogeneousComponent 1 (g i) ∈ equationJetSubmodule g d := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range g)
  let A : Ideal (MvPolynomial σ R) :=
    Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  have hSplit := quadratic_eq_linear_add_quadratic (g i) hQuadratic hZero
  have hLinear : homogeneousComponent 1 (g i) = g i - homogeneousComponent 2 (g i) :=
    (eq_sub_iff_add_eq).mpr hSplit.symm
  have hProduct : a.val * homogeneousComponent 1 (g i) =
      a.val * g i - a.val * homogeneousComponent 2 (g i) := by
    calc
      _ = a.val * (g i - homogeneousComponent 2 (g i)) :=
        congrArg (fun p : MvPolynomial σ R => a.val * p) hLinear
      _ = _ := mul_sub _ _ _
  have hOriginal : a.val * g i ∈ I :=
    I.mul_mem_left a.val (Ideal.subset_span ⟨i, rfl⟩)
  have hMultiplier : a.val ∈ A ^ r :=
    homogeneous_mem_variableIdeal_pow r a.val a.property
  have hQuadraticOrder : homogeneousComponent 2 (g i) ∈ A ^ 2 :=
    homogeneous_mem_variableIdeal_pow 2 _ (homogeneousComponent_isHomogeneous 2 (g i))
  have hTail : a.val * homogeneousComponent 2 (g i) ∈ A ^ r * A ^ 2 :=
    Ideal.mul_mem_mul hMultiplier hQuadraticOrder
  have hNextDegree : r+2=d+1 := by omega
  rw [← pow_add, hNextDegree] at hTail
  change a.val * homogeneousComponent 1 (g i) ∈ I ⊔ A ^ (d+1)
  rw [hProduct]
  apply Submodule.sub_mem
  · have hInclude : I ≤ I ⊔ A ^ (d+1) := le_sup_left
    exact hInclude hOriginal
  · have hInclude : A ^ (d+1) ≤ I ⊔ A ^ (d+1) := le_sup_right
    exact hInclude hTail

/-- Every polynomial multiple of an actual full-annihilator quadric lies in
the original ideal, hence in each actual jet submodule. -/
theorem mul_annihilatorQuadric_mem_equationJetSubmodule
    (g : ι → MvPolynomial σ R) (weights : ι → R) (d : ℕ) (a : MvPolynomial σ R)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hZero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ j, ∑ i, weights i * equationLinearMatrix g i j = 0) :
    a * equationAnnihilatorQuadric g weights ∈ equationJetSubmodule g d := by
  let I : Ideal (MvPolynomial σ R) := Ideal.span (Set.range g)
  have hRelation : equationAnnihilatorQuadric g weights ∈ I :=
    equationAnnihilatorQuadric_mem g weights hQuadratic hZero hAnnihilates
  have hProduct : a * equationAnnihilatorQuadric g weights ∈ I :=
    I.mul_mem_left a hRelation
  have hInclude : I ≤ I ⊔
      (Ideal.span (Set.range (X : σ → MvPolynomial σ R))) ^ (d+1) := le_sup_left
  exact hInclude hProduct

/-- The actual relation span is killed by the canonical degree map. The
degree-sensitive ideal-power argument is proved above, not an input premise. -/
theorem equationDegreeRelations_le_ker (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (d : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hZero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0) :
    equationDegreeRelations g E weights d ≤ LinearMap.ker (homogeneousToEquationLayer g d) := by
  apply Submodule.span_le.mpr
  intro p hp
  change homogeneousToEquationLayer g d p = 0
  apply Subtype.ext
  change (equationJetSubmodule g d).mkQ p.val = 0
  apply (Submodule.Quotient.mk_eq_zero (equationJetSubmodule g d)).mpr
  rcases hp with hLinear | hQuadric
  · obtain ⟨e, r, hDegree, a, hProduct⟩ := hLinear
    rw [hProduct]
    exact homogeneous_mul_linearPart_mem_equationJetSubmodule g (E e) r d a hDegree
      (hQuadratic (E e)) (hZero (E e))
  · obtain ⟨s, r, _hDegree, a, hProduct⟩ := hQuadric
    rw [hProduct]
    exact mul_annihilatorQuadric_mem_equationJetSubmodule g (weights s) d a.val
      hQuadratic hZero (hAnnihilates s)

/-- Factor the canonical homogeneous map by the explicitly generated actual
degree relations. No ideal-intersection equality is contained in the definition. -/
def factoredHomogeneousToEquationLayer (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (d : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hZero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0) :
    (homogeneousSubmodule σ R d ⧸ equationDegreeRelations g E weights d) →ₗ[R]
      equationDegreeLayer g d :=
  (equationDegreeRelations g E weights d).liftQ (homogeneousToEquationLayer g d)
    (equationDegreeRelations_le_ker g E weights d hQuadratic hZero hAnnihilates)

/-- The factor map has the original polynomial representative action. -/
theorem factoredHomogeneousToEquationLayer_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (d : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hZero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0)
    (p : homogeneousSubmodule σ R d) :
    factoredHomogeneousToEquationLayer g E weights d hQuadratic hZero hAnnihilates
      (Submodule.Quotient.mk p) = homogeneousToEquationLayer g d p := rfl

/-- The factored map is surjective because the canonical map is surjective;
neither surjectivity nor its kernel inclusion is assumed by the theorem. -/
theorem factoredHomogeneousToEquationLayer_surjective (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (d : ℕ)
    (hQuadratic : ∀ i, (g i).totalDegree ≤ 2) (hZero : ∀ i, (g i).coeff 0 = 0)
    (hAnnihilates : ∀ s j, ∑ i, weights s i * equationLinearMatrix g i j = 0) :
    Function.Surjective
      (factoredHomogeneousToEquationLayer g E weights d hQuadratic hZero hAnnihilates) := by
  intro x
  obtain ⟨p, hp⟩ := homogeneousToEquationLayer_surjective g d x
  refine ⟨Submodule.Quotient.mk p, ?_⟩
  change homogeneousToEquationLayer g d p = x
  exact hp

end
end PolynomialJets

#check @PolynomialJets.selectedLinearDegreeRelations
#check @PolynomialJets.annihilatorQuadricDegreeRelations
#check @PolynomialJets.equationDegreeRelations
#check @PolynomialJets.homogeneous_mul_linearPart_mem_equationJetSubmodule
#check @PolynomialJets.mul_annihilatorQuadric_mem_equationJetSubmodule
#check @PolynomialJets.equationDegreeRelations_le_ker
#check @PolynomialJets.factoredHomogeneousToEquationLayer
#check @PolynomialJets.factoredHomogeneousToEquationLayer_apply_mk
#check @PolynomialJets.factoredHomogeneousToEquationLayer_surjective

#print axioms PolynomialJets.homogeneous_mul_linearPart_mem_equationJetSubmodule
#print axioms PolynomialJets.mul_annihilatorQuadric_mem_equationJetSubmodule
#print axioms PolynomialJets.equationDegreeRelations_le_ker
#print axioms PolynomialJets.factoredHomogeneousToEquationLayer_apply_mk
#print axioms PolynomialJets.factoredHomogeneousToEquationLayer_surjective
/-
First-party interfaces and proof scripts; no upstream source body is copied
or adapted. This is the elementary right-exact sequence for quotienting
homogeneous degree spaces by one linear form. Multiplication need not be
injective. The underlying polynomial degree filtration is established
background (Stacks Project, Section 10.69, equation (10.69.0.1), tag 061M).

Import-only provenance: unchanged first-party PolynomialFilteredRelations,
at mathlib commit 065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2.
Its existing cached closure supplies MvPolynomial.IsHomogeneous.mul;
Submodule.mapQ, mapQ_apply, ker_mapQ, range_mapQ, mkQ_map_self; and map_sup.
Upstream header authors include Johan Commelin, Eric Wieser, Johannes Hölzl,
Mario Carneiro, Kevin Buzzard and Yury Kudryashov. The preceding sources
retain exact file/license provenance; headers/root LICENSE are Apache-2.0.
Thank you to these authors and all mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Actual linear multiplication and one cut of the explicit relation spaces

The spaces are the homogeneous polynomial spaces modulo the explicit actual
relation spans from `PolynomialFilteredRelations`. Multiplication preserves
these spans by a proved generator argument. The one-cut space is defined by
adding the range of the actual homogeneous multiplication map in each positive
degree; its projection is proved surjective and its kernel is proved equal
to the descended multiplication range. Degree zero remains unchanged.

No exactness field, ideal-intersection equality, finite-dimensionality, or
terminal-plane assertion is assumed. Cut forms are relations in these covering
degree spaces; they are not asserted to vanish in the original equation ideal.
The separate existing DegreewiseLinearCut constructor can consume these maps
after import/source review; it is not redefined or imported here.
-/

namespace PolynomialJets

open MvPolynomial

noncomputable section

variable {σ ι ε κ R : Type*} [CommRing R] [Fintype ι]

/-- Actual multiplication by a homogeneous linear polynomial. -/
def homogeneousLinearMul (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    homogeneousSubmodule σ R n →ₗ[R] homogeneousSubmodule σ R (n+1) where
  toFun a := ⟨z.val * a.val, by
    change (z.val * a.val).IsHomogeneous (n+1)
    simpa only [Nat.add_comm 1 n] using z.property.mul a.property⟩
  map_add' a b := by
    apply Subtype.ext
    exact mul_add z.val a.val b.val
  map_smul' c a := by
    apply Subtype.ext
    exact Algebra.mul_smul_comm c z.val a.val

/-- Multiplication uses the original polynomial representatives. -/
theorem homogeneousLinearMul_val (z : homogeneousSubmodule σ R 1) (n : ℕ)
    (a : homogeneousSubmodule σ R n) :
    (homogeneousLinearMul z n a).val = z.val * a.val := rfl

/-- Multiplying a literal relation generator multiplies its homogeneous
multiplier. Span closure proves stability, with no annihilation premise. -/
theorem equationDegreeRelations_stable (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    equationDegreeRelations g E weights n ≤
      (equationDegreeRelations g E weights (n+1)).comap (homogeneousLinearMul z n) := by
  apply Submodule.span_le.mpr
  intro p hp
  change homogeneousLinearMul z n p ∈ equationDegreeRelations g E weights (n+1)
  apply Submodule.subset_span
  rcases hp with hLinear | hQuadric
  · obtain ⟨e, r, hDegree, a, hProduct⟩ := hLinear
    refine Or.inl ⟨e, r+1, congrArg (fun k : ℕ => k+1) hDegree,
      homogeneousLinearMul z r a, ?_⟩
    change z.val * p.val = (z.val * a.val) * homogeneousComponent 1 (g (E e))
    rw [hProduct]
    exact (mul_assoc _ _ _).symm
  · obtain ⟨s, r, hDegree, a, hProduct⟩ := hQuadric
    have hNextDegree : (r+1)+2=(n+1) := by omega
    refine Or.inr ⟨s, r+1, hNextDegree, homogeneousLinearMul z r a, ?_⟩
    change z.val * p.val = (z.val * a.val) * equationAnnihilatorQuadric g (weights s)
    rw [hProduct]
    exact (mul_assoc _ _ _).symm

/-- The one-cut relation family. Its positive-degree added subspace is the
range of literal polynomial multiplication; degree zero is unchanged. -/
def equationLinearCutRelations (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) :
    (n : ℕ) → Submodule R (homogeneousSubmodule σ R n)
  | 0 => equationDegreeRelations g E weights 0
  | n+1 => equationDegreeRelations g E weights (n+1) ⊔
      LinearMap.range (homogeneousLinearMul z n)

/-- Descended multiplication between the actual explicit-span quotients. -/
def equationDegreeMultiplication (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    (homogeneousSubmodule σ R n ⧸ equationDegreeRelations g E weights n) →ₗ[R]
      (homogeneousSubmodule σ R (n+1) ⧸ equationDegreeRelations g E weights (n+1)) :=
  (equationDegreeRelations g E weights n).mapQ
    (equationDegreeRelations g E weights (n+1)) (homogeneousLinearMul z n)
    (equationDegreeRelations_stable g E weights z n)

/-- The actual quotient projection after one linear cut in positive degree. -/
def equationLinearCutProjection (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    (homogeneousSubmodule σ R (n+1) ⧸ equationDegreeRelations g E weights (n+1)) →ₗ[R]
      (homogeneousSubmodule σ R (n+1) ⧸ equationLinearCutRelations g E weights z (n+1)) :=
  (equationDegreeRelations g E weights (n+1)).mapQ
    (equationLinearCutRelations g E weights z (n+1)) LinearMap.id (by
      change equationDegreeRelations g E weights (n+1) ≤
        equationDegreeRelations g E weights (n+1) ⊔ LinearMap.range (homogeneousLinearMul z n)
      exact le_sup_left)

/-- Descended multiplication still multiplies the actual representatives. -/
theorem equationDegreeMultiplication_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ)
    (p : homogeneousSubmodule σ R n) :
    equationDegreeMultiplication g E weights z n (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (homogeneousLinearMul z n p) := rfl

/-- The cut projection sends each polynomial representative to itself. -/
theorem equationLinearCutProjection_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ)
    (p : homogeneousSubmodule σ R (n+1)) :
    equationLinearCutProjection g E weights z n (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk p := rfl

/-- Every class after the cut has the same polynomial representative before it. -/
theorem equationLinearCutProjection_surjective (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    Function.Surjective (equationLinearCutProjection g E weights z n) := by
  intro x
  obtain ⟨p, rfl⟩ := (equationLinearCutRelations g E weights z (n+1)).mkQ_surjective x
  exact ⟨Submodule.Quotient.mk p, rfl⟩

/-- The right-exact one-cut sequence is derived from these actual quotient
maps. There is no injectivity or exactness premise. -/
theorem equationLinearCut_range_eq_kernel (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    LinearMap.range (equationDegreeMultiplication g E weights z n) =
      LinearMap.ker (equationLinearCutProjection g E weights z n) := by
  let D := equationDegreeRelations g E weights n
  let F := equationDegreeRelations g E weights (n+1)
  let mu := homogeneousLinearMul z n
  have hStable : D ≤ F.comap mu := equationDegreeRelations_stable g E weights z n
  have hInclude : F ≤ (F ⊔ LinearMap.range mu).comap (LinearMap.id :
      homogeneousSubmodule σ R (n+1) →ₗ[R] homogeneousSubmodule σ R (n+1)) := by
    change F ≤ F ⊔ LinearMap.range mu
    exact le_sup_left
  change LinearMap.range (D.mapQ F mu hStable) =
    LinearMap.ker (F.mapQ (F ⊔ LinearMap.range mu) LinearMap.id hInclude)
  rw [Submodule.range_mapQ, Submodule.ker_mapQ, Submodule.comap_id,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

/-- The exact degree-zero boundary of the cut is identity. -/
def equationLinearCut_degreeZeroEquiv (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z : homogeneousSubmodule σ R 1) :
    (homogeneousSubmodule σ R 0 ⧸ equationDegreeRelations g E weights 0) ≃ₗ[R]
      (homogeneousSubmodule σ R 0 ⧸ equationLinearCutRelations g E weights z 0) :=
  LinearEquiv.refl R _

/-- A cut family remains stable under every homogeneous linear multiplier.
This is the concrete compatibility needed to iterate the same construction. -/
theorem equationLinearCutRelations_stable (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (z t : homogeneousSubmodule σ R 1) (n : ℕ) :
    equationLinearCutRelations g E weights z n ≤
      (equationLinearCutRelations g E weights z (n+1)).comap (homogeneousLinearMul t n) := by
  cases n with
  | zero =>
      intro p hp
      have hNext := equationDegreeRelations_stable g E weights t 0 hp
      have hInclude : equationDegreeRelations g E weights 1 ≤
          equationDegreeRelations g E weights 1 ⊔ LinearMap.range (homogeneousLinearMul z 0) :=
        le_sup_left
      exact hInclude hNext
  | succ n =>
      apply sup_le
      · intro p hp
        have hNext := equationDegreeRelations_stable g E weights t (n+1) hp
        have hInclude : equationDegreeRelations g E weights ((n+1)+1) ≤
            equationDegreeRelations g E weights ((n+1)+1) ⊔
              LinearMap.range (homogeneousLinearMul z (n+1)) := le_sup_left
        exact hInclude hNext
      · intro p hp
        obtain ⟨a, rfl⟩ := hp
        have hInclude : LinearMap.range (homogeneousLinearMul z (n+1)) ≤
            equationDegreeRelations g E weights ((n+1)+1) ⊔
              LinearMap.range (homogeneousLinearMul z (n+1)) := le_sup_right
        apply hInclude
        refine ⟨homogeneousLinearMul t n a, ?_⟩
        apply Subtype.ext
        change z.val * (t.val * a.val) = t.val * (z.val * a.val)
        exact mul_left_comm _ _ _

end
end PolynomialJets

#check @PolynomialJets.homogeneousLinearMul
#check @PolynomialJets.homogeneousLinearMul_val
#check @PolynomialJets.equationDegreeRelations_stable
#check @PolynomialJets.equationLinearCutRelations
#check @PolynomialJets.equationDegreeMultiplication
#check @PolynomialJets.equationLinearCutProjection
#check @PolynomialJets.equationDegreeMultiplication_apply_mk
#check @PolynomialJets.equationLinearCutProjection_apply_mk
#check @PolynomialJets.equationLinearCutProjection_surjective
#check @PolynomialJets.equationLinearCut_range_eq_kernel
#check @PolynomialJets.equationLinearCut_degreeZeroEquiv
#check @PolynomialJets.equationLinearCutRelations_stable

#print axioms PolynomialJets.homogeneousLinearMul_val
#print axioms PolynomialJets.equationDegreeRelations_stable
#print axioms PolynomialJets.equationDegreeMultiplication_apply_mk
#print axioms PolynomialJets.equationLinearCutProjection_apply_mk
#print axioms PolynomialJets.equationLinearCutProjection_surjective
#print axioms PolynomialJets.equationLinearCut_range_eq_kernel
#print axioms PolynomialJets.equationLinearCut_degreeZeroEquiv
#print axioms PolynomialJets.equationLinearCutRelations_stable
/-
First-party interfaces and proof scripts; no upstream source body is copied
or adapted. The internal helper generalizes the previously passed first-party
one-cut stability argument once, rather than copying a proof at every stage.
The mathematics is the elementary ordered iteration of linear cuts on
homogeneous polynomial relation spaces. Right-exactness is proved from the
actual quotient maps, not supplied as a field of the input data.

Import-only provenance: unchanged first-party PolynomialLinearCut, mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2. Its closure
supplies Submodule.mapQ, ker_mapQ, range_mapQ, quotEquivOfEq and
quotEquivOfEq_mk; the Lean core supplies List.foldl and foldl_append.
File-header authors and Apache-2.0/root license evidence are retained in the
preceding source and architecture attribution ledger. The elementary degree
filtration background is Stacks Project Section 10.69, equation (10.69.0.1),
tag 061M. No new associated-graded theorem or terminal coordinate result is
claimed. Thank you to the Lean and mathlib authors and contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Ordered finite cuts of the actual homogeneous relation spaces

A reusable internal helper records only closure under literal linear
multiplication. The actual initial equation relation family discharges that
property using the preceding passed theorem. List foldl records the cut order,
and a proved append identity identifies every literal next stage.

Every public equation-stage multiplication/projection, representative formula,
surjectivity and range/kernel theorem is uniform in the ordered finite prefix.
No exactness, field, finite-dimensionality, terminal-plane or dimension premise
is added. The numerical DegreewiseLinearCut composition remains separate.
-/

namespace PolynomialJets

open MvPolynomial

noncomputable section

variable {σ ι ε κ R : Type*} [CommRing R]

/-! This implementation namespace contains the structural helper, not a
certificate structure or an assumed exact-sequence interface. -/
namespace HomogeneousRelationFamilies

abbrev Family (σ R : Type*) [CommRing R] :=
  (n : ℕ) → Submodule R (homogeneousSubmodule σ R n)

/-- Structural multiplication closure, distinct from quotient exactness. -/
def LinearStable (D : Family σ R) : Prop :=
  ∀ (z : homogeneousSubmodule σ R 1) (n : ℕ),
    D n ≤ (D (n+1)).comap (homogeneousLinearMul z n)

/-- One literal cut; it introduces no negative-degree multiplication term. -/
def cut (D : Family σ R) (z : homogeneousSubmodule σ R 1) : Family σ R
  | 0 => D 0
  | n+1 => D (n+1) ⊔ LinearMap.range (homogeneousLinearMul z n)

/-- A linear cut inherits multiplication closure. This proof is shared by
all stages of the finite ordered chain. -/
theorem cut_stable (D : Family σ R) (hD : LinearStable D)
    (z : homogeneousSubmodule σ R 1) : LinearStable (cut D z) := by
  intro t n
  cases n with
  | zero =>
      intro p hp
      have hNext := hD t 0 hp
      have hInclude : D 1 ≤ D 1 ⊔ LinearMap.range (homogeneousLinearMul z 0) := le_sup_left
      exact hInclude hNext
  | succ n =>
      apply sup_le
      · intro p hp
        have hNext := hD t (n+1) hp
        have hInclude : D ((n+1)+1) ≤ D ((n+1)+1) ⊔
            LinearMap.range (homogeneousLinearMul z (n+1)) := le_sup_left
        exact hInclude hNext
      · intro p hp
        obtain ⟨a, rfl⟩ := hp
        have hInclude : LinearMap.range (homogeneousLinearMul z (n+1)) ≤
            D ((n+1)+1) ⊔ LinearMap.range (homogeneousLinearMul z (n+1)) := le_sup_right
        apply hInclude
        refine ⟨homogeneousLinearMul t n a, ?_⟩
        apply Subtype.ext
        change z.val * (t.val * a.val) = t.val * (z.val * a.val)
        exact mul_left_comm _ _ _

/-- Apply the finite list of cuts from left to right, retaining literal order. -/
def iterate (D : Family σ R) (cuts : List (homogeneousSubmodule σ R 1)) : Family σ R :=
  cuts.foldl cut D

theorem iterate_nil (D : Family σ R) : iterate D [] = D := rfl

/-- Concatenation means first applying the left list, then the right list. -/
theorem iterate_append (D : Family σ R) (xs ys : List (homogeneousSubmodule σ R 1)) :
    iterate D (xs ++ ys) = iterate (iterate D xs) ys :=
  List.foldl_append

/-- A literal appended cut is the next cut family of the literal prefix. -/
theorem iterate_append_singleton (D : Family σ R)
    (xs : List (homogeneousSubmodule σ R 1)) (z : homogeneousSubmodule σ R 1) :
    iterate D (xs ++ [z]) = cut (iterate D xs) z := by
  rw [iterate_append]
  rfl

/-- Stability is inherited by the ordered list, not assumed at each stage. -/
theorem iterate_stable (cuts : List (homogeneousSubmodule σ R 1)) :
    ∀ D : Family σ R, LinearStable D → LinearStable (iterate D cuts) := by
  induction cuts with
  | nil =>
      intro D hD
      exact hD
  | cons z cuts ih =>
      intro D hD
      exact ih (cut D z) (cut_stable D hD z)

end HomogeneousRelationFamilies

variable [Fintype ι]

/-- Actual ordered cut stages, beginning with the same g/E/weights relation
span that maps onto the actual polynomial degree layer. -/
def equationIteratedCutRelations (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (cuts : List (homogeneousSubmodule σ R 1)) :
    HomogeneousRelationFamilies.Family σ R :=
  HomogeneousRelationFamilies.iterate (equationDegreeRelations g E weights) cuts

theorem equationIteratedCutRelations_nil (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) :
    equationIteratedCutRelations g E weights [] = equationDegreeRelations g E weights := rfl

theorem equationIteratedCutRelations_append_succ (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    equationIteratedCutRelations g E weights (xs ++ [z]) (n+1) =
      equationIteratedCutRelations g E weights xs (n+1) ⊔
        LinearMap.range (homogeneousLinearMul z n) := by
  unfold equationIteratedCutRelations
  rw [HomogeneousRelationFamilies.iterate_append_singleton]
  rfl

theorem equationIteratedCutRelations_append_zero (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) :
    equationIteratedCutRelations g E weights (xs ++ [z]) 0 =
      equationIteratedCutRelations g E weights xs 0 := by
  unfold equationIteratedCutRelations
  rw [HomogeneousRelationFamilies.iterate_append_singleton]
  rfl

/-- The actual initial D is proved stable; induction discharges every stage.
There is no structural stability premise on this public application. -/
theorem equationIteratedCutRelations_stable (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    equationIteratedCutRelations g E weights xs n ≤
      (equationIteratedCutRelations g E weights xs (n+1)).comap (homogeneousLinearMul z n) := by
  have hInitial : HomogeneousRelationFamilies.LinearStable (equationDegreeRelations g E weights) :=
    fun t d => equationDegreeRelations_stable g E weights t d
  exact HomogeneousRelationFamilies.iterate_stable xs _ hInitial z n

/-- Uniform actual multiplication at any literal finite prefix. -/
def equationIteratedCutMultiplication (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    (homogeneousSubmodule σ R n ⧸ equationIteratedCutRelations g E weights xs n) →ₗ[R]
      (homogeneousSubmodule σ R (n+1) ⧸ equationIteratedCutRelations g E weights xs (n+1)) :=
  (equationIteratedCutRelations g E weights xs n).mapQ
    (equationIteratedCutRelations g E weights xs (n+1)) (homogeneousLinearMul z n)
    (equationIteratedCutRelations_stable g E weights xs z n)

/-- Direct quotient projection to the literal append-list stage. -/
def equationIteratedCutProjection (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    (homogeneousSubmodule σ R (n+1) ⧸ equationIteratedCutRelations g E weights xs (n+1)) →ₗ[R]
      (homogeneousSubmodule σ R (n+1) ⧸ equationIteratedCutRelations g E weights (xs ++ [z]) (n+1)) :=
  (equationIteratedCutRelations g E weights xs (n+1)).mapQ
    (equationIteratedCutRelations g E weights (xs ++ [z]) (n+1)) LinearMap.id (by
      change equationIteratedCutRelations g E weights xs (n+1) ≤
        equationIteratedCutRelations g E weights (xs ++ [z]) (n+1)
      rw [equationIteratedCutRelations_append_succ]
      exact le_sup_left)

theorem equationIteratedCutMultiplication_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) (p : homogeneousSubmodule σ R n) :
    equationIteratedCutMultiplication g E weights xs z n (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (homogeneousLinearMul z n p) := rfl

theorem equationIteratedCutProjection_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) (p : homogeneousSubmodule σ R (n+1)) :
    equationIteratedCutProjection g E weights xs z n (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk p := rfl

theorem equationIteratedCutProjection_surjective (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    Function.Surjective (equationIteratedCutProjection g E weights xs z n) := by
  intro x
  obtain ⟨p, rfl⟩ :=
    (equationIteratedCutRelations g E weights (xs ++ [z]) (n+1)).mkQ_surjective x
  exact ⟨Submodule.Quotient.mk p, rfl⟩

/-- Exactness is derived uniformly at every ordered finite prefix. -/
theorem equationIteratedCut_range_eq_kernel (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (n : ℕ) :
    LinearMap.range (equationIteratedCutMultiplication g E weights xs z n) =
      LinearMap.ker (equationIteratedCutProjection g E weights xs z n) := by
  let D := equationIteratedCutRelations g E weights xs n
  let F := equationIteratedCutRelations g E weights xs (n+1)
  let Next := equationIteratedCutRelations g E weights (xs ++ [z]) (n+1)
  let mu := homogeneousLinearMul z n
  have hNext : Next = F ⊔ LinearMap.range mu :=
    equationIteratedCutRelations_append_succ g E weights xs z n
  have hStable : D ≤ F.comap mu := equationIteratedCutRelations_stable g E weights xs z n
  have hInclude : F ≤ Next.comap (LinearMap.id :
      homogeneousSubmodule σ R (n+1) →ₗ[R] homogeneousSubmodule σ R (n+1)) := by
    change F ≤ Next
    rw [hNext]
    exact le_sup_left
  change LinearMap.range (D.mapQ F mu hStable) =
    LinearMap.ker (F.mapQ Next LinearMap.id hInclude)
  rw [Submodule.range_mapQ, Submodule.ker_mapQ, Submodule.comap_id, hNext,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq]

/-- Appending a cut leaves the literal degree-zero quotient unchanged. -/
def equationIteratedCut_degreeZeroEquiv (g : ι → MvPolynomial σ R) (E : ε → ι)
    (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) :
    (homogeneousSubmodule σ R 0 ⧸ equationIteratedCutRelations g E weights xs 0) ≃ₗ[R]
      (homogeneousSubmodule σ R 0 ⧸ equationIteratedCutRelations g E weights (xs ++ [z]) 0) :=
  Submodule.quotEquivOfEq _ _ (equationIteratedCutRelations_append_zero g E weights xs z).symm

theorem equationIteratedCut_degreeZeroEquiv_apply_mk (g : ι → MvPolynomial σ R)
    (E : ε → ι) (weights : κ → ι → R) (xs : List (homogeneousSubmodule σ R 1))
    (z : homogeneousSubmodule σ R 1) (p : homogeneousSubmodule σ R 0) :
    equationIteratedCut_degreeZeroEquiv g E weights xs z (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk p := rfl

end
end PolynomialJets

#check @PolynomialJets.HomogeneousRelationFamilies.LinearStable
#check @PolynomialJets.HomogeneousRelationFamilies.cut
#check @PolynomialJets.HomogeneousRelationFamilies.cut_stable
#check @PolynomialJets.HomogeneousRelationFamilies.iterate
#check @PolynomialJets.HomogeneousRelationFamilies.iterate_append
#check @PolynomialJets.HomogeneousRelationFamilies.iterate_append_singleton
#check @PolynomialJets.HomogeneousRelationFamilies.iterate_stable
#check @PolynomialJets.equationIteratedCutRelations
#check @PolynomialJets.equationIteratedCutRelations_nil
#check @PolynomialJets.equationIteratedCutRelations_append_succ
#check @PolynomialJets.equationIteratedCutRelations_append_zero
#check @PolynomialJets.equationIteratedCutRelations_stable
#check @PolynomialJets.equationIteratedCutMultiplication
#check @PolynomialJets.equationIteratedCutProjection
#check @PolynomialJets.equationIteratedCutMultiplication_apply_mk
#check @PolynomialJets.equationIteratedCutProjection_apply_mk
#check @PolynomialJets.equationIteratedCutProjection_surjective
#check @PolynomialJets.equationIteratedCut_range_eq_kernel
#check @PolynomialJets.equationIteratedCut_degreeZeroEquiv
#check @PolynomialJets.equationIteratedCut_degreeZeroEquiv_apply_mk

#print axioms PolynomialJets.HomogeneousRelationFamilies.cut_stable
#print axioms PolynomialJets.HomogeneousRelationFamilies.iterate_append
#print axioms PolynomialJets.HomogeneousRelationFamilies.iterate_append_singleton
#print axioms PolynomialJets.HomogeneousRelationFamilies.iterate_stable
#print axioms PolynomialJets.equationIteratedCutRelations_nil
#print axioms PolynomialJets.equationIteratedCutRelations_append_succ
#print axioms PolynomialJets.equationIteratedCutRelations_append_zero
#print axioms PolynomialJets.equationIteratedCutRelations_stable
#print axioms PolynomialJets.equationIteratedCutMultiplication_apply_mk
#print axioms PolynomialJets.equationIteratedCutProjection_apply_mk
#print axioms PolynomialJets.equationIteratedCutProjection_surjective
#print axioms PolynomialJets.equationIteratedCut_range_eq_kernel
#print axioms PolynomialJets.equationIteratedCut_degreeZeroEquiv
#print axioms PolynomialJets.equationIteratedCut_degreeZeroEquiv_apply_mk
/-
The definitions and proof scripts here were written independently. Upstream
implementations are not copied or adapted; the declarations below are imported
and called by name. No upstream source file is modified by this module.

Source repository: https://github.com/leanprover-community/mathlib4
Pinned commit: 065356127b1dc0016f66b7283ce0ce2c4055aa55
Principal imported API:
Mathlib/Data/Nat/Choose/Sum.lean :: Nat.sum_range_add_choose.
File-header authors: Chris Hughes, Patrick Stevens.
Local contribution: an independently written iterated-cut counting proof.

The pinned repository LICENSE and inspected file headers state Apache-2.0;
no file-specific exception or repository NOTICE was found for this reuse.
See THIRD_PARTY_NOTICES.md for attribution and LICENSE for the Apache-2.0 text.
Thank you to the cited authors and the mathlib contributors for these foundations.

“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

/-!
# Finite-jet bounds from successive linear cuts

The inputs are natural-number sequences and the dimension inequality supplied
by a degree-wise right-exact sequence. No injectivity or regularity hypothesis
is needed. Applications must separately identify these sequences with the
dimensions of the actual successive graded quotients.

The final theorem is only a numerical budget. It supplies neither the original
ideal, the tail bound, nor the analytic Hilbert–Samuel comparison.
-/

namespace HilbertFunctions.JetBounds

open Finset

/-- Total dimension through degree `N`, with both endpoints included. -/
def cumulative (f : ℕ → ℕ) (N : ℕ) : ℕ :=
  ∑ n ∈ range (N + 1), f n

/-- The dimension inequality for one linear cut. The degree-zero field records
the convention that the degree `-1` piece is zero. -/
structure CutRecurrence (before after : ℕ → ℕ) : Prop where
  zero : before 0 ≤ after 0
  succ : ∀ n, before (n + 1) ≤ before n + after (n + 1)

/-- Summing a single-cut recurrence bounds one graded piece. -/
theorem le_cumulative_of_cut {before after : ℕ → ℕ}
    (hcut : CutRecurrence before after) (n : ℕ) :
    before n ≤ cumulative after n := by
  induction n with
  | zero => simpa [cumulative] using hcut.zero
  | succ n ih =>
      calc
        before (n + 1) ≤ before n + after (n + 1) := hcut.succ n
        _ ≤ cumulative after n + after (n + 1) := Nat.add_le_add_right ih _
        _ = cumulative after (n + 1) := by
          simp only [cumulative, sum_range_succ]

/-- Each cut contributes one more partial summation. -/
theorem cumulative_le_of_cut {before after : ℕ → ℕ}
    (hcut : CutRecurrence before after) (N : ℕ) :
    cumulative before N ≤ cumulative (cumulative after) N := by
  exact sum_le_sum fun n _ => le_cumulative_of_cut hcut n

/-- Summing a binomial envelope raises its two orders by one. -/
theorem cumulative_binomial_envelope (a C k N : ℕ) :
    cumulative (fun n =>
      a * (n + k + 1).choose (k + 1) + C * (n + k).choose k) N =
      a * (N + k + 2).choose (k + 2) + C * (N + k + 1).choose (k + 1) := by
  simp only [cumulative, sum_add_distrib, ← mul_sum]
  rw [show (∑ n ∈ range (N + 1), (n + k + 1).choose (k + 1)) =
      (N + k + 2).choose (k + 2) by
    simpa [Nat.add_assoc] using Nat.sum_range_add_choose N (k + 1)]
  rw [Nat.sum_range_add_choose]

/-- A linear cumulative bound at the final section gives a binomial bound before
`k` cuts. Intermediate cuts may be zero divisors. -/
theorem cumulative_bound_of_cut_chain (k a C : ℕ) (h : ℕ → ℕ → ℕ)
    (hcuts : ∀ i, i < k → CutRecurrence (h i) (h (i + 1)))
    (hlast : ∀ N, cumulative (h k) N ≤ a * (N + 1) + C) (N : ℕ) :
    cumulative (h 0) N ≤
      a * (N + k + 1).choose (k + 1) + C * (N + k).choose k := by
  induction k generalizing h N with
  | zero => simpa using hlast N
  | succ k ih =>
      have hshift : ∀ i, i < k →
          CutRecurrence ((fun j => h (j + 1)) i) ((fun j => h (j + 1)) (i + 1)) := by
        intro i hi
        exact hcuts (i + 1) (by omega)
      have hbound : ∀ n, cumulative (h 1) n ≤
          a * (n + k + 1).choose (k + 1) + C * (n + k).choose k := by
        intro n
        exact ih (fun j => h (j + 1)) hshift hlast n
      calc
        cumulative (h 0) N ≤ cumulative (cumulative (h 1)) N :=
          cumulative_le_of_cut (hcuts 0 (by omega)) N
        _ ≤ cumulative (fun n =>
            a * (n + k + 1).choose (k + 1) + C * (n + k).choose k) N :=
          sum_le_sum fun n _ => hbound n
        _ = a * (N + (k + 1) + 1).choose (k + 1 + 1) +
            C * (N + (k + 1)).choose (k + 1) := by
          simpa [Nat.add_assoc] using cumulative_binomial_envelope a C k N

/-- A uniform tail bound plus a finite initial budget bounds all partial sums. -/
theorem cumulative_bound_of_tail (f : ℕ → ℕ) (d a C : ℕ)
    (hinitial : (∑ n ∈ range d, f n) ≤ C)
    (htail : ∀ n, d ≤ n → f n ≤ a) (N : ℕ) :
    cumulative f N ≤ a * (N + 1) + C := by
  have hterm : ∀ n, f n ≤ a + if n < d then f n else 0 := by
    intro n
    by_cases hn : n < d
    · simp [hn]
    · simpa [hn] using htail n (by omega)
  have hsubset : (range (N + 1)).filter (fun n => n < d) ⊆ range d := by
    intro n hn
    exact mem_range.mpr (mem_filter.mp hn).2
  calc
    cumulative f N ≤ ∑ n ∈ range (N + 1), (a + if n < d then f n else 0) :=
      sum_le_sum fun n _ => hterm n
    _ = a * (N + 1) + ∑ n ∈ (range (N + 1)).filter (fun n => n < d), f n := by
      simp [sum_add_distrib, sum_filter, Nat.mul_comm]
    _ ≤ a * (N + 1) + ∑ n ∈ range d, f n :=
      Nat.add_le_add_left (sum_le_sum_of_subset hsubset) _
    _ ≤ a * (N + 1) + C := Nat.add_le_add_left hinitial _

/-- The first four graded dimensions in a polynomial ring on 19 generators sum
to 1540. The quotient need only satisfy the corresponding upper bounds. -/
theorem initial_budget_nineteen_variables (f : ℕ → ℕ)
    (hsmall : ∀ n, n < 4 → f n ≤ (18 + n).choose 18) :
    (∑ n ∈ range 4, f n) ≤ 1540 := by
  calc
    (∑ n ∈ range 4, f n) ≤ ∑ n ∈ range 4, (18 + n).choose 18 :=
      sum_le_sum fun n hn => hsmall n (mem_range.mp hn)
    _ = 1540 := by norm_num [sum_range_succ, Nat.choose]

/-- The explicit finite-jet budget after restoring the 61 actual linear cuts of
the 19-dimensional section. The tail hypothesis is a separate obligation. -/
theorem sixty_one_cut_jet_budget (h : ℕ → ℕ → ℕ)
    (hcuts : ∀ i, i < 61 → CutRecurrence (h i) (h (i + 1)))
    (hsmall : ∀ n, n < 4 → h 61 n ≤ (18 + n).choose 18)
    (htail : ∀ n, 4 ≤ n → h 61 n ≤ 4) (N : ℕ) :
    cumulative (h 0) N ≤
      4 * (N + 62).choose 62 + 1540 * (N + 61).choose 61 := by
  apply cumulative_bound_of_cut_chain 61 4 1540 h hcuts
  intro n
  exact cumulative_bound_of_tail (h 61) 4 4 1540
    (initial_budget_nineteen_variables (h 61) hsmall) htail n

end HilbertFunctions.JetBounds

/-
The definitions and proof scripts here were written independently. Upstream
implementations are not copied or adapted; the declarations below are imported
and called by name. No upstream source file is modified by this module.

Source repository: https://github.com/leanprover-community/mathlib4
Pinned commit: 065356127b1dc0016f66b7283ce0ce2c4055aa55
Principal imported APIs:
Mathlib/LinearAlgebra/Isomorphisms.lean :: LinearMap.quotKerEquivOfSurjective;
Mathlib/LinearAlgebra/Quotient/Defs.lean :: Submodule.quotEquivOfEq.
File-header authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov.
Mathlib/LinearAlgebra/Dimension/RankNullity.lean ::
Submodule.finrank_quotient_add_finrank. File-header author: Andrew Yang.
Mathlib/LinearAlgebra/Dimension/StrongRankCondition.lean ::
LinearMap.finrank_range_le. File-header author: Kim Morrison.
Local contribution: independently written cokernel and cut-sequence adapters.

The pinned repository LICENSE and inspected file headers state Apache-2.0;
no file-specific exception or repository NOTICE was found for this reuse.
See THIRD_PARTY_NOTICES.md for attribution and LICENSE for the Apache-2.0 text.
Thank you to the cited authors and the mathlib contributors for these foundations.

“If I have seen further it is by standing on the sholders of Giants.” — Isaac Newton, letter to Robert Hooke, 1676.
Source: https://www.newtonproject.ox.ac.uk/view/texts/normalized/OTHE00018
-/

/-!
# Hilbert-function bounds from degree-wise quotient maps

The numerical cut recurrence follows from explicit right-exact linear maps
between finite-dimensional pieces. Multiplication may have a kernel.
An application must identify the pieces and maps with its actual graded ring
and linear cuts; this file does not construct that geometric data.
-/

namespace HilbertFunctions.JetBounds

universe u v w x

section OneDegree

variable {K : Type u} [DivisionRing K]
variable {U : Type v} {V : Type w} {W : Type x}
variable [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module K U] [Module K V] [Module K W]

/-- The cokernel equivalence supplied by a right-exact pair of linear maps. -/
noncomputable def cokernelEquivOfRightExact
    (m : U →ₗ[K] V) (q : V →ₗ[K] W)
    (hexact : LinearMap.range m = LinearMap.ker q)
    (hsurjective : Function.Surjective q) :
    (V ⧸ LinearMap.range m) ≃ₗ[K] W :=
  (Submodule.quotEquivOfEq _ _ hexact).trans (q.quotKerEquivOfSurjective hsurjective)

/-- The equivalence identifies the actual quotient projection, not just dimensions. -/
theorem cokernelEquivOfRightExact_mk
    (m : U →ₗ[K] V) (q : V →ₗ[K] W)
    (hexact : LinearMap.range m = LinearMap.ker q)
    (hsurjective : Function.Surjective q) (v : V) :
    cokernelEquivOfRightExact m q hexact hsurjective (Submodule.Quotient.mk v) = q v := by
  simp [cokernelEquivOfRightExact]

/-- A finite-dimensional cokernel presentation gives the single-degree inequality.
No injectivity of the first map is required. -/
theorem finrank_le_add_finrank_of_cokernel_equiv
    [FiniteDimensional K U] [FiniteDimensional K V]
    (m : U →ₗ[K] V) (e : (V ⧸ LinearMap.range m) ≃ₗ[K] W) :
    Module.finrank K V ≤ Module.finrank K U + Module.finrank K W := by
  have hquotient := (LinearMap.range m).finrank_quotient_add_finrank
  have hequiv := e.finrank_eq
  have hrange := m.finrank_range_le
  omega

/-- The dimension estimate for a right-exact pair, with both maps explicit. -/
theorem finrank_le_add_finrank_of_right_exact
    [FiniteDimensional K U] [FiniteDimensional K V]
    (m : U →ₗ[K] V) (q : V →ₗ[K] W)
    (hexact : LinearMap.range m = LinearMap.ker q)
    (hsurjective : Function.Surjective q) :
    Module.finrank K V ≤ Module.finrank K U + Module.finrank K W :=
  finrank_le_add_finrank_of_cokernel_equiv m
    (cokernelEquivOfRightExact m q hexact hsurjective)

end OneDegree

/-- Degree-wise linear data of one cut. In a graded-ring application,
`multiplication n` is multiplication by a degree-one element and `projection n`
is the quotient map in degree `n + 1`. The degree-zero equivalence records the
absence of a negative-degree contribution. -/
structure DegreewiseLinearCut (K : Type u) [DivisionRing K]
    (A : ℕ → Type v) (B : ℕ → Type w)
    [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
    [∀ n, Module K (A n)] [∀ n, Module K (B n)] where
  degreeZeroEquiv : A 0 ≃ₗ[K] B 0
  multiplication : ∀ n, A n →ₗ[K] A (n + 1)
  projection : ∀ n, A (n + 1) →ₗ[K] B (n + 1)
  range_eq_kernel : ∀ n, LinearMap.range (multiplication n) = LinearMap.ker (projection n)
  surjective : ∀ n, Function.Surjective (projection n)

section GradedPieces

variable {K : Type u} [DivisionRing K]
variable {A : ℕ → Type v} {B : ℕ → Type w}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
variable [∀ n, Module K (A n)] [∀ n, Module K (B n)]

/-- An actual linear quotient equivalence in each positive degree. -/
noncomputable def DegreewiseLinearCut.cokernelEquiv (cut : DegreewiseLinearCut K A B) (n : ℕ) :
    (A (n + 1) ⧸ LinearMap.range (cut.multiplication n)) ≃ₗ[K] B (n + 1) :=
  cokernelEquivOfRightExact (cut.multiplication n) (cut.projection n)
    (cut.range_eq_kernel n) (cut.surjective n)

/-- The numerical recurrence is derived from exactness of actual finite-dimensional
pieces, including the degree-zero boundary. -/
theorem DegreewiseLinearCut.finrank_cut_recurrence
    [∀ n, FiniteDimensional K (A n)] [∀ n, FiniteDimensional K (B n)]
    (cut : DegreewiseLinearCut K A B) :
    CutRecurrence (fun n => Module.finrank K (A n)) (fun n => Module.finrank K (B n)) where
  zero := cut.degreeZeroEquiv.finrank_eq.le
  succ n := finrank_le_add_finrank_of_cokernel_equiv
    (cut.multiplication n) (cut.cokernelEquiv n)

end GradedPieces

/-- The explicit 61-cut bound for finite-dimensional graded pieces connected by
right-exact quotient presentations. The final tail bound remains separate. -/
theorem sixty_one_cut_jet_budget_of_quotient_presentations
    {K : Type u} [DivisionRing K] (A : ℕ → ℕ → Type v)
    [∀ i n, AddCommGroup (A i n)] [∀ i n, Module K (A i n)]
    [∀ i n, FiniteDimensional K (A i n)]
    (cuts : ∀ i, i < 61 → DegreewiseLinearCut K (A i) (A (i + 1)))
    (hsmall : ∀ n, n < 4 → Module.finrank K (A 61 n) ≤ (18 + n).choose 18)
    (htail : ∀ n, 4 ≤ n → Module.finrank K (A 61 n) ≤ 4) (N : ℕ) :
    cumulative (fun n => Module.finrank K (A 0 n)) N ≤
      4 * (N + 62).choose 62 + 1540 * (N + 61).choose 61 := by
  apply sixty_one_cut_jet_budget (fun i n => Module.finrank K (A i n))
  · intro i hi
    exact (cuts i hi).finrank_cut_recurrence
  · exact hsmall
  · exact htail

end HilbertFunctions.JetBounds

#print axioms HilbertFunctions.JetBounds.cokernelEquivOfRightExact
#print axioms HilbertFunctions.JetBounds.cokernelEquivOfRightExact_mk
#print axioms HilbertFunctions.JetBounds.finrank_le_add_finrank_of_cokernel_equiv
#print axioms HilbertFunctions.JetBounds.finrank_le_add_finrank_of_right_exact
#print axioms HilbertFunctions.JetBounds.DegreewiseLinearCut.cokernelEquiv
#print axioms HilbertFunctions.JetBounds.DegreewiseLinearCut.finrank_cut_recurrence
#print axioms HilbertFunctions.JetBounds.sixty_one_cut_jet_budget_of_quotient_presentations
/-
First-party composition and proof scripts; no upstream source body is copied
or adapted. The unchanged admitted JetBudget and GradedQuotientBounds bodies
are used by import and preserved exactly in the single-file audit. Their
recorded passing audit hashes are 618e6e50... and 91a6b883..., reconciled with
current source bodies rather than stale historical attribution-JSON hashes.

Mathematical provenance: the numerical supplement is the classical shifted
hockey-stick/binomial summation, using mathlib's
Nat.sum_range_add_choose. The dimension recurrence is the ordinary cokernel
dimension inequality, already proved in the admitted GradedQuotientBounds.
The polynomial degree-filtration context is Stacks Section 10.69, tag 061M.
No terminal section theorem or finite-jet filtration additivity is claimed.

Import-only upstream provenance at mathlib
065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2:
MvPolynomial.Homogeneous :: homogeneousSubmodule_fg (Johan Commelin, Eric Wieser);
RingTheory.Finiteness.Basic :: Module.Finite.of_fg (Johan Commelin);
FiniteDimensional.Defs :: finiteDimensional_quotient (Chris Hughes);
Data.Nat.Choose.Sum :: sum_range_add_choose (Chris Hughes, Patrick Stevens).
Headers/root LICENSE are Apache-2.0; complete evidence and prior import
provenance are retained by the architecture ledger and admitted predecessors.
Thank you to these authors and all Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Dimensions of the actual finite homogeneous relation quotients

The actual prefix maps fill the existing DegreewiseLinearCut fields without
exactness premises. Finite variables make the actual homogeneous domains and
their quotients finite-dimensional. The sharp cumulative bound remains
conditional on explicit terminal dimensions (at most 1,u,0,0,...).

The conclusion is the cumulative dimension of the covering homogeneous
relation spaces. It is not yet a dimension theorem for the actual polynomial
jet: the finite-jet filtration/additivity and terminal-plane/data applications
remain separate obligations. The exact shifted two-binomial formula is kept;
a coarser constant-multiple envelope is not substituted for it.
-/

namespace HilbertFunctions.JetBounds

open Finset

/-- A shifted binomial sequence with its degree-zero value genuinely zero.
This avoids the false c=0,N=0 contribution from truncated subtraction. -/
def shiftedChoose (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | n+1 => (n+c).choose c

/-- The exact cumulative envelope for c cuts and terminal dimensions (1,u,0,...). -/
def sharpCutEnvelope (u c N : ℕ) : ℕ :=
  (N+c).choose c + u * shiftedChoose c N

/-- The shifted two-binomial expression, with its zero-degree convention. -/
theorem sharpCutEnvelope_eq (u c N : ℕ) :
    sharpCutEnvelope u c N =
      (N+c).choose c + (if N=0 then 0 else u * (N+c-1).choose c) := by
  cases N with
  | zero => simp [sharpCutEnvelope, shiftedChoose]
  | succ N =>
      have hIndex : (N+1)+c-1=N+c := by omega
      simp [sharpCutEnvelope, shiftedChoose, hIndex]

/-- Removing the zero term makes shifted hockey-stick summation exact at all edges. -/
theorem cumulative_shiftedChoose (c N : ℕ) :
    cumulative (shiftedChoose c) N = shiftedChoose (c+1) N := by
  cases N with
  | zero => simp [cumulative, shiftedChoose]
  | succ N =>
      change (∑ n ∈ range ((N+1)+1), shiftedChoose c n) = (N+(c+1)).choose (c+1)
      rw [sum_range_succ']
      simpa only [shiftedChoose, add_zero, Nat.add_assoc] using Nat.sum_range_add_choose N c

/-- One additional partial summation restores one additional cut, sharply. -/
theorem cumulative_sharpCutEnvelope (u c N : ℕ) :
    cumulative (sharpCutEnvelope u c) N = sharpCutEnvelope u (c+1) N := by
  calc
    _ = (∑ n ∈ range (N+1), (n+c).choose c) +
        u * cumulative (shiftedChoose c) N := by
      simp only [cumulative, sharpCutEnvelope, sum_add_distrib, ← mul_sum]
    _ = (N+c+1).choose (c+1) + u * shiftedChoose (c+1) N := by
      rw [Nat.sum_range_add_choose, cumulative_shiftedChoose]
    _ = sharpCutEnvelope u (c+1) N := by
      simp only [sharpCutEnvelope, Nat.add_assoc]

/-- Explicit terminal Hilbert data give the exact zero-cut cumulative envelope. -/
theorem cumulative_bound_of_squareZero_terminal (f : ℕ → ℕ) (u : ℕ)
    (hZero : f 0 ≤ 1) (hOne : f 1 ≤ u) (hTail : ∀ n, 2 ≤ n → f n = 0) (N : ℕ) :
    cumulative f N ≤ sharpCutEnvelope u 0 N := by
  have hPositive : ∀ m, cumulative f (m+1) ≤ 1+u := by
    intro m
    induction m with
    | zero =>
        simpa [cumulative, sum_range_succ] using Nat.add_le_add hZero hOne
    | succ m ih =>
        have hLast : f ((m+1)+1) = 0 := hTail _ (by omega)
        calc
          cumulative f ((m+1)+1) = cumulative f (m+1) + f ((m+1)+1) := by
            simp only [cumulative, sum_range_succ]
          _ ≤ 1+u := by rw [hLast, add_zero]; exact ih
  cases N with
  | zero => simpa [cumulative, sharpCutEnvelope, shiftedChoose] using hZero
  | succ N => simpa [sharpCutEnvelope, shiftedChoose] using hPositive N

/-- Sharp numerical iteration of actual cut recurrences. Only the final
three displayed terminal dimension conditions are hypotheses. -/
theorem cumulative_sharp_bound_of_cut_chain (c u : ℕ) (h : ℕ → ℕ → ℕ)
    (hCuts : ∀ i, i < c → CutRecurrence (h i) (h (i+1)))
    (hZero : h c 0 ≤ 1) (hOne : h c 1 ≤ u)
    (hTail : ∀ n, 2 ≤ n → h c n = 0) (N : ℕ) :
    cumulative (h 0) N ≤ sharpCutEnvelope u c N := by
  induction c generalizing h N with
  | zero => exact cumulative_bound_of_squareZero_terminal (h 0) u hZero hOne hTail N
  | succ c ih =>
      have hShift : ∀ i, i < c → CutRecurrence ((fun j => h (j+1)) i)
          ((fun j => h (j+1)) (i+1)) := by
        intro i hi
        exact hCuts (i+1) (by omega)
      have hBound : ∀ n, cumulative (h 1) n ≤ sharpCutEnvelope u c n := by
        intro n
        exact ih (fun j => h (j+1)) hShift hZero hOne hTail n
      calc
        cumulative (h 0) N ≤ cumulative (cumulative (h 1)) N :=
          cumulative_le_of_cut (hCuts 0 (by omega)) N
        _ ≤ cumulative (sharpCutEnvelope u c) N := sum_le_sum fun n _ => hBound n
        _ = sharpCutEnvelope u (c+1) N := cumulative_sharpCutEnvelope u c N

end HilbertFunctions.JetBounds

namespace PolynomialJets

open MvPolynomial
open HilbertFunctions.JetBounds

noncomputable section

variable {σ ι ε κ K : Type*} [Field K] [Fintype ι]

/-- The literal homogeneous quotient at the actual ordered cut prefix. -/
abbrev equationCutPiece (g : ι → MvPolynomial σ K) (E : ε → ι)
    (weights : κ → ι → K) (xs : List (homogeneousSubmodule σ K 1)) (n : ℕ) :=
  homogeneousSubmodule σ K n ⧸ equationIteratedCutRelations g E weights xs n

/-- The existing right-exact cut structure is filled by actual proved maps. -/
def equationPrefixDegreewiseLinearCut (g : ι → MvPolynomial σ K) (E : ε → ι)
    (weights : κ → ι → K) (xs : List (homogeneousSubmodule σ K 1))
    (z : homogeneousSubmodule σ K 1) :
    DegreewiseLinearCut K (equationCutPiece g E weights xs)
      (equationCutPiece g E weights (xs ++ [z])) where
  degreeZeroEquiv := equationIteratedCut_degreeZeroEquiv g E weights xs z
  multiplication := equationIteratedCutMultiplication g E weights xs z
  projection := equationIteratedCutProjection g E weights xs z
  range_eq_kernel := equationIteratedCut_range_eq_kernel g E weights xs z
  surjective := equationIteratedCutProjection_surjective g E weights xs z

variable [Finite σ]

/-- Finite variables make H_n finite; the ambient polynomial ring need not be. -/
instance finiteDimensional_homogeneousPolynomial (n : ℕ) :
    FiniteDimensional K (homogeneousSubmodule σ K n) :=
  Module.Finite.of_fg (homogeneousSubmodule_fg σ K n)

/-- Every actual prefix quotient is finite by its actual homogeneous domain. -/
theorem equationCutPiece_finiteDimensional (g : ι → MvPolynomial σ K) (E : ε → ι)
    (weights : κ → ι → K) (xs : List (homogeneousSubmodule σ K 1)) (n : ℕ) :
    FiniteDimensional K (equationCutPiece g E weights xs n) := by
  infer_instance

/-- The actual finite quotient maps imply their finrank cut recurrence. -/
theorem equationPrefix_finrank_cut_recurrence (g : ι → MvPolynomial σ K) (E : ε → ι)
    (weights : κ → ι → K) (xs : List (homogeneousSubmodule σ K 1))
    (z : homogeneousSubmodule σ K 1) :
    CutRecurrence (fun n => Module.finrank K (equationCutPiece g E weights xs n))
      (fun n => Module.finrank K (equationCutPiece g E weights (xs ++ [z]) n)) :=
  (equationPrefixDegreewiseLinearCut g E weights xs z).finrank_cut_recurrence

/-- Exact sharp cumulative bound for the actual uncut homogeneous relation
quotients, conditional on explicit terminal dimensions. This is not yet the
actual polynomial-jet dimension or a proved terminal section statement. -/
theorem equation_relation_cumulative_sharp_bound_of_terminal
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K)
    (cuts : List (homogeneousSubmodule σ K 1)) (u N : ℕ)
    (hZero : Module.finrank K (equationCutPiece g E weights cuts 0) ≤ 1)
    (hOne : Module.finrank K (equationCutPiece g E weights cuts 1) ≤ u)
    (hTail : ∀ n, 2 ≤ n → Module.finrank K (equationCutPiece g E weights cuts n) = 0) :
    cumulative (fun n => Module.finrank K (equationCutPiece g E weights [] n)) N ≤
      (N+cuts.length).choose cuts.length +
        (if N=0 then 0 else u * (N+cuts.length-1).choose cuts.length) := by
  -- Capture the entire finrank expression as a nondependent function of the
  -- prefix. Transport list equalities through this function, rather than
  -- simplifying inside the quotient type and its dependent module instances.
  let dim : List (homogeneousSubmodule σ K 1) → ℕ → ℕ := fun xs n =>
    Module.finrank K (equationCutPiece g E weights xs n)
  let h : ℕ → ℕ → ℕ := fun i => dim (cuts.take i)
  have hCuts : ∀ i, i < cuts.length → CutRecurrence (h i) (h (i+1)) := by
    intro i hi
    have hStep : CutRecurrence (dim (cuts.take i)) (dim (cuts.take i ++ [cuts[i]])) :=
      equationPrefix_finrank_cut_recurrence g E weights (cuts.take i) cuts[i]
    have hAfter : dim (cuts.take (i+1)) = dim (cuts.take i ++ [cuts[i]]) :=
      congrArg dim (List.take_succ_eq_append_getElem (l := cuts) hi)
    change CutRecurrence (dim (cuts.take i)) (dim (cuts.take (i+1)))
    rw [hAfter]
    exact hStep
  have hFinal : h cuts.length = dim cuts := congrArg dim (List.take_length (l := cuts))
  have hFinalZero : h cuts.length 0 ≤ 1 := by
    rw [hFinal]
    exact hZero
  have hFinalOne : h cuts.length 1 ≤ u := by
    rw [hFinal]
    exact hOne
  have hFinalTail : ∀ n, 2 ≤ n → h cuts.length n = 0 := by
    intro n hn
    rw [hFinal]
    exact hTail n hn
  have hBound := cumulative_sharp_bound_of_cut_chain cuts.length u h hCuts
    hFinalZero hFinalOne hFinalTail N
  have hBefore : h 0 = dim [] := congrArg dim (List.take_zero (l := cuts))
  rw [hBefore, sharpCutEnvelope_eq] at hBound
  exact hBound

end
end PolynomialJets

#check @HilbertFunctions.JetBounds.shiftedChoose
#check @HilbertFunctions.JetBounds.sharpCutEnvelope
#check @HilbertFunctions.JetBounds.sharpCutEnvelope_eq
#check @HilbertFunctions.JetBounds.cumulative_shiftedChoose
#check @HilbertFunctions.JetBounds.cumulative_sharpCutEnvelope
#check @HilbertFunctions.JetBounds.cumulative_bound_of_squareZero_terminal
#check @HilbertFunctions.JetBounds.cumulative_sharp_bound_of_cut_chain
#check @PolynomialJets.equationCutPiece
#check @PolynomialJets.equationPrefixDegreewiseLinearCut
#check @PolynomialJets.finiteDimensional_homogeneousPolynomial
#check @PolynomialJets.equationCutPiece_finiteDimensional
#check @PolynomialJets.equationPrefix_finrank_cut_recurrence
#check @PolynomialJets.equation_relation_cumulative_sharp_bound_of_terminal

#print axioms HilbertFunctions.JetBounds.sharpCutEnvelope_eq
#print axioms HilbertFunctions.JetBounds.cumulative_shiftedChoose
#print axioms HilbertFunctions.JetBounds.cumulative_sharpCutEnvelope
#print axioms HilbertFunctions.JetBounds.cumulative_bound_of_squareZero_terminal
#print axioms HilbertFunctions.JetBounds.cumulative_sharp_bound_of_cut_chain
#print axioms PolynomialJets.equationPrefixDegreewiseLinearCut
#print axioms PolynomialJets.finiteDimensional_homogeneousPolynomial
#print axioms PolynomialJets.equationCutPiece_finiteDimensional
#print axioms PolynomialJets.equationPrefix_finrank_cut_recurrence
#print axioms PolynomialJets.equation_relation_cumulative_sharp_bound_of_terminal
/-
First-party composition and proof scripts; no upstream source body is copied
or adapted. The mathematics is the standard degree-one generation argument:
if every quadratic is already a relation and relations are stable under
linear multiplication, every higher homogeneous polynomial is a relation.
The actual degree-two relation equality remains an explicit input.

Import-only provenance: unchanged passed PolynomialCutDimensionBounds at
mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 / Lean v4.35.0-rc2.
Existing cached APIs are MvPolynomial.homogeneousSubmodule_one_pow
(Johan Commelin, Eric Wieser), Submodule.mul_le (Kenny Lau),
Submodule.mem_map, Submodule.Quotient.subsingleton_iff and
Module.finrank_zero_of_subsingleton. Exact upstream file/license provenance
is retained in the admitted predecessors and architecture attribution ledger;
headers/root LICENSE are Apache-2.0. No new import or source modification.
Thank you to these authors and all Lean/mathlib contributors.
“If I have seen further it is by standing on the sholders of Giants.”
— Isaac Newton, letter to Robert Hooke, 1676.
-/


/-!
# Quadratic fullness forces the actual stable homogeneous tail to vanish

The product of polynomial submodules is a span of products, so the proof
handles finite sums and scalars through Submodule.mul_le. It does not assume
that an individual homogeneous polynomial is one product.

The structural helper works over an arbitrary commutative ring and variable
type. The actual iterated equation relation family discharges stability using
the passed theorem. Its D_2=top equality is required explicitly; no terminal
plane, substitution kernel, numerical table or geometric claim is inferred.
-/

namespace PolynomialJets

open MvPolynomial

noncomputable section

variable {σ ι ε κ R : Type*} [CommRing R]

namespace HomogeneousRelationFamilies

/-- Full relations in one degree imply full relations in the next degree.
Linear stability is the sole reusable structural premise. -/
theorem LinearStable.eq_top_succ (D : Family σ R) (hStable : LinearStable D)
    (n : ℕ) (hTop : D n = ⊤) : D (n+1) = ⊤ := by
  let F : Submodule R (MvPolynomial σ R) :=
    (D (n+1)).map (homogeneousSubmodule σ R (n+1)).subtype
  have hProducts : homogeneousSubmodule σ R 1 * homogeneousSubmodule σ R n ≤ F := by
    apply Submodule.mul_le.mpr
    intro z hz a ha
    let zH : homogeneousSubmodule σ R 1 := ⟨z, hz⟩
    let aH : homogeneousSubmodule σ R n := ⟨a, ha⟩
    have haD : aH ∈ D n := by
      rw [hTop]
      exact Submodule.mem_top
    have hNext : homogeneousLinearMul zH n aH ∈ D (n+1) := hStable zH n haD
    exact Submodule.mem_map.mpr ⟨homogeneousLinearMul zH n aH, hNext, rfl⟩
  have hDegree : homogeneousSubmodule σ R (n+1) =
      homogeneousSubmodule σ R 1 * homogeneousSubmodule σ R n := by
    rw [← homogeneousSubmodule_one_pow (σ := σ) (R := R) (n+1),
      pow_succ', homogeneousSubmodule_one_pow (σ := σ) (R := R) n]
  apply le_antisymm le_top
  intro p _
  have hpProduct : p.val ∈ homogeneousSubmodule σ R 1 * homogeneousSubmodule σ R n := by
    rw [← hDegree]
    exact p.property
  obtain ⟨q, hq, hqp⟩ := Submodule.mem_map.mp (hProducts hpProduct)
  have hEq : q = p := Subtype.ext hqp
  exact hEq ▸ hq

/-- Starting at degree two, fullness propagates without dependent index casts. -/
theorem LinearStable.eq_top_of_degree_two (D : Family σ R) (hStable : LinearStable D)
    (hTwo : D 2 = ⊤) : ∀ n, 2 ≤ n → D n = ⊤ :=
  Nat.le_induction (m := 2) (P := fun n _ => D n = ⊤) hTwo
    (fun n _ hTop => LinearStable.eq_top_succ D hStable n hTop)

end HomogeneousRelationFamilies

variable [Fintype ι]

/-- The actual equation-family stability is supplied internally. The actual
degree-two equality remains the stated and genuinely needed hypothesis. -/
theorem equationIteratedCutRelations_eq_top_of_degree_two
    (g : ι → MvPolynomial σ R) (E : ε → ι) (weights : κ → ι → R)
    (cuts : List (homogeneousSubmodule σ R 1))
    (hTwo : equationIteratedCutRelations g E weights cuts 2 = ⊤) :
    ∀ n, 2 ≤ n → equationIteratedCutRelations g E weights cuts n = ⊤ := by
  have hStable : HomogeneousRelationFamilies.LinearStable
      (equationIteratedCutRelations g E weights cuts) :=
    fun z n => equationIteratedCutRelations_stable g E weights cuts z n
  exact HomogeneousRelationFamilies.LinearStable.eq_top_of_degree_two _ hStable hTwo

section Field

variable {K : Type*} [Field K]

/-- A full actual relation subspace makes the actual quotient a singleton.
No finite-variable or ambient finite-dimensionality hypothesis is needed. -/
theorem equationCutPiece_subsingleton_of_degree_two
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K)
    (cuts : List (homogeneousSubmodule σ K 1))
    (hTwo : equationIteratedCutRelations g E weights cuts 2 = ⊤) (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (equationCutPiece g E weights cuts n) :=
  (Submodule.Quotient.subsingleton_iff
    (p := equationIteratedCutRelations g E weights cuts n)).mpr
      (equationIteratedCutRelations_eq_top_of_degree_two g E weights cuts hTwo n hn)

/-- The tail hypothesis required by the sharp numerical adapter follows from
actual degree-two fullness; that degree-two binder is not proved here. -/
theorem equationCutPiece_finrank_tail_eq_zero_of_degree_two
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K)
    (cuts : List (homogeneousSubmodule σ K 1))
    (hTwo : equationIteratedCutRelations g E weights cuts 2 = ⊤) :
    ∀ n, 2 ≤ n → Module.finrank K (equationCutPiece g E weights cuts n) = 0 := by
  intro n hn
  letI : Subsingleton (equationCutPiece g E weights cuts n) :=
    equationCutPiece_subsingleton_of_degree_two g E weights cuts hTwo n hn
  exact Module.finrank_zero_of_subsingleton

/-- The sharp cumulative bound now needs only the finite degree-two fullness
input, alongside the actual terminal degree-zero and degree-one bounds.
This still does not prove a terminal plane equality or an actual jet bound. -/
theorem equation_relation_cumulative_sharp_bound_of_degree_two [Finite σ]
    (g : ι → MvPolynomial σ K) (E : ε → ι) (weights : κ → ι → K)
    (cuts : List (homogeneousSubmodule σ K 1)) (u N : ℕ)
    (hZero : Module.finrank K (equationCutPiece g E weights cuts 0) ≤ 1)
    (hOne : Module.finrank K (equationCutPiece g E weights cuts 1) ≤ u)
    (hTwo : equationIteratedCutRelations g E weights cuts 2 = ⊤) :
    HilbertFunctions.JetBounds.cumulative
        (fun n => Module.finrank K (equationCutPiece g E weights [] n)) N ≤
      (N+cuts.length).choose cuts.length +
        (if N=0 then 0 else u * (N+cuts.length-1).choose cuts.length) :=
  equation_relation_cumulative_sharp_bound_of_terminal g E weights cuts u N
    hZero hOne (equationCutPiece_finrank_tail_eq_zero_of_degree_two g E weights cuts hTwo)

end Field

end
end PolynomialJets

#check @PolynomialJets.HomogeneousRelationFamilies.LinearStable.eq_top_succ
#check @PolynomialJets.HomogeneousRelationFamilies.LinearStable.eq_top_of_degree_two
#check @PolynomialJets.equationIteratedCutRelations_eq_top_of_degree_two
#check @PolynomialJets.equationCutPiece_subsingleton_of_degree_two
#check @PolynomialJets.equationCutPiece_finrank_tail_eq_zero_of_degree_two
#check @PolynomialJets.equation_relation_cumulative_sharp_bound_of_degree_two

#print axioms PolynomialJets.HomogeneousRelationFamilies.LinearStable.eq_top_succ
#print axioms PolynomialJets.HomogeneousRelationFamilies.LinearStable.eq_top_of_degree_two
#print axioms PolynomialJets.equationIteratedCutRelations_eq_top_of_degree_two
#print axioms PolynomialJets.equationCutPiece_subsingleton_of_degree_two
#print axioms PolynomialJets.equationCutPiece_finrank_tail_eq_zero_of_degree_two
#print axioms PolynomialJets.equation_relation_cumulative_sharp_bound_of_degree_two
