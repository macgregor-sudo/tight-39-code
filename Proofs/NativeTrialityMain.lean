module

public import NativeTrialityTraceFree
public import NativeTrialityCyclic
public import NativeTrialitySection

/-!
# Native triality and the 52-dimensional derivation algebra (MASTER §6.6)

The public endpoint `native_derivation_triality` assembles, for the actual native compact Albert
algebra and octonions:

1. every Jordan derivation is trace-free, skew for the positive trace pairing and kills the unit;
2. Peirce restriction `peirceRestrictionEquiv : diagonalFixer ≃ₗ⁅ℝ⁆ relatedTriples` is a Lie
   equivalence with inverse extension, which acts on upper slots `(o01, o02, o12)` by `(A, C, B)`;
3. the two projections `firstProjEquiv`, `secondProjEquiv : relatedTriples ≃ₗ⁅ℝ⁆ skewEnd` are Lie
   equivalences; the cyclic action is `(B, K C K, A)`, the cyclic seed is `(R_u, -L_u - R_u, L_u)` and the
   first cyclic Peirce slot carries the second projection;
4. the inner section `4 [L_v, L_{e_i}]` splits the derivations linearly as
   `(O × O × O) × diagonalFixer`, so the fixer has dimension 28 and the derivations dimension 52.

No rank, basis, trace-free, surjectivity, product-preservation or decomposition hypothesis appears.
Not claimed: `Aut J = F₄`, a `Spin(8)` group identification, integration of the Lie equivalences,
or a Lie direct-product structure on the `24 + 28` splitting.
-/

@[expose] public section

noncomputable section

namespace CKM.NativeDerivationTriality

open Glennie Reuse

attribute [local instance 100] LieRing.ofAssociativeRing

theorem finrank_diagonalFixer : Module.finrank ℝ diagonalFixer = 28 :=
  (peirceRestrictionEquiv.toLinearEquiv.finrank_eq).trans finrank_relatedTriples

instance : Module.Finite ℝ diagonalFixer :=
  FiniteDimensional.of_finrank_pos (by rw [finrank_diagonalFixer]; norm_num)

theorem finrank_jordanDerivations : Module.finrank ℝ jordanDerivations = 52 := by
  rw [derivationDecomposition.finrank_eq,
    Module.finrank_prod (R := ℝ) (M := Octonion × Octonion × Octonion) (M' := diagonalFixer),
    Module.finrank_prod (R := ℝ) (M := Octonion) (M' := Octonion × Octonion),
    Module.finrank_prod (R := ℝ) (M := Octonion) (M' := Octonion), finrank_octonion, finrank_diagonalFixer]

/-- The native derivation/triality endpoint (MASTER §6.6, lines 694–732). -/
theorem native_derivation_triality :
    -- (1) trace-free, skew, unit-killing
    (∀ D ∈ jordanDerivations, (∀ x, Glennie.trace (D x) = 0) ∧ (∀ x y, Glennie.inner (D x) y + Glennie.inner x (D y) = 0) ∧
        D 1 = 0) ∧
    -- (2) restriction/extension, both inverse laws, upper-slot order (A, C, B)
    (∀ D : diagonalFixer, (peirceRestrictionEquiv D : EndTriple) = restrictTriple D) ∧
    (∀ t : relatedTriples, (peirceRestrictionEquiv.symm t : Module.End ℝ Albert) = extendTriple t) ∧
    (∀ t ∈ relatedTriples, restrictTriple (extendTriple t) = t) ∧
    (∀ D ∈ diagonalFixer, extendTriple (restrictTriple D) = D) ∧
    (∀ (t : EndTriple) (x : Albert), extendTriple t x = ⟨0, 0, 0, t.1 x.o01, t.2.2 x.o02, t.2.1 x.o12⟩) ∧
    -- (3) the two projections, the cyclic convention and seed
    (∀ t : relatedTriples, (firstProjEquiv t : Module.End ℝ Octonion) = (t : EndTriple).1) ∧
    (∀ t : relatedTriples, (secondProjEquiv t : Module.End ℝ Octonion) = (t : EndTriple).2.1) ∧
    (∀ u : Octonion, octRe u = 0 → seedTriple u ∈ relatedTriples ∧
        cyclicAction (seedTriple u) = (rightMul u, -leftMul u - rightMul u, leftMul u)) ∧
    (∀ (t : EndTriple) (x : Albert), cyclicSlots (extendTriple t x) =
        ((cyclicAction t).1 (cyclicSlots x).1, (cyclicAction t).2.1 (cyclicSlots x).2.1,
          (cyclicAction t).2.2 (cyclicSlots x).2.2)) ∧
    (∀ (D : diagonalFixer) (x : Albert), (cyclicSlots ((D : Module.End ℝ Albert) x)).1 =
        (secondProjEquiv (peirceRestrictionEquiv D) : Module.End ℝ Octonion) (cyclicSlots x).1) ∧
    -- (4) the inner section, its Peirce values and the splitting
    (∀ a : Octonion, peirceInner (slot01 a) idem0 idem0 = slot01 a ∧
        peirceInner (slot01 a) idem0 idem1 = -slot01 a ∧ peirceInner (slot01 a) idem0 idem2 = 0) ∧
    (∀ v, innerSection v ∈ jordanDerivations ∧ diagonalVariation (innerSection v) = v) ∧
    (∀ D ∈ jordanDerivations, D ∈ diagonalFixer ↔ diagonalVariation D = 0) ∧
    -- literal dimensions
    Module.finrank ℝ skewEnd = 28 ∧ Module.finrank ℝ relatedTriples = 28 ∧
    Module.finrank ℝ diagonalFixer = 28 ∧ Module.finrank ℝ jordanDerivations = 52 := by
  refine ⟨fun D hD => ⟨derivation_trace_eq_zero hD, derivation_inner_skew hD, derivation_map_one hD⟩,
    peirceRestrictionEquiv_apply, peirceRestrictionEquiv_symm_apply,
    fun t ht => restrictTriple_extendTriple ht, fun D hD => extendTriple_restrictTriple hD,
    extendTriple_apply, firstProj_apply, secondProj_apply,
    fun u hu => ⟨seedTriple_mem hu, cyclicAction_seedTriple hu⟩, cyclicSlots_extendTriple,
    firstCyclicSlot_eq_secondProj,
    fun a => ⟨peirceInner_slot01_idem0 a, peirceInner_slot01_idem1 a, peirceInner_slot01_idem2 a⟩,
    fun v => ⟨innerSection_mem v, diagonalVariation_innerSection v⟩,
    fun D hD => mem_diagonalFixer_iff_diagonalVariation hD,
    finrank_skewEnd, finrank_relatedTriples, finrank_diagonalFixer, finrank_jordanDerivations⟩

end CKM.NativeDerivationTriality
