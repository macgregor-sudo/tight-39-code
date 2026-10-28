module
public import PairingDefinitions
public import GPCode
public import Mathlib.Topology.Homeomorph.Quotient
@[expose] public section

noncomputable section

/- Compact definitions copied verbatim from Challenge; no Challenge theorem
 placeholders are imported. Existing native membership constructs the classes. -/
namespace Option2StatementCode
open Glennie CKM.NativeTightCode

end Option2StatementCode

namespace Option2StatementCode
/- The actual literal four-phase family in the canonical quotient topology. -/
end Option2StatementCode

namespace Option2StatementCode
open Glennie NativePolynomial CKM.NativeTightCode CKM.NativeGroupSlice
open CKM.NativeUnlabelledSlice

private theorem point_action (γ : CodeGroup) (C : Cfg) (i : Fin 39) :
    codePoint (codeAct γ C) (γ.2 i) =
      coordEnd.symm (autVal γ.1) (codePoint C i) := by
  simp only [codeAct, codePoint_eq, coordEnd_symm_apply,
    upperCoordinates_fromUpperCoordinates, actC_apply, permAct_apply,
    Equiv.symm_apply_apply]

theorem codeSetoid_relation_iff (C D : tightLocus) :
    codeSetoid.r C D ↔ CKM.NativeUnlabelledSlice.codeSetoid.r C D := by
  constructor
  · rintro ⟨g, hg, e, he⟩
    let A : autC := autCEquiv.symm ⟨g, hg⟩
    let a : autGroup := autGroupEquiv.symm A
    have ha : coordEnd.symm (autVal a) = g.toLinearMap := by
      change coordEnd.symm (coordEnd g.toLinearMap) = g.toLinearMap
      exact coordEnd.symm_apply_apply _
    refine ⟨(a, e), ?_⟩
    funext i
    apply upperCoordinateEquiv.symm.injective
    change codePoint (codeAct (a, e) C.1) i = codePoint D.1 i
    obtain ⟨j, rfl⟩ := e.surjective i
    rw [point_action, ha]
    exact he j
  · rintro ⟨γ, hγ⟩
    refine ⟨(autCEquiv (autGroupEquiv γ.1)).1,
      (autCEquiv (autGroupEquiv γ.1)).2, γ.2, ?_⟩
    intro i
    change coordEnd.symm (autVal γ.1) (codePoint C.1 i) = codePoint D.1 (γ.2 i)
    rw [← point_action, hγ]

theorem codeSetoid_eq_native : codeSetoid = CKM.NativeUnlabelledSlice.codeSetoid := by
  ext C D
  exact codeSetoid_relation_iff C D

def quotientHomeomorph : CodeModuli ≃ₜ CKM.NativeUnlabelledSlice.CodeModuli :=
  Homeomorph.Quotient.congrRight codeSetoid_relation_iff

@[simp] theorem quotientHomeomorph_codeClass (C : CodeCoords) (hC : C ∈ tightLocus) :
    quotientHomeomorph (codeClass C hC) =
      Quotient.mk CKM.NativeUnlabelledSlice.codeSetoid ⟨C, hC⟩ := rfl

@[simp] theorem quotientHomeomorph_phaseClass (u : CKM.NativeGoodPhase.PhaseTorus) :
    quotientHomeomorph (phaseClass u) = CKM.NativeGoodPhase.codeClass u := rfl

@[simp] theorem quotientHomeomorph_originalCode :
    quotientHomeomorph originalCode = CKM.NativeGoodPhase.codeClass
      CKM.NativeGoodPhase.onePhase := rfl

open CKM.NativeGoodPhase
open scoped Topology

theorem exists_goodAvoid_codeClass_mem_nhds_one {p : MvPolynomial (Fin 4) ℂ}
    (hp : p ≠ 0) {V : Set CodeModuli} (hV : V ∈ 𝓝 originalCode) :
    ∃ u : PhaseTorus, u ≠ onePhase ∧ u ∈ GoodAvoid p ∧ phaseClass u ∈ V := by
  have hN : quotientHomeomorph '' V ∈ 𝓝 (CKM.NativeGoodPhase.codeClass onePhase) := by
    rw [← quotientHomeomorph_originalCode]
    exact quotientHomeomorph.isOpenMap.image_mem_nhds hV
  obtain ⟨u, hne, hu, hv⟩ := CKM.NativeGoodPhase.exists_goodAvoid_codeClass_mem_nhds_one hp hN
  refine ⟨u, hne, hu, ?_⟩
  obtain ⟨v, hv, he⟩ := hv
  have : v = phaseClass u := quotientHomeomorph.injective
    (he.trans (quotientHomeomorph_phaseClass u).symm)
  simpa only [this] using hv

#print axioms Option2StatementCode.codeSetoid_relation_iff
#print axioms Option2StatementCode.quotientHomeomorph
#print axioms Option2StatementCode.exists_goodAvoid_codeClass_mem_nhds_one
end Option2StatementCode
