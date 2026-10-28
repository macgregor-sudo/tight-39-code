module

public import A4Orbit
public import A4KClassify

@[expose] public section

/-!
# The quotient `T(ξ)/O(ξ)` as a real `K`-representation

By exactness of invariants (`finrank_fixH_quot`): `dim (T/O)^H = (26 + 2 r_H) − 16` and
`dim (T/O)^K = 8 − 4`, so the classification gives `T/O ≃_K ℝ⁴_triv ⊕ ⨁_H V_H^(3 + r_H)` (MASTER (6.8)),
at every unit phase.
-/

noncomputable section

namespace CKM.NativeIntrinsicTriality

open Glennie CKM.NativeDerivationTriality CKM.NativeFirstOrder

/-- `K` acting on the real vector-space quotient `T(ξ)/O(ξ)`. -/
def tangentQuotAction (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : KAction (tangentSpace ξ ⧸ orbitInT ξ) :=
  (tanAction ξ hξ).quot (orbitInT ξ) (orbitInT_invariant ξ hξ)

/-- `O(ξ)` inside `T(ξ)` has dimension `52`. -/
theorem finrank_orbitInT (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (orbitInT ξ) = 52 := by
  rw [orbitInT, (Submodule.comapSubtypeEquivOfLe (orbitSpace_le_tangentSpace ξ hξ)).finrank_eq,
    finrank_orbitSpace ξ hξ]

theorem finrank_tangentQuot_fixK (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (tangentQuotAction ξ hξ).fixK = 4 := by
  have h := finrank_fixK_quot (tanAction ξ hξ) (orbitInT ξ) (orbitInT_invariant ξ hξ)
  rw [finrank_orbit_fixK, finrank_tanAction_fixK] at h
  unfold tangentQuotAction
  omega

theorem finrank_tangentQuot_fixH (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (H : Fin 4) :
    Module.finrank ℝ ((tangentQuotAction ξ hξ).fixH H) =
      4 + 2 * (3 + UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H)) := by
  have h := finrank_fixH_quot (tanAction ξ hξ) (orbitInT ξ) (orbitInT_invariant ξ hξ) H
  rw [finrank_orbit_fixH, finrank_tanAction_fixH] at h
  unfold tangentQuotAction
  omega

theorem finrank_tangentQuot (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Module.finrank ℝ (tangentSpace ξ ⧸ orbitInT ξ) =
      28 + 2 * ∑ H, UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H) := by
  have h := Submodule.finrank_quotient_add_finrank (orbitInT ξ)
  rw [finrank_orbitInT ξ hξ, finrank_tangentSpace ξ hξ] at h
  omega

/-- **(6.8)** `T(ξ)/O(ξ) ≃_K ℝ⁴_triv ⊕ ⨁_H V_H^(3 + r_H)`. -/
theorem tangentQuot_kEquiv (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Nonempty (KEquiv (tangentQuotAction ξ hξ)
      (stdAction 4 fun H => 3 + UnitaryErrorBases.resonanceCount (anchorTriple ξ hξ H))) :=
  kEquiv_std_of_finrank _ 4 _ (finrank_tangentQuot_fixK ξ hξ) (finrank_tangentQuot_fixH ξ hξ)

end CKM.NativeIntrinsicTriality

#print axioms CKM.NativeIntrinsicTriality.finrank_orbitInT
#print axioms CKM.NativeIntrinsicTriality.finrank_tangentQuot_fixK
#print axioms CKM.NativeIntrinsicTriality.finrank_tangentQuot_fixH
#print axioms CKM.NativeIntrinsicTriality.finrank_tangentQuot
#print axioms CKM.NativeIntrinsicTriality.tangentQuot_kEquiv
