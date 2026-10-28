module

public import ULGroup

@[expose] public section

/-!
# The compensated stabilizer `Γξ` of the literal configuration 

`Γξ = {(g, π) ∈ G × Π | (g, π) • P = P}` with `P = literalCfg ξ`, as the actual stabilizer subgroup.

* Projection `Γξ → Π` is injective, from the accepted trivial labelled stabilizer
  `actC_literalCfg_eq_iff`: if `(g, π)` and `(g', π)` fix `P` then `g'⁻¹ g` fixes `P` labelwise.
  Hence `Γξ` is finite. Its order, triviality, genericity or faithfulness on any later quotient are
  **not** asserted.
* Every `(g, π)` (in all of `G × Π`) preserves the finite-sum native trace pairing `cfgPairing`.
* Every element of `Γξ` preserves the actual orbit tangent `orbitC ξ` (conjugation `g D g⁻¹` keeps
  `derC`), the normal space `normalC ξ = (orbitC ξ)ᗮ`, the affine slice `P + normalC ξ`, and the
  original zero set (the last for all of `G × Π`).
-/

noncomputable section

namespace CKM.NativeUnlabelledSlice

open Glennie NativePolynomial CKM.NativeFirstOrder CKM.NativeGroupSlice
open Option2.NativeStress.AnalyticDerivative (originalF)
open scoped Topology

/-- The compensated stabilizer of the literal configuration. -/
def stab (ξ : Fin 4 → ℂ) : Subgroup Big := MulAction.stabilizer Big (literalCfg ξ)

theorem mem_stab_iff (ξ : Fin 4 → ℂ) (γ : Big) : γ ∈ stab ξ ↔ γ • literalCfg ξ = literalCfg ξ :=
  MulAction.mem_stabilizer_iff

/-- Pointwise reading of membership in `Γξ`. -/
private theorem uls_fix {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (i : Fin 39) :
    autVal γ.1 (literalCfg ξ ((γ.2 : Equiv.Perm (Fin 39)).symm i)) = literalCfg ξ i := by
  have h := congrFun ((mem_stab_iff ξ γ).1 hγ) i
  rwa [big_smul_apply] at h

private theorem uls_inv_apply {A : CEnd} (hA : A ∈ autC) (x : Coord) : Ring.inverse A (A x) = x := by
  have h := congrArg (fun T : CEnd => T x) (mul_inverse_of_mem_autOf hA).2
  simpa using h

private theorem uls_apply_inv {A : CEnd} (hA : A ∈ autC) (x : Coord) : A (Ring.inverse A x) = x := by
  have h := congrArg (fun T : CEnd => T x) (mul_inverse_of_mem_autOf hA).1
  simpa using h

/-- Pull-back form of membership in `Γξ`: `P (e⁻¹ i) = g⁻¹ (P i)`. -/
private theorem uls_fix_symm {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (i : Fin 39) :
    literalCfg ξ ((γ.2 : Equiv.Perm (Fin 39)).symm i) = Ring.inverse (autVal γ.1) (literalCfg ξ i) := by
  rw [← uls_fix hγ i, uls_inv_apply (autVal_mem γ.1)]

/-- **Injective projection to `Π`.** -/
theorem stab_snd_injective (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) :
    Function.Injective fun γ : stab ξ => (γ : Big).2 := by
  intro γ δ hγδ
  have he : ((γ : Big).2 : Equiv.Perm (Fin 39)) = ((δ : Big).2 : Equiv.Perm (Fin 39)) :=
    congrArg Subtype.val hγδ
  set A := autVal (γ : Big).1 with hAdef
  set B := autVal (δ : Big).1 with hBdef
  have hA : A ∈ autC := autVal_mem _
  have hfix : ∀ i, (B * Ring.inverse A) (literalCfg ξ i) = (1 : CEnd) (literalCfg ξ i) := by
    intro i
    show B (Ring.inverse A (literalCfg ξ i)) = literalCfg ξ i
    rw [← uls_fix_symm γ.2 i, he, uls_fix δ.2 i]
  have h1 : B * Ring.inverse A = 1 := orbit_eq_of_literalCfg ξ hξ hfix
  have hBA : B = A := by
    calc B = B * (Ring.inverse A * A) := by rw [(mul_inverse_of_mem_autOf hA).2, mul_one]
      _ = (B * Ring.inverse A) * A := by rw [mul_assoc]
      _ = A := by rw [h1, one_mul]
  have hg : (γ : Big).1 = (δ : Big).1 := Subtype.ext (Units.ext hBA.symm)
  exact Subtype.ext (Prod.ext hg hγδ)

/-- **`Γξ` is finite.** -/
theorem finite_stab (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) : Finite (stab ξ) := by
  exact Finite.of_injective _ (stab_snd_injective ξ hξ)

/-- The label action preserves the trace pairing. -/
theorem cfgPairing_permAct (e : Equiv.Perm (Fin 39)) (C C' : Cfg) :
    cfgPairing (permAct e C) (permAct e C') = cfgPairing C C' := by
  unfold cfgPairing
  simp only [permAct_apply]
  exact Equiv.sum_comp e.symm (fun i => CoordinateMaps.coordinatePairing (C i) (C' i))

/-- **Every element of `G × Π` preserves the finite-sum native trace pairing.** -/
theorem cfgPairing_smul (γ : Big) (C C' : Cfg) : cfgPairing (γ • C) (γ • C') = cfgPairing C C' := by
  rw [big_smul_def, big_smul_def, cfgPairing_actC (autVal_mem γ.1), cfgPairing_permAct]

/-- Conjugation by a native automorphism preserves the derivations. -/
theorem conj_mem_derC {A : CEnd} (hA : A ∈ autC) {D : CEnd} (hD : D ∈ derC) :
    A * D * Ring.inverse A ∈ derC := by
  have hAi := inverse_mem_autOf hA
  refine mem_derOf.2 fun a b => ?_
  show A (D (Ring.inverse A (prodC a b))) =
    prodC (A (D (Ring.inverse A a))) b + prodC a (A (D (Ring.inverse A b)))
  rw [hAi.2, (mem_derOf.1 hD), map_add, hA.2, hA.2, uls_apply_inv hA, uls_apply_inv hA]

/-- `γ • (D • P) = (g D g⁻¹) • P` for `γ = (g, e) ∈ Γξ`. -/
private theorem uls_smul_orbitMapC {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (D : CEnd) :
    γ • orbitMapC ξ D = orbitMapC ξ (autVal γ.1 * D * Ring.inverse (autVal γ.1)) := by
  funext i
  rw [big_smul_apply, orbitMapC_apply, orbitMapC_apply, uls_fix_symm hγ i]
  rfl

private theorem uls_smul_mem_orbitC {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) {u : Cfg}
    (hu : u ∈ orbitC ξ) : γ • u ∈ orbitC ξ := by
  obtain ⟨D, hD, rfl⟩ := hu
  refine ⟨_, conj_mem_derC (autVal_mem γ.1) hD, ?_⟩
  exact (uls_smul_orbitMapC hγ D).symm

/-- **`Γξ` preserves the actual orbit tangent.** -/
theorem smul_mem_orbitC_iff {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (u : Cfg) :
    γ • u ∈ orbitC ξ ↔ u ∈ orbitC ξ := by
  refine ⟨fun h => ?_, uls_smul_mem_orbitC hγ⟩
  have h' := uls_smul_mem_orbitC ((stab ξ).inv_mem hγ) h
  rwa [big_inv_smul_smul] at h'

/-- `bigLin γ` is the action of `γ` (definitional). -/
private theorem uls_bigLin_apply (γ : Big) (C : Cfg) : bigLin γ C = γ • C := rfl

theorem orbitC_map_bigLin {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) :
    (orbitC ξ).map (bigLin γ : Cfg →ₗ[ℝ] Cfg) = orbitC ξ := by
  ext x
  refine ⟨?_, fun hx => ⟨γ⁻¹ • x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    show bigLin γ y ∈ orbitC ξ
    rw [uls_bigLin_apply]
    exact (smul_mem_orbitC_iff hγ y).2 hy
  · exact (smul_mem_orbitC_iff hγ _).1 (by rwa [big_smul_inv_smul])
  · show bigLin γ (γ⁻¹ • x) = x
    rw [uls_bigLin_apply, big_smul_inv_smul]

/-- **`Γξ` preserves the normal space.** -/
theorem smul_mem_normalC_iff {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (n : Cfg) :
    γ • n ∈ normalC ξ ↔ n ∈ normalC ξ := by
  rw [mem_normalC_iff, mem_normalC_iff]
  constructor
  · intro h u hu
    rw [← cfgPairing_smul γ u n]
    exact h _ ((smul_mem_orbitC_iff hγ u).2 hu)
  · intro h u hu
    rw [← big_smul_inv_smul γ u, cfgPairing_smul]
    exact h _ ((smul_mem_orbitC_iff ((stab ξ).inv_mem hγ) u).2 hu)

theorem normalC_map_bigLin {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) :
    (normalC ξ).map (bigLin γ : Cfg →ₗ[ℝ] Cfg) = normalC ξ := by
  ext x
  refine ⟨?_, fun hx => ⟨γ⁻¹ • x, ?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    show bigLin γ y ∈ normalC ξ
    rw [uls_bigLin_apply]
    exact (smul_mem_normalC_iff hγ y).2 hy
  · exact (smul_mem_normalC_iff hγ _).1 (by rwa [big_smul_inv_smul])
  · show bigLin γ (γ⁻¹ • x) = x
    rw [uls_bigLin_apply, big_smul_inv_smul]

/-- **`Γξ` preserves the affine slice `P + normalC ξ`.** -/
theorem smul_mem_sliceSet_iff {ξ : Fin 4 → ℂ} {γ : Big} (hγ : γ ∈ stab ξ) (C : Cfg) :
    γ • C ∈ sliceSet ξ ↔ C ∈ sliceSet ξ := by
  show γ • C - literalCfg ξ ∈ normalC ξ ↔ C - literalCfg ξ ∈ normalC ξ
  have hP : γ • literalCfg ξ = literalCfg ξ := (mem_stab_iff ξ γ).1 hγ
  have h : γ • C - literalCfg ξ = γ • (C - literalCfg ξ) := by
    rw [← uls_bigLin_apply γ (C - literalCfg ξ), map_sub, uls_bigLin_apply, uls_bigLin_apply, hP]
  rw [h]
  exact smul_mem_normalC_iff hγ _

/-- **`Γξ` (indeed all of `G × Π`) preserves the original zero set.** -/
theorem stab_smul_mem_zeroSet_iff {ξ : Fin 4 → ℂ} {γ : Big} (_hγ : γ ∈ stab ξ) (C : Cfg) :
    γ • C ∈ zeroSet ↔ C ∈ zeroSet :=
  big_smul_mem_zeroSet_iff γ C

end CKM.NativeUnlabelledSlice

#print axioms CKM.NativeUnlabelledSlice.stab_snd_injective
#print axioms CKM.NativeUnlabelledSlice.finite_stab
#print axioms CKM.NativeUnlabelledSlice.cfgPairing_permAct
#print axioms CKM.NativeUnlabelledSlice.cfgPairing_smul
#print axioms CKM.NativeUnlabelledSlice.conj_mem_derC
#print axioms CKM.NativeUnlabelledSlice.smul_mem_orbitC_iff
#print axioms CKM.NativeUnlabelledSlice.orbitC_map_bigLin
#print axioms CKM.NativeUnlabelledSlice.smul_mem_normalC_iff
#print axioms CKM.NativeUnlabelledSlice.normalC_map_bigLin
#print axioms CKM.NativeUnlabelledSlice.smul_mem_sliceSet_iff
#print axioms CKM.NativeUnlabelledSlice.stab_smul_mem_zeroSet_iff
