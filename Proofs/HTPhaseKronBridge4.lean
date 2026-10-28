module

public import HTPhaseKronBridge3

@[expose] public section

/-! # L1 bridge theorem: `PhiR Q12.toComplex (ξ/ξ_base) = literalCfg ξ` for every unit phase ξ.
First-party. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Option2.NativeStress.HTPhaseKron
open CompactAlbert CKM.NativeFirstOrder NativePolynomial NativeH.Equilibrium
open QuadraticCertificate.ExactCKMConfiguration UnitaryErrorBases.ThreeCycleFourier UnitaryErrorBases.ComplexQuartet

theorem g2_fixed (α β α' β' : ℂ) (hα : Complex.normSq α = Complex.normSq α')
    (hβ : Complex.normSq β = Complex.normSq β') (c : ℕ) (hc : c < 27)
    (h : c < 3 ∨ planeExp ((c - 3) / 2) = none) : g2 α β ⟨c, hc⟩ = g2 α' β' ⟨c, hc⟩ := by
  interval_cases c <;> simp [g2, planeExp, hα, hβ] at h ⊢

theorem g3_fixed (α β α' β' : ℂ) (hα : Complex.normSq α = Complex.normSq α')
    (hβ : Complex.normSq β = Complex.normSq β') (c : ℕ) (hc : c < 27)
    (h : c < 3 ∨ planeExp ((c - 3) / 2) = none) : g3 α β ⟨c, hc⟩ = g3 α' β' ⟨c, hc⟩ := by
  interval_cases c <;> simp [g3, planeExp, hα, hβ] at h ⊢

theorem nsq_unit (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (a : Fin 4) (z : ℂ) :
    Complex.normSq (ξ a * z) = Complex.normSq (exactPhases a * z) := by
  rw [Complex.normSq_mul, Complex.normSq_mul, hξ a, exactPhases_unit' a]

/-- Coordinates off the moving planes do not depend on the phase. -/
theorem fixed_pc (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p c : ℕ) (hp : p < 39) (hc : c < 27)
    (h : c < 3 ∨ planeExp ((c - 3) / 2) = none) :
    Cn ξ (27 * p + c) = Cn exactPhases (27 * p + c) := by
  rcases lt_or_ge p 21 with h1 | h1
  · exact low_eq ξ p c h1 hc
  rw [Cn_pc' ξ p c hp hc _ rfl, Cn_pc' exactPhases p c hp hc _ rfl]
  rcases lt_or_ge p 30 with h2 | h2
  · rw [point_g2 ξ p h1 h2, point_g2 exactPhases p h1 h2,
      g2_fixed _ _ _ _ (nsq_unit ξ hξ 0 _) (nsq_unit ξ hξ 1 _) c hc h]
  · rw [point_g3 ξ p h2 (by omega), point_g3 exactPhases p h2 (by omega),
      g3_fixed _ _ _ _ (nsq_unit ξ hξ 2 _) (nsq_unit ξ hξ 3 _) c hc h]

theorem charLaw (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (p : ℕ) (hp : p < 39) (j : ℕ) (m : Ex)
    (hj : j < 12) (hm : planeExp j = some m) :
    Cn ξ (27 * p + 3 + 2 * j) - Complex.I * Cn ξ (27 * p + 3 + 2 * j + 1) =
      (Cn exactPhases (27 * p + 3 + 2 * j) - Complex.I * Cn exactPhases (27 * p + 3 + 2 * j + 1)) *
        mono (Uph ξ hξ) m := by
  interval_cases j <;> simp [planeExp] at hm <;> subst hm <;>
    first | exact cl_2 ξ hξ p hp | exact cl_3 ξ hξ p hp | exact cl_5 ξ hξ p hp |
      exact cl_7 ξ hξ p hp | exact cl_9 ξ hξ p hp | exact cl_10 ξ hξ p hp

section Unfold
variable {R : Type*} [CommRing R] (ι : Q12 →+* R) (U : Fin 4 → Rˣ)

theorem PhiR_fixed (v : Fin 1053) (h : v.val % 27 < 3 ∨ planeExp ((v.val % 27 - 3) / 2) = none) :
    PhiR ι U v = ι (bq v.val) := by
  unfold PhiR phiTerms
  by_cases h3 : v.val % 27 < 3
  · simp [h3, ev, mono]
  · have h' : planeExp ((v.val % 27 - 3) / 2) = none := h.resolve_left h3
    simp [h3, h', ev, mono]

theorem PhiR_even (v : Fin 1053) (m : Ex) (h3 : ¬ v.val % 27 < 3)
    (hm : planeExp ((v.val % 27 - 3) / 2) = some m) (he : (v.val % 27 - 3) % 2 = 0) :
    PhiR ι U v =
      ι half * (ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2))) - ι Q12.I *
          ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1))) * mono U m +
      ι half * (ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2))) + ι Q12.I *
          ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1))) * mono U (Ex.neg m) := by
  unfold PhiR phiTerms
  simp [h3, hm, he, ev]

theorem PhiR_odd (v : Fin 1053) (m : Ex) (h3 : ¬ v.val % 27 < 3)
    (hm : planeExp ((v.val % 27 - 3) / 2) = some m) (he : ¬ (v.val % 27 - 3) % 2 = 0) :
    PhiR ι U v =
      ι half * (ι Q12.I * (ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2))) - ι Q12.I *
          ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1)))) * mono U m -
      ι half * (ι Q12.I * (ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2))) + ι Q12.I *
          ι (bq (27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1)))) * mono U (Ex.neg m) := by
  unfold PhiR phiTerms
  simp [h3, hm, he, ev]
  ring

end Unfold

theorem toComplex_half : Q12.toComplex half = 1 / 2 := by
  simp [half, Q12.toComplex_lit]

/-- **L1 bridge.** At every unit phase `ξ`, the Laurent configuration `Φ(u)` evaluated at
`u = ξ / exactPhases` is exactly the accepted literal configuration `literalCfg ξ`. -/
theorem phi_bridge (ξ : Fin 4 → ℂ) (hξ : IsUnitPhase ξ) (v : Fin 1053) :
    PhiR Q12.toComplex (Uph ξ hξ) v = ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ) := by
  have hv := v.isLt
  have hCn : ((PartialAction.pack (literalCfg ξ) v : ℝ) : ℂ) = Cn ξ v.val := by
    simp [Cn, hv]
  rw [hCn]
  by_cases hf : v.val % 27 < 3 ∨ planeExp ((v.val % 27 - 3) / 2) = none
  · rw [PhiR_fixed _ _ v hf, base_link]
    have e : v.val = 27 * (v.val / 27) + v.val % 27 := by omega
    rw [e]
    exact (fixed_pc ξ hξ _ _ (by omega) (Nat.mod_lt _ (by norm_num)) (by simpa using hf)).symm
  · have h3 : ¬ v.val % 27 < 3 := fun h => hf (Or.inl h)
    have hne : planeExp ((v.val % 27 - 3) / 2) ≠ none := fun h => hf (Or.inr h)
    obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
    have hcl := charLaw ξ hξ (v.val / 27) (by omega) _ m (by omega) hm
    have hA := assemble _ _ _ _ _ (Cn_star ξ _) (Cn_star ξ _) (Cn_star _ _) (Cn_star _ _)
      (star_mono ξ hξ m) hcl
    by_cases he : (v.val % 27 - 3) % 2 = 0
    · rw [PhiR_even _ _ v m h3 hm he]
      simp only [base_link, Q12.toComplex_I, toComplex_half, mono_neg]
      have hva : v.val = 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) := by omega
      conv_rhs => rw [hva]
      rw [hA.1]
    · rw [PhiR_odd _ _ v m h3 hm he]
      simp only [base_link, Q12.toComplex_I, toComplex_half, mono_neg]
      have hva : v.val = 27 * (v.val / 27) + 3 + 2 * ((v.val % 27 - 3) / 2) + 1 := by omega
      conv_rhs => rw [hva]
      rw [hA.2]

end Option2.NativeStress.HTPhaseKron
#print axioms Option2.NativeStress.HTPhaseKron.phi_bridge
