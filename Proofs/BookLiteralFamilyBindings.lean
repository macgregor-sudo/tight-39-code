module

public import BookNativeConjugationFamily

@[expose] public section

/-! Fixed literal base, signed coordinate transports, and exact A5 anchor labels. -/
set_option Elab.async false
noncomputable section
namespace Option2.NativeStress.BookHT.TangentCoordinates
open Option2.BookNativeBase CKM.NativeFirstOrder CKM.NativeFourFamily
open NativePolynomial CompactAlbert
open QuadraticCertificate.ExactCKMConfiguration

theorem literalPoint_exactPhases : literalPoint exactPhases = nativePoint := rfl

theorem exactPhases_unit : IsUnitPhase exactPhases := by
  intro i
  fin_cases i <;> norm_num [exactPhases, Complex.normSq_apply, Complex.div_re, Complex.div_im]

theorem pack_literalCfg_exactPhases : PartialAction.pack (literalCfg exactPhases) = bookBase := by
  rw [bookBase_eq_originalSeed]
  rfl

theorem bookPointQ12_complex_native (p : Fin 39) (k : Fin 27) :
    Q12.toComplex (bookPointQ12 p k) = (upperCoordinates (literalPoint exactPhases p) k : ℂ) := by
  let v : Fin 1053 := ⟨27*p.val+k.val, by omega⟩
  have hv : bookQ12 v = bookPointQ12 p k := by
    unfold bookQ12
    congr 1 <;> apply Fin.ext <;> dsimp [v] <;> omega
  rw [← hv, ← bookBase_complex, ← pack_literalCfg_exactPhases]
  change ((PartialAction.pack (literalCfg exactPhases) v : ℝ) : ℂ) = _
  have hp : (⟨v.val/27, by omega⟩ : Fin 39) = p := by apply Fin.ext; dsimp [v]; omega
  have hk : (⟨v.val%27, by omega⟩ : Fin 27) = k := by apply Fin.ext; dsimp [v]; omega
  simp only [PartialAction.pack, hp, hk, literalCfg]

theorem anchorRelabel_mask : ∀ (s : Fin 4) (p : Fin 39),
    ((anchorRelabel s).symm p).val < 12 ↔
      p.val/3 = 0 ∨ (1+3*s.val ≤ p.val/3 ∧ p.val/3 ≤ 3+3*s.val) := by
  decide +kernel

theorem q12SheetInverse_complex_native (s : Fin 4) (p : Fin 39) (k : Fin 27) :
    Q12.toComplex (q12SheetInverse s (bookPointQ12 p) k) =
      (upperCoordinates (anchorΨ s (literalPoint exactPhases p)) k : ℂ) := by
  fin_cases s <;>
    simp [q12SheetInverse, anchorΨ, transportTinv, upper_signedTransport,
      TitsS.sgnPerm, bookPointQ12_complex_native]

theorem q12SheetTransport_re_native (s : Fin 4) (x : Fin 27 → Q12) (k : Fin 27) :
    (Q12.toComplex (q12SheetTransport s x k)).re =
      upperCoordinates (anchorΨinv s
        (fromUpperCoordinates (fun j => (Q12.toComplex (x j)).re))) k := by
  fin_cases s <;>
    simp [q12SheetTransport, anchorΨinv, transportT, upper_signedTransport,
      TitsS.sgnPerm]

theorem q12SheetTransport_im_native (s : Fin 4) (x : Fin 27 → Q12) (k : Fin 27) :
    (Q12.toComplex (q12SheetTransport s x k)).im =
      upperCoordinates (anchorΨinv s
        (fromUpperCoordinates (fun j => (Q12.toComplex (x j)).im))) k := by
  fin_cases s <;>
    simp [q12SheetTransport, anchorΨinv, transportT, upper_signedTransport,
      TitsS.sgnPerm]

end Option2.NativeStress.BookHT.TangentCoordinates
#check Option2.NativeStress.BookHT.TangentCoordinates.anchorRelabel_mask
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.anchorRelabel_mask
#check Option2.NativeStress.BookHT.TangentCoordinates.q12SheetInverse_complex_native
#print axioms Option2.NativeStress.BookHT.TangentCoordinates.q12SheetInverse_complex_native

