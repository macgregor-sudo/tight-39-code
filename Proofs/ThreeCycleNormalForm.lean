module

public import ThreeCycleParameterUniqueness
public import Mathlib.Algebra.Module.Equiv.Basic
import all FourierTransport

/-!
# Real-linear normal form for the original UEB derivative kernel

The existing NormalForm is unchanged. Its six real slots index (block, diagonal
entry); its six free complex slots index (row, mode 0 or 2). The resonant slot j
is the original middle-mode seed at k=j-1, preserving the proved phase shift.
The inverse laws consume the checked matrix/Fourier parameter characterization.
First-party proof; imported mathlib provenance unchanged. No release license assigned.
-/

@[expose] public section
noncomputable section

namespace UnitaryErrorBases.ThreeCycleMatrix

open ThreeCycleFourier

def sixIndex : (Index × Fin 2) ≃ Fin 6 :=
  (((ZMod.finEquiv 3).toEquiv.symm).prodCongr (Equiv.refl (Fin 2))).trans finProdFinEquiv

def normalFormDiagonal {d : PhaseTriple} (x : NormalForm d) : Index → Fin 2 → ℝ :=
  fun b t => x.1 (sixIndex (b, t))

def normalFormSeed (d : PhaseTriple) (x : NormalForm d) : Index → Index → ℂ := by
  classical
  exact fun k mu => if mu = 1 then
    if h : d.val (k + 1) ^ 3 = 1 then x.2.2 ⟨k + 1, h⟩ else 0
    else if mu = 0 then x.2.1 (sixIndex (k, 0)) else x.2.1 (sixIndex (k, 1))

def packParameters (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) : NormalForm d :=
  (fun i => s (sixIndex.symm i).1 (sixIndex.symm i).2,
   fun i => a (sixIndex.symm i).1 (if (sixIndex.symm i).2 = 0 then 0 else 2),
   fun j => a (j.val - 1) 1)

theorem normalFormSeed_supported (d : PhaseTriple) (x : NormalForm d) :
    ResonanceSupported d (normalFormSeed d x) := by
  classical
  intro k
  by_cases h : d.val (k + 1) ^ 3 = 1 <;> simp [normalFormSeed, h]

theorem normalFormDiagonal_pack (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) : normalFormDiagonal (packParameters d s a) = s := by
  funext b t
  simp [normalFormDiagonal, packParameters]

theorem normalFormSeed_pack (d : PhaseTriple) (s : Index → Fin 2 → ℝ)
    (a : Index → Index → ℂ) (ha : ResonanceSupported d a) :
    normalFormSeed d (packParameters d s a) = a := by
  classical
  funext k mu
  rcases (by decide : ∀ mu : Index, mu = 0 ∨ mu = 1 ∨ mu = 2) mu with h | h | h
  · subst mu
    simp [normalFormSeed, packParameters]
  · subst mu
    by_cases hr : d.val (k + 1) ^ 3 = 1
    · simp [normalFormSeed, packParameters, hr]
    · simp [normalFormSeed, hr, (resonanceSupported_iff d a).mp ha k hr]
  · subst mu
    simp [normalFormSeed, packParameters, show (2 : Index) ≠ 1 by decide,
      show (2 : Index) ≠ 0 by decide]

theorem pack_normalForm (d : PhaseTriple) (x : NormalForm d) :
    packParameters d (normalFormDiagonal x) (normalFormSeed d x) = x := by
  classical
  apply Prod.ext
  · funext i
    simp [packParameters, normalFormDiagonal]
  · apply Prod.ext
    · funext i
      obtain ⟨⟨k, t⟩, rfl⟩ := sixIndex.surjective i
      fin_cases t <;>
        simp [packParameters, normalFormSeed, show (2 : Index) ≠ 1 by decide,
          show (2 : Index) ≠ 0 by decide]
    · funext j
      simp [packParameters, normalFormSeed, j.property]

theorem normalFormDiagonal_add (d : PhaseTriple) (x y : NormalForm d) :
    normalFormDiagonal (x + y) = normalFormDiagonal x + normalFormDiagonal y := rfl

theorem normalFormDiagonal_smul (d : PhaseTriple) (r : ℝ) (x : NormalForm d) :
    normalFormDiagonal (r • x) = r • normalFormDiagonal x := rfl

theorem normalFormSeed_add (d : PhaseTriple) (x y : NormalForm d) :
    normalFormSeed d (x + y) = normalFormSeed d x + normalFormSeed d y := by
  classical
  funext k mu
  simp only [normalFormSeed, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp

theorem normalFormSeed_smul (d : PhaseTriple) (r : ℝ) (x : NormalForm d) :
    normalFormSeed d (r • x) = r • normalFormSeed d x := by
  classical
  funext k mu
  simp only [normalFormSeed, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> simp

theorem reconstruct_add (d : PhaseTriple) (a c : Index → Index → ℂ) :
    reconstruct d (a + c) = reconstruct d a + reconstruct d c := by
  funext b k mu
  simp only [reconstruct, Pi.add_apply]
  split_ifs <;> simp [mul_add]

theorem reconstruct_real_smul (d : PhaseTriple) (r : ℝ) (a : Index → Index → ℂ) :
    reconstruct d (r • a) = r • reconstruct d a := by
  funext b k mu
  simp only [reconstruct, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul] <;> ring

theorem inverse_add (y z : Coordinates) : inverse (y + z) = inverse y + inverse z := by
  funext a b k
  simp [inverse, add_mul, Finset.sum_add_distrib]

theorem inverse_real_smul (r : ℝ) (y : Coordinates) : inverse (r • y) = r • inverse y := by
  funext a b k
  simp [inverse, Finset.smul_sum, mul_assoc]

theorem tracelessDiagonal_add (s t : Fin 2 → ℝ) :
    tracelessDiagonal (s + t) = tracelessDiagonal s + tracelessDiagonal t := by
  funext k
  simp only [tracelessDiagonal, Pi.add_apply]
  split_ifs <;> ring

theorem tracelessDiagonal_smul (r : ℝ) (s : Fin 2 → ℝ) :
    tracelessDiagonal (r • s) = r • tracelessDiagonal s := by
  funext k
  simp only [tracelessDiagonal, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

theorem parameterMatrix_add (s t : Index → Fin 2 → ℝ) (y z : Coordinates) :
    parameterMatrix (s + t) (y + z) = parameterMatrix s y + parameterMatrix t z := by
  funext p i j
  change parameterMatrix (s + t) (y + z) p i j =
    parameterMatrix s y p i j + parameterMatrix t z p i j
  simp only [parameterMatrix, Pi.add_apply, tracelessDiagonal_add]
  split_ifs <;> simp [Complex.ofReal_add, mul_add, star_add] <;> ring

theorem parameterMatrix_real_smul (r : ℝ) (s : Index → Fin 2 → ℝ) (y : Coordinates) :
    parameterMatrix (r • s) (r • y) = r • parameterMatrix s y := by
  funext p i j
  change parameterMatrix (r • s) (r • y) p i j = r • parameterMatrix s y p i j
  simp only [parameterMatrix, Pi.smul_apply, tracelessDiagonal_smul]
  split_ifs <;> simp [Complex.real_smul, Complex.ofReal_mul, star_mul] <;> ring

theorem fromCoordinates_add (d : PhaseTriple) (M N : Family) :
    fromCoordinates d (M + N) = fromCoordinates d M + fromCoordinates d N := by
  funext p
  simp [fromCoordinates, Matrix.mul_add, Matrix.add_mul]

theorem fromCoordinates_real_smul (d : PhaseTriple) (r : ℝ) (M : Family) :
    fromCoordinates d (r • M) = r • fromCoordinates d M := by
  funext p
  simp [fromCoordinates, Matrix.mul_smul, Matrix.smul_mul]

def normalFormTangentLinear (d : PhaseTriple) :
    NormalForm d →ₗ[ℝ] firstOrderSpace (monomialFamily d) where
  toFun x := ⟨fromCoordinates d
    (parameterMatrix (normalFormDiagonal x) (inverse (reconstruct d (normalFormSeed d x)))),
    parameterMatrix_mem_firstOrder d _ _ (normalFormSeed_supported d x)⟩
  map_add' x y := by
    apply Subtype.ext
    change fromCoordinates d (parameterMatrix (normalFormDiagonal (x + y))
      (inverse (reconstruct d (normalFormSeed d (x + y))))) = _
    rw [normalFormDiagonal_add, normalFormSeed_add, reconstruct_add, inverse_add,
      parameterMatrix_add, fromCoordinates_add]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    change fromCoordinates d (parameterMatrix (normalFormDiagonal (r • x))
      (inverse (reconstruct d (normalFormSeed d (r • x))))) = _
    rw [normalFormDiagonal_smul, normalFormSeed_smul, reconstruct_real_smul,
      inverse_real_smul, parameterMatrix_real_smul, fromCoordinates_real_smul]
    rfl

theorem normalFormTangentLinear_bijective (d : PhaseTriple) :
    Function.Bijective (normalFormTangentLinear d) := by
  constructor
  · intro x y h
    have he := congrArg Subtype.val h
    have hp := tangent_parameters_injective d (normalFormDiagonal x) (normalFormDiagonal y)
      (normalFormSeed d x) (normalFormSeed d y) he
    calc
      x = packParameters d (normalFormDiagonal x) (normalFormSeed d x) :=
        (pack_normalForm d x).symm
      _ = packParameters d (normalFormDiagonal y) (normalFormSeed d y) := by rw [hp.1, hp.2]
      _ = y := pack_normalForm d y
  · intro V
    obtain ⟨s, a, ha, hv⟩ := (mem_firstOrder_iff_parameters d V.val).mp V.property
    refine ⟨packParameters d s a, ?_⟩
    apply Subtype.ext
    change fromCoordinates d (parameterMatrix (normalFormDiagonal (packParameters d s a))
      (inverse (reconstruct d (normalFormSeed d (packParameters d s a))))) = V.val
    rw [normalFormDiagonal_pack, normalFormSeed_pack d s a ha]
    exact hv.symm

/-- The exact original Challenge's real-linear normal form, with unchanged carrier. -/
def firstOrderNormalForm (d : PhaseTriple) :
    firstOrderSpace (monomialFamily d) ≃ₗ[ℝ] NormalForm d :=
  ({ normalFormTangentLinear d,
     Equiv.ofBijective (normalFormTangentLinear d) (normalFormTangentLinear_bijective d) with } :
    NormalForm d ≃ₗ[ℝ] firstOrderSpace (monomialFamily d)).symm

end UnitaryErrorBases.ThreeCycleMatrix
