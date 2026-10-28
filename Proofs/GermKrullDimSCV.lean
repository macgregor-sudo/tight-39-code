module

/-
First-party discharge of the Noetherian instance argument of `GermKrullDim`.
Pin: Lean v4.35.0-rc2, Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
-/
public import GermKrullDim
public import ConvergentGermSCVNoetherian

@[expose] public section

namespace GermKrullDim

open ConvergentResidualJets

/-- `ringKrullDim (GermRing n) = n`, unconditional. -/
theorem ringKrullDim_germRing' (n : ℕ) : ringKrullDim (GermRing n) = (n : WithBot ℕ∞) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing n
  exact ringKrullDim_germRing n

theorem ringKrullDim_quotient_ker_of_surjective' {m d : ℕ} (ρ : GermRing m →ₐ[ℂ] GermRing d)
    (hρ : Function.Surjective ρ) :
    ringKrullDim (GermRing m ⧸ RingHom.ker ρ.toRingHom) = (d : WithBot ℕ∞) := by
  letI := ConvergentGermSCVBridge.germRing_isNoetherianRing d
  exact ringKrullDim_quotient_ker_of_surjective ρ hρ

end GermKrullDim

#print axioms GermKrullDim.ringKrullDim_germRing'
#print axioms GermKrullDim.ringKrullDim_quotient_ker_of_surjective'
