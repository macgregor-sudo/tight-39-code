/-
First-party isolated consumer of the SCV carrier bridge, 2026-10-23.
No outgoing project license is selected here. The imported SCV domain theorem
uses the analytic identity principle; this module does not import Noetherianity.
-/
module

public import ConvergentGermSCVBridge
public import Mathlib.Algebra.Ring.Equiv

@[expose] public section

namespace ConvergentGermSCVBridge

open ConvergentResidualJets

/-- The accepted ring of actual analytic germs is an integral domain. -/
theorem germRing_isDomain (n : ℕ) : IsDomain (GermRing n) :=
  MulEquiv.isDomain _ (germEquiv n).toRingEquiv.toMulEquiv

/-- Kernel primality needs no retraction, surjectivity or Noetherian premise. -/
theorem kernel_isPrime {m n : ℕ} (f : GermRing n →ₐ[ℂ] GermRing m) :
    (RingHom.ker f.toRingHom).IsPrime := by
  letI := germRing_isDomain m
  exact RingHom.ker_isPrime f.toRingHom

end ConvergentGermSCVBridge
