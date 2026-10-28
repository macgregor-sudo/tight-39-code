module

public import NativeIncludedQuartetReadouts

/-!
# Shared Fourier definitions

The accepted NativeIncludedQuartetReadouts artifact already owns the complete
UnitaryErrorBases.ThreeCycleFourier namespace. Its 215-line namespace body is
byte-identical to the standalone first-party FourierTransport source used by
the isolated derivative graph. This module adds no declaration or assumption.
It selects the existing native owner for integration, avoiding a second import
of the same declarations. 

Native and mathlib provenance remain in the imported accepted module. This
first-party import facade does not copy upstream code or assign a release license.
Original standalone source identity: native-src/FourierTransport.lean.
-/
