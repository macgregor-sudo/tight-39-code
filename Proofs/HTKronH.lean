module

public import HTKronEngine

@[expose] public section

/-!
# The twelve H Kronecker evaluations (ENGINE, first-party)

Each statement compares the exact `ℤ[i, √3]` value of the native evaluator (original weights,
row shapes and eigencolumns) at the Golomb–Kronecker point with the Book value, by `decide +kernel`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option Elab.async false

namespace Option2.NativeStress.HTRouteKron

theorem hCheck00 : hValue 0 0 = hBookValue 0 0 := by decide +kernel

theorem hCheck01 : hValue 0 1 = hBookValue 0 1 := by decide +kernel

theorem hCheck02 : hValue 0 2 = hBookValue 0 2 := by decide +kernel

theorem hCheck10 : hValue 1 0 = hBookValue 1 0 := by decide +kernel

theorem hCheck11 : hValue 1 1 = hBookValue 1 1 := by decide +kernel

theorem hCheck12 : hValue 1 2 = hBookValue 1 2 := by decide +kernel

theorem hCheck20 : hValue 2 0 = hBookValue 2 0 := by decide +kernel

theorem hCheck21 : hValue 2 1 = hBookValue 2 1 := by decide +kernel

theorem hCheck22 : hValue 2 2 = hBookValue 2 2 := by decide +kernel

theorem hCheck30 : hValue 3 0 = hBookValue 3 0 := by decide +kernel

theorem hCheck31 : hValue 3 1 = hBookValue 3 1 := by decide +kernel

theorem hCheck32 : hValue 3 2 = hBookValue 3 2 := by decide +kernel

end Option2.NativeStress.HTRouteKron
