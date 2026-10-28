module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# A6 compact route: the one field instance on `ZMod 1048573`

Every file of the A6 compact library uses Mathlib's `ZMod.instField` (Mathlib/Algebra/Field/ZMod.lean), selected by the
single `Fact (Nat.Prime 1048573)` instance below. No other `Field (ZMod 1048573)` instance or `Fact` instance may be
declared anywhere in the library (Q's `Matrix.zmodField` is only ever used by Q inside proofs via `letI`; the
feasibility copy of TopGlue's global `fieldZMod1048573` instance is removed). `zmodField_eq` records that Q's structure
is definitionally Mathlib's (`A6Compact.zmodField_eq`, proved by `rfl` in interface/A6SpecLin.lean), so facts proved
under Q's `letI` transfer.
Lean v4.35.0-rc2, Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55; Mathlib-only imports (cheap for certificate files).
-/

namespace A6Compact

/-- The prime. -/
abbrev p : ℕ := 1048573

theorem prime_p : Nat.Prime 1048573 := by norm_num

/-- THE primality instance (selects Mathlib's `ZMod.instField`). -/
instance fact_prime_p : Fact (Nat.Prime 1048573) := ⟨prime_p⟩

/-- The field `F = ZMod 1048573`. -/
abbrev F : Type := ZMod 1048573

end A6Compact
