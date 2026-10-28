module

public import DeterminantDescent
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# Spanning descends from a residue field to a characteristic-zero field

Setting: a commutative ring `O` of exact data, an *injective* ring homomorphism `ψ : O →+* K`
to a field `K` (here `Z12 → Q12` or `Z12 → ℂ`), and an arbitrary ring homomorphism
`φ : O →+* F` to a field `F` (here `Z12 → ZMod p`, `p` prime). (`Q12` carries only a
`CommRing` instance in this development, so the characteristic-zero target used is `ℂ`.)

`Matrix.span_eq_top_of_span_map_eq_top`: if the images under `φ` of a family of vectors
`v : ι → (n → O)` span `F^n`, then their images under `ψ` span `K^n`.

Proof. Extract from the `F`-images a linearly independent subfamily with the same span
(`exists_linearIndependent'`); it is a basis, so it has `card n` members. The square matrix over
`O` formed by the corresponding vectors has nonzero determinant after `φ` (its rows are
independent over the field `F`), hence nonzero determinant in `O` (descent), hence nonzero
determinant after `ψ` (ascent along an injective map). Its `ψ`-rows are therefore a basis of
`K^n`, and they are among the `ψ`-images of the family.

Only nonvanishing of a determinant is transferred from `F`; no equality is.
-/

@[expose] public section

namespace Matrix

variable {O K F : Type*} [CommRing O] [Field K] [Field F]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- From a spanning family in `F^n` one can select `card n` members, indexed by `n` itself,
that are linearly independent. -/
theorem exists_independent_selection_of_span_eq_top {ι : Type*} (w : ι → (n → F))
    (hw : Submodule.span F (Set.range w) = ⊤) :
    ∃ sel : n → ι, LinearIndependent F (fun j => w (sel j)) := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' F w
  have hle : ⊤ ≤ Submodule.span F (Set.range (w ∘ a)) := by rw [hspan, hw]
  let b := Module.Basis.mk hli hle
  let _ : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hcard : Fintype.card n = Fintype.card κ := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card]
  let e : n ≃ κ := Fintype.equivOfCardEq hcard
  exact ⟨fun j => a (e j), hli.comp e e.injective⟩

/-- **Spanning descent.** If the `φ`-images of `v` span `F^n` and `ψ` is injective, then the
`ψ`-images of `v` span `K^n`. -/
theorem span_eq_top_of_span_map_eq_top {ι : Type*} (φ : O →+* F) (ψ : O →+* K)
    (hψ : Function.Injective ψ) (v : ι → (n → O))
    (hspan : Submodule.span F (Set.range fun i k => φ (v i k)) = ⊤) :
    Submodule.span K (Set.range fun i k => ψ (v i k)) = ⊤ := by
  obtain ⟨sel, hli⟩ := exists_independent_selection_of_span_eq_top _ hspan
  -- the selected vectors as a square matrix over `O`
  let M : Matrix n n O := fun j => v (sel j)
  have hdetF : (M.map φ).det ≠ 0 := by
    have hunit : IsUnit (M.map φ) := linearIndependent_rows_iff_isUnit.1 hli
    exact ((isUnit_iff_isUnit_det _).1 hunit).ne_zero
  have hdetK : (M.map ψ).det ≠ 0 :=
    map_det_ne_zero_of_injective ψ hψ M (det_ne_zero_of_map_det_ne_zero φ M hdetF)
  refine top_unique ?_
  rw [← span_rows_eq_top_of_det_ne_zero (M.map ψ) hdetK]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨sel j, rfl⟩

/-! ## Instances for the exact ring `Z12` -/

/-! ## `ZMod p` as a field

Mathlib's instance `Field (ZMod p)` lives in `Mathlib.Algebra.Field.ZMod`, whose compiled file is
not available in the build tree used here. We construct the same structure as a definition
(not an instance) and use it locally. -/

-- Provenance: the shape of this structure (fields `mul_inv_cancel`, `inv_zero`, and the
-- default `nnqsmul`/`qsmul` fields) follows Mathlib, commit
-- 065356127b1dc0016f66b7283ce0ce2c4055aa55, file Mathlib/Algebra/Field/ZMod.lean, lines 19–36
-- (Copyright (c) 2018 Chris Hughes. All rights reserved. Author: Chris Hughes; SPDX-License-Identifier: Apache-2.0; license: LICENSE). Modifications: a `def` instead of
-- an `instance`, an explicit primality argument instead of `Fact`, an explicit `exists_pair_ne`
-- field, and a new proof of `mul_inv_cancel` via `ZMod.mul_inv_eq_gcd`.

/-- A nonzero residue modulo a prime `p` is invertible: `a * a⁻¹ = 1`. -/
theorem zmod_mul_inv_cancel_of_prime (p : ℕ) (hp : p.Prime) (a : ZMod p) (ha : a ≠ 0) :
    a * a⁻¹ = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hval : a.val ≠ 0 := (ZMod.val_ne_zero a).2 ha
  have hndvd : ¬ p ∣ a.val := fun hd => hval (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt a))
  have hcop : Nat.Coprime a.val p :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd)
  rw [ZMod.mul_inv_eq_gcd, hcop.gcd_eq_one, Nat.cast_one]

/-- The field structure on `ZMod p` for a prime `p` (a definition, used via `letI`). -/
@[reducible] noncomputable def zmodField (p : ℕ) (hp : p.Prime) : Field (ZMod p) where
  mul_inv_cancel := zmod_mul_inv_cancel_of_prime p hp
  inv_zero := ZMod.inv_zero p
  exists_pair_ne := by
    have : Fact (1 < p) := ⟨hp.one_lt⟩
    exact exists_pair_ne (ZMod p)
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl


/-- Trial division up to a bound: if `2 ≤ p < B²` and no `m` with `2 ≤ m < B` divides `p`, then
`p` is prime. The hypothesis on divisors is decidable and is checked by the kernel. -/
theorem prime_of_no_divisor_below (p B : ℕ) (hp : 2 ≤ p) (hB : p < B * B)
    (hdiv : ∀ m < B, 2 ≤ m → p % m ≠ 0) : Nat.Prime p := by
  refine Nat.prime_def_le_sqrt.2 ⟨hp, fun m hm hle hdvd => ?_⟩
  have hsqrt : Nat.sqrt p < B := Nat.sqrt_lt.2 hB
  exact hdiv m (lt_of_le_of_lt hle hsqrt) hm (Nat.mod_eq_zero_of_dvd hdvd)

/-- `999049` is prime (trial division below `1000`, kernel-checked). -/
theorem prime_999049 : Nat.Prime 999049 :=
  prime_of_no_divisor_below 999049 1000 (by decide) (by decide) (by decide +kernel)

/-- `1048573 = 2²⁰ - 3` is prime (trial division below `1025`, kernel-checked). -/
theorem prime_1048573 : Nat.Prime 1048573 :=
  prime_of_no_divisor_below 1048573 1025 (by decide) (by decide) (by decide +kernel)

/-- `Z12 → ℂ` (through `Q12`) is injective. -/
theorem Z12_toComplex_injective : Function.Injective (Q12.toComplex.comp Z12.toQ12) :=
  Q12.toComplex_injective.comp Z12.toQ12_injective

/-- **Spanning descent for `Z12`, residue field `ZMod p` to `ℂ`.** -/
theorem Z12_span_complex_eq_top_of_span_mod_p {ι : Type*} (p : ℕ) (hp : p.Prime)
    (ri rs : ZMod p) (hi : ri * ri = -1) (hs : rs * rs = 3) (v : ι → (n → Z12))
    (hspan : Submodule.span (ZMod p)
      (Set.range fun i k => Z12.toZMod p ri rs hi hs (v i k)) = ⊤) :
    Submodule.span ℂ (Set.range fun i k => Q12.toComplex (Z12.toQ12 (v i k))) = ⊤ :=
  letI : Field (ZMod p) := zmodField p hp
  span_eq_top_of_span_map_eq_top (F := ZMod p) (Z12.toZMod p ri rs hi hs)
    (Q12.toComplex.comp Z12.toQ12) Z12_toComplex_injective v hspan

/-- The concrete reduction modulo `1048573` (the packing prime `2²⁰ - 3`), to `ℂ`. -/
theorem Z12_span_complex_eq_top_of_span_mod_1048573 {ι : Type*} (v : ι → (n → Z12))
    (hspan : Submodule.span (ZMod 1048573)
      (Set.range fun i k => Z12.toZMod1048573 (v i k)) = ⊤) :
    Submodule.span ℂ (Set.range fun i k => Q12.toComplex (Z12.toQ12 (v i k))) = ⊤ :=
  Z12_span_complex_eq_top_of_span_mod_p 1048573 prime_1048573 _ _ _ _ v hspan

/-- The concrete reduction modulo `999049`, to `ℂ`. -/
theorem Z12_span_complex_eq_top_of_span_mod_999049 {ι : Type*} (v : ι → (n → Z12))
    (hspan : Submodule.span (ZMod 999049)
      (Set.range fun i k => Z12.toZMod999049 (v i k)) = ⊤) :
    Submodule.span ℂ (Set.range fun i k => Q12.toComplex (Z12.toQ12 (v i k))) = ⊤ :=
  Z12_span_complex_eq_top_of_span_mod_p 999049 prime_999049 _ _ _ _ v hspan

end Matrix

end

#print axioms Matrix.exists_independent_selection_of_span_eq_top
#print axioms Matrix.span_eq_top_of_span_map_eq_top
#print axioms Matrix.prime_of_no_divisor_below
#print axioms Matrix.prime_999049
#print axioms Matrix.prime_1048573
#print axioms Matrix.zmod_mul_inv_cancel_of_prime
#print axioms Matrix.zmodField
#print axioms Matrix.Z12_toComplex_injective
#print axioms Matrix.Z12_span_complex_eq_top_of_span_mod_p
#print axioms Matrix.Z12_span_complex_eq_top_of_span_mod_1048573
#print axioms Matrix.Z12_span_complex_eq_top_of_span_mod_999049
