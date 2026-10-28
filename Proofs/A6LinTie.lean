module

public import RowJacobian
public import PipelineNaturality
public import A6LinChecks

@[expose] public section

/-!
# Lane LIN: the tie of the literal rows `lRow r` to the actual Jacobian of `translatedRowModP`

Route (no Jacobian data from package Q): Q's lane-B2 lemma `RowBridge.equationLinearMatrix_translate_fRow` (generic over a
commutative ring) gives `equationLinearMatrix (translate P ∘ fRow h t) r a = sparseLookup (jacobianRow h t r P) a`,
a computable sparse list built from the row's shape table. We replace `pointModP` by the literal `ptLit` (one kernel
check, `pointModP_eq_ptLit`) and `2⁻¹` by `524287`, and compare `jacobianRow` with `lRow r` by the packed-slot engine
(`tieCheck`, kernel runs in `A6LinRunTie*`). Soundness: `sparseLookup_eq_of_tieCheck`.
First-party code.
-/

namespace A6Compact.LinTie

open MvPolynomial PolynomialJets QuarticCertificate.RowBridge QuarticCertificate.PipelineNaturality
open A6Compact A6Compact.LinEngine A6Compact.LinCheck NativePolynomial.ConfigurationResiduals

/-- The reduced point as a literal function. -/
def ptLit (v : Fin 1053) : ZMod 1048573 := ((ptVal v.val : ℕ) : ZMod 1048573)

/-- One kernel evaluation of the 1053 reduced coordinates. -/
theorem pointModP_eq_ptLit : ∀ v, pointModP v = ptLit v := by decide +kernel

theorem half_eq : (2⁻¹ : ZMod 1048573) = 524287 := by decide +kernel

/-- The computed Jacobian row, as a `(key, residue)` list. -/
def jacN (r : Fin 2184) : List (ℕ × ℕ) :=
  (jacobianRow (524287 : ZMod 1048573) 0 r ptLit).map fun e => (e.1.val, e.2.val)

def tieList (r : Fin 2184) : List (ℕ × ℕ) := jacN r ++ (lRow r.val).map fun e => (e.1, P - e.2)

def tieCheck (r : Fin 2184) : Bool :=
  Nat.blt (totalN (tieList r)) (2 ^ 64) && modCheck P 1053 (codeN 64 (tieList r))

def tieCheckN (n : ℕ) : Bool := tieCheck ⟨n % 2184, Nat.mod_lt _ (by decide)⟩

/-! ## Soundness -/

theorem cast_natSlot_jac (l : List (Fin 1053 × ZMod 1048573)) (a : Fin 1053) :
    ((natSlot (l.map fun e => (e.1.val, e.2.val)) a.val : ℕ) : ZMod 1048573) = sparseLookup l a := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    rw [List.map_cons, cast_natSlot_cons, ih]
    unfold sparseLookup
    rw [List.map_cons, List.sum_cons]
    congr 1
    simp only [Fin.val_inj, ZMod.natCast_zmod_val]

theorem cast_natSlot_neg (l : List (ℕ × ℕ)) (hl : valsLe l P = true) (k : ℕ) :
    ((natSlot (l.map fun e => (e.1, P - e.2)) k : ℕ) : ZMod 1048573) = -((natSlot l k : ℕ) : ZMod 1048573) := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [valsLe, List.all_cons, Bool.and_eq_true, Nat.ble_eq] at hl
    rw [List.map_cons, cast_natSlot_cons, cast_natSlot_cons, ih hl.2, neg_add]
    congr 1
    split_ifs
    · rw [Nat.cast_sub hl.1, show ((P : ℕ) : ZMod 1048573) = 0 from ZMod.natCast_self _, zero_sub]
    · simp

theorem sparseLookup_eq_of_tieCheck (r : Fin 2184) (h : tieCheck r = true) (hv : valsLe (lRow r.val) P = true)
    (hk : keysBelow (lRow r.val) 1053 = true) (a : Fin 1053) :
    sparseLookup (jacobianRow (524287 : ZMod 1048573) 0 r ptLit) a =
      ((natSlot (lRow r.val) a.val : ℕ) : ZMod 1048573) := by
  simp only [tieCheck, Bool.and_eq_true, Nat.blt_eq] at h
  have hkeys : ∀ e ∈ tieList r, e.1 < 1053 := by
    intro e he
    simp only [tieList, jacN, List.mem_append, List.mem_map] at he
    rcases he with ⟨x, _, rfl⟩ | ⟨x, hx, rfl⟩
    · exact x.1.isLt
    · simpa using List.all_eq_true.mp hk x hx
  have h0 := natSlot_mod_of_modCheck P 1053 (by norm_num) (by norm_num) _ h.1 hkeys h.2 a.val
  have hz := cast_natSlot_eq_zero (p := 1048573) h0
  rw [tieList, natSlot_append, Nat.cast_add, jacN, cast_natSlot_jac, cast_natSlot_neg _ hv] at hz
  exact sub_eq_zero.mp (by rw [sub_eq_add_neg]; exact hz)

/-- `translatedRowModP`'s Jacobian is the literal-point `jacobianRow` (no kernel evaluation besides the point check). -/
theorem equationLinearMatrix_eq_jacobianRow (r : Fin 2184) (a : Fin 1053) :
    equationLinearMatrix translatedRowModP r a =
      sparseLookup (jacobianRow (524287 : ZMod 1048573) 0 r ptLit) a := by
  have e1 : equationLinearMatrix translatedRowModP r a =
      equationLinearMatrix (fun r => translate pointModP (fRow (2⁻¹ : ZMod 1048573) 3⁻¹ r)) r a := rfl
  rw [e1, equationLinearMatrix_translate_fRow, jacobianEntry_eq_sparseLookup, half_eq,
    show pointModP = ptLit from funext pointModP_eq_ptLit]
  rfl

end A6Compact.LinTie
