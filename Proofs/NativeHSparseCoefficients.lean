module

public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Ring.Hom.Defs
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! A finite sparse coefficient tree with a proved interpretation. It stores
computed sums only; no coefficient table or polynomial identity is assumed. -/

namespace Option2.NativeStress.NativeH.Reproduction

universe u

inductive CoeffTree (R : Type u) : Nat → Type u
  | empty {n} : CoeffTree R n
  | leaf (value : R) : CoeffTree R 0
  | branch {n} : CoeffTree R n → CoeffTree R n → CoeffTree R (n+1)
  deriving DecidableEq

namespace CoeffTree

variable {R S : Type*} [CommRing R] [CommRing S] [DecidableEq R]

def leafOf (c : R) : CoeffTree R 0 := if c = 0 then .empty else .leaf c

def branchOf {n} : CoeffTree R n → CoeffTree R n → CoeffTree R (n+1)
  | .empty, .empty => .empty
  | l, r => .branch l r

def evaluate (f : R →+* S) : {n : Nat} → CoeffTree R n → (Nat → S) → S
  | _, .empty, _ => 0
  | _, .leaf c, w => f c * w 0
  | n+1, .branch l r, w => evaluate f l w + evaluate f r (fun k => w (2^n+k))

@[simp] theorem evaluate_leafOf (f : R →+* S) (c : R) (w : Nat → S) :
    evaluate f (leafOf c) w = f c * w 0 := by
  by_cases h : c = 0 <;> simp [leafOf, h, evaluate]

@[simp] theorem evaluate_branchOf (f : R →+* S) {n} (l r : CoeffTree R n)
    (w : Nat → S) :
    evaluate f (branchOf l r) w = evaluate f l w + evaluate f r (fun k => w (2^n+k)) := by
  cases l <;> cases r <;> simp [branchOf, evaluate]

def addAt : {n : Nat} → Nat → R → CoeffTree R n → CoeffTree R n
  | 0, _, c, .empty => leafOf c
  | 0, _, c, .leaf d => leafOf (c+d)
  | n+1, k, c, .empty =>
      if k < 2^n then branchOf (addAt k c (.empty : CoeffTree R n)) .empty
      else branchOf .empty (addAt (k-2^n) c (.empty : CoeffTree R n))
  | n+1, k, c, .branch l r =>
      if k < 2^n then branchOf (addAt k c l) r
      else branchOf l (addAt (k-2^n) c r)

theorem evaluate_addAt (f : R →+* S) {n} (t : CoeffTree R n) (k : Nat)
    (hk : k < 2^n) (c : R) (w : Nat → S) :
    evaluate f (addAt k c t) w = f c * w k + evaluate f t w := by
  induction n generalizing k w with
  | zero =>
      have h : k = 0 := by simpa using hk
      subst k
      cases t <;> simp [addAt, evaluate, map_add, add_mul]
  | succ n ih =>
      have hp : 2^(n+1) = 2^n + 2^n := by rw [pow_succ]; omega
      by_cases h : k < 2^n
      · cases t <;> simp [addAt, h, evaluate, ih _ k h, add_assoc]
      · have hk' : k - 2^n < 2^n := by omega
        have he : 2^n + (k - 2^n) = k := by omega
        cases t <;> simp [addAt, h, evaluate, ih _ _ hk', he, add_comm, add_left_comm]

/-- Fold an ordered stream into the sparse exact coefficient tree. -/
def collect {n} (es : List (Nat × R)) : CoeffTree R n :=
  es.foldr (fun e t => addAt e.1 e.2 t) .empty

theorem evaluate_collect (f : R →+* S) {n} (es : List (Nat × R))
    (he : ∀ e ∈ es, e.1 < 2^n) (w : Nat → S) :
    evaluate f (collect (n:=n) es) w = (es.map fun e => f e.2 * w e.1).sum := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      rw [collect, List.foldr_cons, evaluate_addAt f _ _ (he e (by simp))]
      rw [show es.foldr (fun e t => addAt e.1 e.2 t) .empty = collect es from rfl]
      rw [ih (fun x hx => he x (by simp [hx]))]
      rfl

def entries : {n : Nat} → CoeffTree R n → List (Nat × R)
  | _, .empty => []
  | _, .leaf c => [(0,c)]
  | n+1, .branch l r => entries l ++ (entries r).map (fun e => (2^n+e.1,e.2))

theorem entries_evaluate (f : R →+* S) {n} (t : CoeffTree R n) (w : Nat → S) :
    ((entries t).map fun e => f e.2 * w e.1).sum = evaluate f t w := by
  induction t generalizing w with
  | empty => rfl
  | leaf c => simp [entries, evaluate]
  | @branch n l r hl hr =>
      simp only [entries, List.map_append, List.sum_append, List.map_map, evaluate,
        Function.comp_def]
      exact congrArg₂ (· + ·) (hl w) (hr (fun k => w (2^n+k)))

end CoeffTree
end Option2.NativeStress.NativeH.Reproduction
