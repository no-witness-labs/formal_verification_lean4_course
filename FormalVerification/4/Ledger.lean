import Mathlib.Tactic
import Blaster

abbrev Ident := Nat
abbrev Amount := Nat

structure Account where
  id : Ident
  name : String
  bal : Amount
  deriving Repr, BEq, DecidableEq

abbrev Ledger := List Account

def addAccount (l : Ledger) (a : Account) : Ledger :=
  if l.any (fun x => x.id == a.id)
  then l
  else a :: l

theorem addAccount_length (l : Ledger) (a : Account) :
  (addAccount l a).length = l.length ∨ (addAccount l a).length = l.length + 1
  := by
  unfold addAccount
  split <;> simp

theorem addAccount_exists (l : Ledger) (a : Account) :
  a ∈ l -> (addAccount l a).length = l.length := by
  intro a_in_l
  unfold addAccount
  split_ifs with if_any
  next => rfl
  next =>
    have if_any_contra : List.any l (λ x => x.id == a.id) = true := by
      simp [List.any_eq_true]
      use a
    contradiction

theorem addAccount_not_exists (l : Ledger) (a : Account) :
  ¬ (l.any (λ x => x.id == a.id) = true) -> (addAccount l a).length = l.length + 1 := by sorry

theorem addAccount_idem (l : Ledger) (a : Account) :
  addAccount (addAccount l a) a = addAccount l a := by sorry

def getBalance (l : Ledger) (id : Ident) : Option Amount := sorry
 
def getSupply (l : Ledger) : Amount := sorry

def debitAccount (l : Ledger) (id : Ident) (amt : Amount) : Option Ledger :=
  match l with
  | [] => none
  | h :: t =>
    if (h.id == id) then
      if (h.bal >= amt) then
        some ({ h with bal := h.bal - amt } :: t)
      else none
    else Functor.map (fun t' => h :: t') (debitAccount t id amt)

def creditAccount (l : Ledger) (id : Ident) : (amt : Amount) : Option Ledger := sorry

def transferFunds (l : Ledger) (fromId : Ident) (toId : Ident) (amt : Amount) : Option Ledger := sorry
