import Mathlib
import Blaster

abbrev Addr := String
abbrev Amount := Int

structure Account where
  addr : Addr
  bal : Amount
  deriving Repr

abbrev Ledger := List Account

namespace Ledger
open List

def addAccount (ledger : Ledger) (acc : Account) : Ledger :=
  if ledger.any (fun x => x.addr == acc.addr) || acc.bal < 0
  then ledger
  else acc :: ledger

theorem addAccount_exists (ledger : Ledger) (acc : Account) :
  acc ∈ ledger -> List.length (ledger.addAccount acc) = List.length ledger := by
  intro acc_in_ledger
  unfold addAccount
  have any_true : ledger.any (λ x => x.addr == acc.addr) = true := by
    rw [List.any_eq_true]
    refine ⟨acc, ?_⟩
    constructor
    . assumption
    . rw [BEq.refl]
  simp [any_true]

def getBalance (ledger : Ledger) (name : Addr) : Option Amount := do
  let acc <- ledger.find? (λ x => x.addr == name)
  return acc.bal
 
def getSupply (ledger : Ledger) : Amount := sum $ ledger.map (λ x => x.bal)

def debitAccount (ledger : Ledger) (name : Addr) (amt : Amount) : Option Ledger :=
  match ledger with    
  | [] => none
  | h :: t =>
      if (h.addr == name) then
        if (amt <= h.bal) then
          some ({ h with bal := h.bal - amt } :: t)
        else none
      else do
        let ledger' <- debitAccount t name amt
        return (h :: ledger')

lemma debit_subtracts (l : Ledger) (addr : Addr) (amt : Amount) :
  ∀ l', l.debitAccount addr amt = some l'
  -> l'.getSupply = l.getSupply - amt := by
  induction l with
  | nil => simp [debitAccount]
  | cons x xs ih =>
    simp [debitAccount, getSupply] at *
    split
    next => split <;> simp_all; ring
    next =>
      cases h : debitAccount xs addr amt with
      | none    => simp
      | some ys =>
        simp [Option.bind]
        rw [ ih ys h ]
        ring

def creditAccount (ledger : Ledger) (addr : Addr) (amt : Amount) : Option Ledger :=
  match ledger with
  | []     => none
  | h :: t =>
    if (h.addr == addr)
    then some $ { h with bal := h.bal + amt } :: t
    else do
      let ledger' <- creditAccount t addr amt
      return (h :: ledger')

lemma credit_adds (l : Ledger) (addr : Addr) (amt : Amount) :
  ∀ l', l.creditAccount addr amt = some l'
  -> l'.getSupply = l.getSupply + amt := by sorry

def transferFunds (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) : Option Ledger := do
  let ledger' <- debitAccount ledger fromAddr amt
  creditAccount ledger' toAddr amt

theorem transfer_preserves (l : Ledger) (fromAddr toAddr : Addr) (amt : Amount) :
  ∀ l', l.transferFunds fromAddr toAddr amt = some l'
  -> l'.getSupply = l.getSupply := by
  induction l with
  | nil => simp [transferFunds, debitAccount]
  | cons x xs xih =>
    simp [transferFunds]
    cases h1 : debitAccount (x :: xs) fromAddr amt with
    | none => simp
    | some xs1 =>
      simp
      cases h2 : creditAccount xs1 toAddr amt with
      | none => simp
      | some xs2 =>
        simp
        have d := debit_subtracts (x :: xs) fromAddr amt xs1
        have c := credit_adds xs1 toAddr amt xs2
        rw [ c h2, d h1 ]
        ring

structure Proposal where
  id : Nat
  addr : Addr
  amt : Amount
  yes : Nat
  no : Nat
  done : Bool
  deriving Repr

structure DAO where
  ledger : Ledger
  prop : List Proposal
  deriving Repr

inductive Action
  | contrib
  | propose
  | vote
  | execute
  deriving Repr

inductive Vote
  | yes
  | no
  deriving Repr

namespace DAO

def genesis : DAO :=
  {
    ledger := [ { addr := "treasury", bal := 0 } ]
    prop := []
  }

def treasury (d : DAO) : Option Amount := d.ledger.getBalance "treasury"

def supply (d : DAO) : Amount := sorry
