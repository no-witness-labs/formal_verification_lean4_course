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

def noneg (ledger : Ledger) : Prop := ledger.Forall (fun x => x.bal >= 0)

def addAccount (ledger : Ledger) (acc : Account) : Ledger :=
  if ledger.any (fun x => x.addr == acc.addr) then
    ledger
  else if acc.bal < 0 then
    ledger
  else acc :: ledger

lemma addAccount_length
  (ledger : Ledger) (acc : Account) :
  acc ∈ ledger -> List.length (ledger.addAccount acc) = List.length ledger := by
  intro hmem
  simp [addAccount]
  split_ifs with hex hpos <;> simp
  exact hex ⟨acc, hmem, rfl⟩

lemma addAccount_preserves_noneg (ledger : Ledger) (acc : Account) :
  ledger.noneg -> (ledger.addAccount acc).noneg := by
  intro hnoneg
  simp [addAccount]
  split_ifs with hex hpos <;> simp_all [noneg]

def getBalance (ledger : Ledger) (name : Addr) : Option Amount := do
  let acc <- ledger.find? (λ x => x.addr == name)
  return acc.bal
 
def getSupply (ledger : Ledger) : Amount := (ledger.map (λ x => x.bal)).sum

def debitAccount (ledger : Ledger) (addr : Addr) (amt : Amount) : Option Ledger :=
  match ledger with    
  | [] => none
  | h :: t =>
      if (h.addr == addr) then
        if (amt <= h.bal) then
          some ({ h with bal := h.bal - amt } :: t)
        else none
      else do
        let ledger' <- debitAccount t addr amt
        return (h :: ledger')

lemma debitAccount_subtracts_supply (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.debitAccount addr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply - amt := by
  induction ledger with
  | nil => simp [debitAccount]
  | cons x xs xih =>
    simp [debitAccount, getSupply] at ⊢ xih
    split
    next => split <;> simp_all; ring
    next =>
      cases h : debitAccount xs addr amt with
      | none    => simp
      | some ys =>
        simp [Option.bind]
        rw [ xih ys h ]
        ring

lemma debitAccount_preserves_noneg (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.noneg
  -> ledger.debitAccount addr amt = some ledger'
  -> ledger'.noneg := by
  induction ledger with
  | nil => simp [debitAccount, noneg]
  | cons x xs xih =>
    intro ledger' hnoneg hdebit
    simp [debitAccount] at hdebit
    simp [noneg] at hnoneg
    obtain ⟨hnonegx, hnonegxs⟩ := hnoneg
    by_cases haddr : x.addr = addr
    next =>
      simp [haddr] at hdebit
      obtain ⟨hamt, hledger⟩ := hdebit
      subst hledger
      simp [noneg]
      exact ⟨hamt, hnonegxs⟩
    next =>
      simp [haddr] at hdebit
      cases hdebit' : debitAccount xs addr amt with
      | none => simp [hdebit'] at hdebit
      | some ys =>
        simp [hdebit'] at hdebit
        subst hdebit
        simp [noneg]
        exact ⟨hnonegx, xih ys hnonegxs hdebit'⟩
    
def creditAccount (ledger : Ledger) (addr : Addr) (amt : Amount) : Option Ledger :=
  match ledger with
  | []     => none
  | h :: t =>
    if (h.addr == addr)
    then some $ { h with bal := h.bal + amt } :: t
    else do
      let ledger' <- creditAccount t addr amt
      return (h :: ledger')

lemma creditAccount_adds_supply (ledger : Ledger) (addr : Addr) (amt : Amount) :
  ∀ ledger', ledger.creditAccount addr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply + amt := by sorry

def transferFunds (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) : Option Ledger := do
  let ledger' <- debitAccount ledger fromAddr amt
  creditAccount ledger' toAddr amt

theorem transferFunds_preserves_supply (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) :
  ∀ ledger', ledger.transferFunds fromAddr toAddr amt = some ledger'
  -> ledger'.getSupply = ledger.getSupply := by
  induction ledger with
  | nil => simp [transferFunds, debitAccount]
  | cons x xsl _ =>
    simp [transferFunds]
    cases hd : debitAccount (x :: xsl) fromAddr amt with
    | none => simp
    | some xsd =>
      simp
      cases hc : creditAccount xsd toAddr amt with
      | none => simp
      | some xsc =>
        simp
        have d := debitAccount_subtracts_supply (x :: xsl) fromAddr amt xsd
        have c := creditAccount_adds_supply xsd toAddr amt xsc
        rw [ c hc, d hd ]
        ring

lemma transferFunds_preserves_noneg (ledger : Ledger) (fromAddr toAddr : Addr) (amt : Amount) :
  ∀ ledger', ledger.noneg 
  -> ledger.transferFunds fromAddr toAddr amt = some ledger' 
  -> ledger'.noneg := by sorry

structure Proposal where
  id : Nat
  proposer : Addr
  amt : Amount
  yes : Nat
  no : Nat
  done : Bool
  deriving Repr

structure DAO where
  ledger : Ledger
  propl : List Proposal
  deriving Repr

namespace DAO

inductive Vote
  | yes
  | no
  deriving Repr

inductive Action
  | contrib (contributor : Addr) (amt : Amount)
  | propose (proposer : Addr) (amt : Amount)
  | vote (pid : Nat) (vt : Vote)
  | execute (pid : Nat)
  deriving Repr

def daoAddr : Addr := "treasury"

def contrib (dao : DAO) (contributor : Addr) (amt : Amount) : Option DAO := do
  let ledger' <- dao.ledger.transferFunds contributor daoAddr amt
  return { dao with ledger := ledger' }

def propose (dao : DAO) (proposer : Addr) (amt : Amount) : Option DAO :=
  let prop := { id := dao.propl.length + 1, proposer, amt, yes := 0, no := 0, done := false }
  return { dao with propl := prop :: dao.propl }

def vote (dao : DAO) (pid : Nat) (vt : Vote) : Option DAO :=
  let propl' := dao.propl.map (λ p =>
    if p.id != pid
    then p 
    else if p.done
    then p
    else
      match vt with
      | Vote.yes => { p with yes := p.yes + 1 }
      | Vote.no  => { p with no := p.no + 1 })
  return { dao with propl := propl' }

def execute (dao : DAO) (pid : Nat) : Option DAO := do
  let p <- dao.propl.find? (λ q => q.id == pid) 
  if p.done
  then none
  else if p.yes <= p.no
  then none
  else do
    let l' <- dao.ledger.transferFunds daoAddr p.proposer p.amt
    return { dao with
      ledger := l'
      propl := dao.propl.map (λ q => if q.id = pid then { q with done := true } else q)
    }

def contract (dao : DAO) (act : Action) : Option DAO :=
  match act with
  | Action.contrib contributor amt => dao.contrib contributor amt
  | Action.propose proposer amt    => dao.propose proposer amt
  | Action.vote pid vt            => dao.vote pid vt
  | Action.execute pid             => dao.execute pid

def run (dao : DAO) (acts : List Action) : Option DAO :=
  match acts with
  | [] => dao
  | (h :: t) => do
      let dao' <- contract dao h
      run dao' t

lemma propose_never_fails (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∃ dao', dao.contract (Action.propose proposer amt) = some dao' := ⟨_, rfl⟩

lemma vote_never_fails (dao : DAO) (pid : Nat) (vote : Vote) :
  ∃ dao', dao.contract (Action.vote pid vote) = some dao' := sorry

lemma propose_preserves_ledger (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.propose proposer amt) = some dao'
  -> dao'.ledger = dao.ledger := by
  intro dao' hStep
  simp [contract, propose] at hStep
  subst hStep
  rfl
 
lemma vote_preserves_ledger (dao : DAO) (pid : Nat) (vote : Vote) :
  ∀ dao', dao.contract (.vote pid vote) = some dao'
  -> dao'.ledger = dao.ledger := by sorry

lemma contrib_preserves_propl (dao : DAO) (contributor : Addr) (amt : Amount) :
  ∀ dao', dao.contract (.contrib contributor amt) = some dao'
  -> dao'.propl = dao.propl := by
  intro dao' hStep
  simp [contract, contrib] at hStep
  cases ht : dao.ledger.transferFunds contributor daoAddr amt with
  | none => simp [ht] at hStep
  | some _ => simp [ht] at hStep; subst hStep; rfl

def supply (dao : DAO) : Amount := dao.ledger.getSupply

lemma contrib_preserves_supply (dao : DAO) (contributor : Addr) (amt : Amount) :
  ∀ dao', dao.contract (Action.contrib contributor amt) = some dao'
  -> dao'.supply = dao.supply := by
  intro dao' hStep
  simp [contract, contrib] at hStep
  cases ht : dao.ledger.transferFunds contributor daoAddr amt with
  | none => simp [ht] at hStep
  | some l' =>
    simp [ht] at hStep
    subst hStep
    simp [supply]
    exact transferFunds_preserves_supply dao.ledger contributor daoAddr amt l' ht

lemma propose_preserves_supply (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.contract (Action.propose proposer amt) = some dao'
  -> dao'.supply = dao.supply := by sorry

lemma vote_preserves_supply (dao : DAO) (pid : Nat) (vt : Vote) :
  ∀ dao', dao.contract (Action.vote pid vt) = some dao'
  -> dao'.supply = dao.supply := by sorry

lemma execute_preserves_supply (dao : DAO) (pid : Nat) :
  ∀ dao', dao.contract (Action.execute pid) = some dao'
  -> dao'.supply = dao.supply := by sorry

theorem contract_preserves_supply (dao : DAO) (act : Action) :
  ∀ dao', dao.contract act = some dao'
  -> dao'.supply = dao.supply := by
  intro dao' hStep
  cases act with
  | contrib contributor amt => exact contrib_preserves_supply dao contributor amt dao' hStep
  | propose proposer amt => exact propose_preserves_supply dao proposer amt dao' hStep
  | vote pid vote => sorry
  | execute pid => sorry

lemma propose_increments_propl_count (dao : DAO) (proposer : Addr) (amt : Amount) :
  ∀ dao', dao.propose proposer amt = some dao'
  -> dao'.propl.length = dao.propl.length + 1 := by sorry

lemma vote_preserves_propl_count (dao : DAO) (pid : Nat) (v : Vote) :
  ∀ dao', dao.vote pid v = some dao'
  -> dao'.propl.length = dao.propl.length := by sorry

lemma execute_preserves_propl_count (dao : DAO) (pid : Nat) :
  ∀ dao', dao.execute pid = some dao'
  -> dao'.propl.length = dao.propl.length := by sorry

theorem execute_only_if_pass (dao : DAO) (pid : Nat) :
  ∀ dao', dao.contract (.execute pid) = some dao'
  -> ∃ p, dao.propl.find? (fun q => q.id == pid) = some p ∧ p.no < p.yes ∧ p.done = false := by
  intro dao' hStep
  simp [contract, execute] at hStep
  cases hFind : dao.propl.find? (λ q => q.id == pid) with
  | none => simp [hFind] at hStep
  | some p' =>
    simp [hFind] at hStep
    obtain ⟨hnotdone, hvote, _⟩ := hStep
    exact ⟨p', rfl, hvote, hnotdone⟩

theorem run_preserves_supply (daoGen : DAO) (acts : List Action) :
  ∀ (daoFinal : DAO), daoGen.run acts = some daoFinal --  better to have ∀ (daoGen daoFinal : DAO)
  -> daoFinal.supply = daoGen.supply := by
  induction acts generalizing daoGen with
  | nil =>
    intro daoFinal hRun
    simp [run] at hRun
    subst hRun
    rfl
  | cons act acts aih =>
    intro daoFinal hRun
    simp [run] at hRun
    cases hCon : daoGen.contract act with
    | none => simp [hCon] at hRun
    | some daoInter =>
      simp [hCon] at hRun
      have h1 := contract_preserves_supply daoGen act daoInter hCon
      have h2 := aih daoInter daoFinal hRun
      rw [ <- h1, h2 ]
