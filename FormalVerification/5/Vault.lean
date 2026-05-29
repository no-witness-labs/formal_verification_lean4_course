import Mathlib.Tactic
import Blaster

abbrev Amount := Int

-- State
structure Vault where
  password : String
  locked   : Bool
  amount   : Amount
  deriving Repr

inductive Action where
  | deposit : Int -> Action
  | claim : String -> Action
  deriving Repr

open Action

def contract (s : Vault) (a : Action) : Option Vault :=
  match a with
  | deposit n =>
    if n >= 0
    then some { password := s.password, locked := s.locked, amount := s.amount + n }
    else none
  | claim pw =>
      if pw = s.password then
        if s.locked then some { password := s.password, locked := false, amount := 0 }
        else none
      else none

def initial : Vault := { password := "secret", locked := true, amount := 100 }

def claimed : Vault := { password := "secret", locked := false, amount := 0 }

-- funds locked are always positive
def Valid (s : Vault) : Prop := s.amount >= 0

-- if vault is NOT locked, then there are NO funds inside
def Consistent (s : Vault) : Prop := s.locked = false -> s.amount = 0

-- tests (sanity checks)
theorem deposit_works :
  contract initial (deposit 10) = some { password := "secret", locked := true, amount := 110 } := by
  rfl

theorem password_claims : contract initial (claim "secret") = some claimed := by rfl

-- theorems
theorem deposit_preserves_validity : Valid s -> contract s (deposit n) = some s' -> Valid s' := by
  intro hValid hStep
  unfold contract at hStep
  unfold Valid at *
  by_cases h : n >= 0
  · simp [h] at hStep
    blaster
  · simp [h] at hStep

theorem deposit_preserves_consistency : Consistent s -> contract s (deposit n) = some s' -> Consistent s' := by sorry

theorem claim_preserves_consistency : contract s (claim pw) = some s' -> Consistent s' := by
  intro hStep
  unfold Consistent
  intro hUnlocked
  unfold contract at hStep
  by_cases hPw : pw = s.password
  · simp [hPw] at hStep
    by_cases hLocked : s.locked
    · simp [hLocked] at hStep
      blaster
    · simp [hLocked] at hStep
  · simp [hPw] at hStep

theorem claim_preserves_validity : Valid s -> contract s (claim p) = some s' -> Valid s' := by sorry

theorem contract_preserves_invariants :
  Valid s ->
  Consistent s ->
  contract s a = some s' ->
  Valid s' /\ Consistent s' := by
  intro hv hc hs
  cases a with
  | deposit n => sorry
  | claim pw => sorry

theorem successful_claim_empties : contract s (claim pw) = some s' -> s'.amount = 0 := by
  intro h
  unfold contract at h
  by_cases hPw : pw = s.password
  · simp [hPw] at h
    by_cases hLocked : s.locked
    · simp [hLocked] at h
      blaster
    · simp [hLocked] at h
  · simp [hPw] at h

theorem successful_claim_unlocks : contract s (claim pw) = some s' -> s'.locked = false := by sorry
