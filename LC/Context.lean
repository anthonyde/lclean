/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import Mathlib.Tactic.Linarith

open Mathlib

namespace Context

variable {τ : Type}

-- Typing contexts
inductive Ctx : Nat → Type
  | empty :
    Ctx 0
  | extend {n : Nat} (Γ : Ctx n) (T : τ) :
    Ctx (n + 1)

def Ctx.mem {n : Nat} : @Ctx τ n → Fin n → τ
  | extend _ T, ⟨0, _⟩ => T
  | extend Γ _, ⟨k + 1, _⟩ => Γ.mem ⟨k, by linarith⟩

def Ctx.insert {n : Nat} (Γ : @Ctx τ n) (T : τ) : Fin (n + 1) → @Ctx τ (n + 1)
  | 0 => Γ.extend T
  | ⟨i + 1, _⟩ =>
    match Γ with
    | extend Γ' T' => (Γ'.insert T ⟨i, by linarith⟩).extend T'

notation "⬝" => Ctx.empty
notation "[" Γ " << " T "]" => Ctx.insert Γ T

lemma extend_mem_succ {n : Nat} {Γ : Ctx n} {T : τ} {i : Fin n} :
    (Γ.extend T).mem i.succ = Γ.mem i := rfl

lemma insert_zero {n : Nat} {Γ : Ctx n} {T : τ} : ([Γ << T] 0) = Γ.extend T := by
  cases Γ <;> rfl

lemma insert_succ {n : Nat} {Γ : Ctx n} {T T' : τ} {c : Fin (n + 1)} :
    [Γ.extend T << T'] c.succ = ([Γ << T'] c).extend T := rfl

-- Looking up the insertion index gives the inserted type
lemma insert_mem {n : Nat} (Γ : Ctx n) {T : τ} {i : Fin (n + 1)} : ([Γ << T] i).mem i = T := by
  induction Γ with
  | empty =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
  | extend Γ' T' ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i => exact ih

-- Looking up an index below the insertion index gives the underlying type
lemma insert_mem_below {n : Nat} {Γ : Ctx n} {T : τ} {i : Fin (n + 1)} {j : Fin n} :
    j.castSucc < i → ([Γ << T] i).mem j.castSucc = Γ.mem j := by
  intro h
  induction Γ with
  | empty => exact Fin.elim0 j
  | extend Γ' T' ih =>
    cases i using Fin.cases with
    | zero => contradiction
    | succ i =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        rw [Fin.castSucc_fin_succ, Fin.succ_lt_succ_iff] at h
        exact ih h

-- Looking up an index above the insertion index gives the underlying type
lemma insert_mem_above {n : Nat} {Γ : Ctx n} {T : τ} {i : Fin (n + 1)} {j : Fin n} :
    i ≤ j.castSucc → ([Γ << T] i).mem j.succ = Γ.mem j := by
  intro h
  induction Γ with
  | empty => exact Fin.elim0 j
  | extend Γ' T' ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      cases j using Fin.cases with
      | zero => contradiction
      | succ j =>
        rw [Fin.castSucc_fin_succ, Fin.succ_le_succ_iff] at h
        exact ih h
