/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import LC.Context
import LC.Subst
import LC.Syntax

open Context Subst Syntax

namespace Multi

variable {τ : Type}

-- SF2: Norm
def msub (j : Nat) (σ : List (Term τ)) (t : Term τ) : Term τ :=
  match σ with
  | [] => t
  | v :: σ' => [j ↦ v] (msub (j + 1) σ' t)

def mbuild (Δ : List τ) : @Ctx τ Δ.length :=
  match Δ with
  | [] => .empty
  | T :: Δ' => (mbuild Δ').extend T

def mcat {n m : Nat} (Γ : @Ctx τ n) : @Ctx τ m → @Ctx τ (n + m)
  | ⬝ => Γ
  | Ctx.extend Γ' T => (mcat Γ Γ').extend T

def mextend {n : Nat} (Δ : List τ) : @Ctx τ n → @Ctx τ (Δ.length + n) :=
  mcat (mbuild Δ)

lemma mbuild_mem {Δ : List τ} {i : Fin Δ.length} : (mbuild Δ).mem i = Δ[i] := by
  induction Δ with
  | nil => exact Fin.elim0 i
  | cons T Δ' ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i' => exact ih

lemma mcat_mem {n m : Nat} {Γ₁ : @Ctx τ n} {Γ₂ : @Ctx τ m} {i : Fin (n + m)} :
    (mcat Γ₁ Γ₂).mem i =
    if h : m ≤ i then Γ₁.mem (i.subNat m (by linarith)) else Γ₂.mem (i.castLT (by linarith)) := by
  induction Γ₂ with
  | empty =>
    rw [dite_cond_eq_true (by grind only)]
    rfl
  | @extend n' Γ₂' T ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i' =>
      rw [mcat, extend_mem_succ, ih]
      split <;> split
      case extend.succ.isTrue.isTrue =>
        congr 1
        ext
        simp_all only [Fin.coe_subNat, Fin.val_succ]
        omega
      case extend.succ.isFalse.isFalse => rfl
      all_goals
        next h =>
          rw [Fin.val_succ] at h
          linarith

lemma mextend_mem {Δ : List τ} {n : Nat} {Γ : Ctx n} {i : Fin (Δ.length + n)} :
    (mextend Δ Γ).mem i =
    if h : n ≤ i then Δ[i - n]'(by grind only) else Γ.mem (i.castLT (by linarith)) := by
  induction Δ with
  | nil =>
    split
    · grind only [= List.length_nil]
    · induction Γ with
      | empty => rfl
      | extend Γ' T ih =>
        induction i using Fin.cases with
        | zero => rfl
        | succ i' =>
          apply ih
          simp_all only [Fin.val_succ]
          linarith
  | cons T Δ' ih =>
    rw [mextend, mcat_mem]
    split
    · rw [mbuild_mem]
      rfl
    · rfl

lemma mextend_nil : mextend (@List.nil τ) ⬝ = ⬝ := rfl

lemma mextend_cons {Δ : List τ} {T : τ} : mextend (T :: Δ) ⬝ = (mextend Δ ⬝).extend T := rfl

lemma mextend_extend {Δ : List τ} {n : Nat} {Γ : Ctx n} {T : τ} :
    (mextend Δ Γ).extend T = mextend Δ (Γ.extend T) := rfl
