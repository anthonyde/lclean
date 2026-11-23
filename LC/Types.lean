/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import LC.Context
import LC.Relations
import LC.Semantics
import LC.Subst
import LC.Syntax
import Mathlib.Tactic.Linarith

open Context Mathlib Relations Semantics Subst Syntax

namespace Types

inductive Un : Type
  | u : Un

inductive Ty : Type
  | a : Ty
  | f : Ty → Ty → Ty

notation T₁ " ⤳ " T₂ => Ty.f T₁ T₂

-- Typing relation
inductive Typed : ∀ {n : Nat}, @Ctx Ty n → Term Ty → Ty → Prop
  | a : ∀ {Γ},
    Typed Γ .a .a
  | var : ∀ {Γ} k {T},
    Ctx.mem Γ k = T →
    Typed Γ (.var ↑k) T
  | abs : ∀ {Γ T₁ t T₂},
    Typed (Ctx.extend Γ T₁) t T₂ →
    Typed Γ (.abs T₁ t) (.f T₁ T₂)
  | app : ∀ {Γ T₁ t₁ T₂ t₂},
    Typed Γ t₁ (.f T₁ T₂) →
    Typed Γ t₂ T₁ →
    Typed Γ (.app t₁ t₂) T₂

notation Γ " ⊢ " t " : " T => Typed Γ t T

-- TAPL 9.3.4
lemma canon_a {t : Term Ty} : Val t → (⬝ ⊢ t : .a) → t = .a := by
  grind only [Typed, Val]

lemma canon_fn {T₁ T₂ : Ty} {t : Term Ty} : Val t → (⬝ ⊢ t : T₁ ⤳ T₂) → ∃ s, t = .abs T₁ s := by
  grind only [Typed, Val]

-- TAPL 9.3.5
theorem progress {T : Ty} {t : Term Ty} : (⬝ ⊢ t : T) → Val t ∨ (∃ t', t ⟶v t') := by
  intro hT
  induction t generalizing T with
  | a =>
    left
    exact .a
  | var k =>
    cases hT with
    | var hT => grind only
  | abs T t ih =>
    left
    exact .abs
  | app t₁ t₂ ih₁ ih₂ =>
    right
    cases hT with
    | app hT₁ hT₂ =>
      cases ih₁ hT₁ with
      | inl hv₁ =>
        cases ih₂ hT₂ with
        | inl hv₂ =>
          obtain ⟨t', rfl⟩ := canon_fn hv₁ hT₁
          exact ⟨_, .appabs hv₂⟩
        | inr ht₂ =>
          obtain ⟨t₂', ht₂⟩ := ht₂
          exact ⟨_, .app₂ hv₁ ht₂⟩
      | inr ht₁ =>
        obtain ⟨t₁', ht₁⟩ := ht₁
        exact ⟨_, .app₁ ht₁⟩

lemma nf_val {T : Ty} {t : Term Ty} : (⬝ ⊢ t : T) → NormalForm CBV t → Val t := by
  grind only [NormalForm, Typed, progress]

-- A context with an insertion types a term shifted s.t. there is a hole at the inserted index.
theorem weakening {n : Nat} {Γ : Ctx n} {T T' : Ty} {t : Term Ty} {c : Fin n.succ} :
    (Γ ⊢ t : T) → ([Γ << T'] c) ⊢ shift ↑c t : T := by
  intro hT
  induction t generalizing n Γ T with
  | a =>
    cases hT with
    | a => exact .a
  | var k =>
    cases hT with
    | var k hT =>
      cases c using Fin.cases with
      | zero =>
        rw [insert_zero]
        exact .var k.succ hT
      | succ c =>
        dsimp [shift]
        split
        case' var.var.succ.isTrue =>
          apply Typed.var k.castSucc
          rw [insert_mem_below]
        case' var.var.succ.isFalse h =>
          rw [not_lt] at h
          apply Typed.var k.succ
          rw [insert_mem_above]
        all_goals
          assumption
  | abs T₁ t ih =>
    cases hT with
    | abs hT₂ =>
      apply Typed.abs
      rw [← insert_succ]
      exact ih hT₂
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT with
    | app hT₁ hT₂ => exact .app (ih₁ hT₁) (ih₂ hT₂)

lemma shift_closed' {n : Nat} {Γ : Ctx n} {T : Ty} {t : Term Ty} {c : Nat} :
    n ≤ c → (Γ ⊢ t : T) → shift c t = t := by
  induction t generalizing n T c <;> grind only [Typed, shift]

lemma shift_closed {T : Ty} {t : Term Ty} : (⬝ ⊢ t : T) → (↑¹t) = t :=
  shift_closed' (by linarith)

lemma unshift_closed' {n : Nat} {Γ : Ctx n} {T : Ty} {t : Term Ty} {c : Nat} :
    n ≤ c → (Γ ⊢ t : T) → unshift c t = t := by
  induction t generalizing n T c <;> grind only [Typed, unshift]

lemma unshift_closed {T : Ty} {t : Term Ty} : (⬝ ⊢ t : T) → (↑⁻¹t) = t :=
  unshift_closed' (by linarith)

lemma sub_closed' {n j : Nat} {Γ : Ctx n} {T : Ty} {t s : Term Ty} :
    n ≤ j → (Γ ⊢ t : T) → ([j ↦ s] t) = t := by
  induction t generalizing n j T s <;> grind only [Typed, sub]

lemma sub_closed {T : Ty} {t s : Term Ty} {j : Nat} : (⬝ ⊢ t : T) → ([j ↦ s] t) = t :=
  sub_closed' (by linarith)

lemma weakening_closed {n : Nat} {Γ : Ctx n} {T : Ty} {t : Term Ty} :
    (⬝ ⊢ t : T) → (Γ ⊢ t : T) := by
  intro hT
  induction Γ with
  | empty => exact hT
  | extend Γ' T' ih =>
    rw [← insert_zero, ← shift_closed hT]
    exact weakening ih

example : ⬝.extend .a ⊢ .var 0 : .a := by
  apply Typed.var 0
  rfl

example : [(⬝.extend .a) << (.f .a .a)] 0 ⊢ ↑¹(.var 0) : .a := by
  apply weakening
  apply Typed.var 0
  rfl

lemma β_pres' {n : Nat} {Γ : Ctx n} {T T' : Ty} {t t' : Term Ty} {c : Fin (n + 1)} :
    (Γ ⊢ t : T) → (Γ.insert T c ⊢ t' : T') → Γ ⊢ unshift c (sub c (shift c t) t') : T' := by
  intro hT hT'
  induction t' generalizing n t T' with
  | a =>
    cases hT' with
    | a => exact .a
  | var k =>
    cases hT' with
    | var k hT' =>
      dsimp [sub]
      subst T'
      split
      case var.var.isTrue h =>
        rw [Fin.val_eq_val] at h
        subst k
        rw [shift_unshift, insert_mem]
        exact hT
      case var.var.isFalse =>
        dsimp [unshift]
        split
        case isTrue h =>
          apply Typed.var (k.castLT (by omega))
          rw [← insert_mem_below, Fin.castSucc_castLT]
          exact h
        case isFalse =>
          have hk : k ≠ 0 := by
            intro hc
            simp_all only [Fin.le_zero_iff, Fin.val_fin_lt, not_lt, not_true_eq_false]
          apply Typed.var (k.pred hk)
          rw [← insert_mem_above, Fin.succ_pred]
          rw [Fin.le_castSucc_iff, Fin.succ_pred]
          omega
  | abs T₁ s ih =>
    cases hT' with
    | abs hT₂ =>
      apply Typed.abs
      rw [← Fin.val_succ, shift_comm]
      · apply ih
        · rw [← insert_zero]
          exact weakening hT
        · exact hT₂
      · linarith
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT' with
    | app hT' hT₂ => exact .app (ih₁ hT hT') (ih₂ hT hT₂)

-- TAPL 9.3.8
lemma β_pres {n : Nat} {Γ : Ctx n} {T T' : Ty} {t t' : Term Ty} :
    (Γ ⊢ t : T) → (Γ.extend T ⊢ t' : T') → Γ ⊢ β t' t : T' := by
  rw [← insert_zero]
  exact β_pres'

-- TAPL 9.3.9
theorem preservation {T : Ty} {t t' : Term Ty} : (⬝ ⊢ t : T) → (t ⟶v t') → ⬝ ⊢ t' : T := by
  intro hT hs
  induction hs generalizing T with
  | app₁ ht₁ ih₁ =>
    cases hT with
    | app hT₁ hT₂ => exact .app (ih₁ hT₁) hT₂
  | app₂ hv ht₂ ih₂ =>
    cases hT with
    | app hT₁ hT₂ => exact .app hT₁ (ih₂ hT₂)
  | appabs hv =>
    cases hT with
    | app hT₁ hT₂ =>
      cases hT₁ with
      | abs hT => exact β_pres hT₂ hT

lemma nf_pres {T : Ty} {t t' : Term Ty} : (⬝ ⊢ t : T) → NormalFormOf CBV t t' → (⬝ ⊢ t' : T) := by
  intro hT hN
  obtain ⟨ht, hN⟩ := hN
  induction ht with
  | refl => exact hT
  | step hs₁ hs₂ ih => exact ih (preservation hT hs₁) hN

lemma halts_val {T : Ty} {t t' : Term Ty} :
    (⬝ ⊢ t : T) → Halts CBV t → NormalFormOf CBV t t' → Val t' := by
  intro hT hH hN
  have hT' := nf_pres hT hN
  obtain ⟨ht, hN⟩ := hN
  exact nf_val hT' hN
