/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import LC.Syntax

open Syntax

namespace Subst

variable {τ : Type}

-- Substitution
-- TAPL 6.2.1
def shift (c : Nat) : Term τ → Term τ
  | .a => .a
  | .var k => .var (if k < c then k else k + 1)
  | .abs T t => .abs T (shift (c + 1) t)
  | .app t₁ t₂ => .app (shift c t₁) (shift c t₂)
def unshift (c : Nat) : Term τ → Term τ
  | .a => .a
  | .var k => .var (if k < c then k else k - 1)
  | .abs T t => .abs T (unshift (c + 1) t)
  | .app t₁ t₂ => .app (unshift c t₁) (unshift c t₂)

notation "↑¹" t => shift 0 t
notation "↑⁻¹" t => unshift 0 t

theorem shift_comm {t : Term τ} {c₁ c₂ : Nat} :
    c₁ ≤ c₂ → shift c₁ (shift c₂ t) = shift (c₂ + 1) (shift c₁ t) := by
  induction t generalizing c₁ c₂ <;> grind only [shift]

theorem shift_unshift {t : Term τ} (c : Nat) : unshift c (shift c t) = t := by
  induction t generalizing c <;> grind only [shift, unshift]

theorem unshift_comm {t : Term τ} {c₁ c₂ : Nat} :
    c₁ ≤ c₂ → unshift c₂ (unshift c₁ t) = unshift c₁ (unshift (c₂ + 1) t) := by
  induction t generalizing c₁ c₂ <;> grind only [unshift]

-- TAPL 6.2.4
def sub (j : Nat) (s : Term τ) : Term τ → Term τ
  | .a => .a
  | .var k => if k = j then s else .var k
  | .abs T t => .abs T (sub (j + 1) (↑¹s) t)
  | .app t₁ t₂ => .app (sub j s t₁) (sub j s t₂)

notation "[" j " ↦ " s "]" => sub j s

theorem shift_sub {t s : Term τ} {c : Nat} : sub c s (shift c t) = shift c t := by
  induction t generalizing s c <;> grind only [shift, sub]

theorem sub_shift_comm {t s : Term τ} {c j : Nat} :
    c ≤ j → shift c ([j ↦ s] t) = [j + 1 ↦ shift c s] (shift c t) := by
  induction t generalizing s c j <;> grind only [shift, shift_comm, sub]

-- Free variables of a term
def fv : Term τ → Nat → Prop
  | .a, _ => False
  | .var k, j => j = k
  | .abs _ t, j => fv t (j + 1)
  | .app t₁ t₂, j => fv t₁ j ∨ fv t₂ j

theorem shift_not_fv {t : Term τ} {c : Nat} : ¬fv (shift c t) c := by
  induction t generalizing c <;> grind only [fv, shift]

theorem shift_pres_not_fv {t : Term τ} {c j : Nat} (hf : ¬fv t j) :
    c ≤ j → ¬fv (shift c t) (j + 1) := by
  induction t generalizing c j <;> grind only [fv, shift]

theorem unshift_pres_not_fv {t : Term τ} {c j : Nat} (hf : ¬fv t c) (hf' : ¬fv t (j + 1)) :
    c ≤ j → ¬fv (unshift c t) j := by
  induction t generalizing c j <;> grind only [fv, unshift]

theorem sub_pres_not_fv {t s : Term τ} {j : Nat} (hf : ¬fv s j) : ¬fv ([j ↦ s] t) j := by
  induction t generalizing s j <;> grind only [fv, shift_pres_not_fv, sub]

theorem sub_pres_not_fv_ne {t s : Term τ} {j k : Nat} (hf : ¬fv s k) (hf' : ¬fv t k) :
    j ≠ k → ¬fv ([j ↦ s] t) k := by
  induction t generalizing s j k <;> grind only [fv, shift_pres_not_fv, sub]

theorem shift_unshift_comm {t : Term τ} {c₁ c₂ : Nat} (hf : ¬fv t c₂) :
    c₁ ≤ c₂ → unshift (c₂ + 1) (shift c₁ t) = shift c₁ (unshift c₂ t) := by
  induction t generalizing c₁ c₂ <;> grind only [fv, shift, unshift]

theorem sub_unshift_comm {t s : Term τ} {c j : Nat} (hf : ¬fv s c) (hf' : ¬fv t c) :
    j < c → unshift c ([j ↦ s] t) = [j ↦ unshift c s] (unshift c t) := by
  induction t generalizing s c j <;>
    grind only [fv, shift_pres_not_fv, shift_unshift_comm, sub, unshift]

-- β-reduction
abbrev β (t s : Term τ) : Term τ := ↑⁻¹[0 ↦ ↑¹s] t

theorem β_pres_not_fv {t s : Term τ} {j : Nat} (hf : ¬fv s j) (hf' : ¬fv t (j + 1)) :
    ¬fv (β t s) j := by
  apply unshift_pres_not_fv (sub_pres_not_fv shift_not_fv)
    (sub_pres_not_fv_ne (shift_pres_not_fv hf _) hf' _) <;> omega

theorem β_shift_comm {t s : Term τ} {c : Nat} :
    shift c (β t s) = β (shift (c + 1) t) (shift c s) := by
  unfold β
  generalize hc' : 0 = c'
  have hc : c' ≤ c := by omega
  revert hc
  clear hc'
  induction t generalizing s c c' <;> grind only [shift, shift_comm, shift_unshift, sub, unshift]

theorem β_unshift_comm {t s : Term τ} {c : Nat} (hf : ¬fv s c) (hf' : ¬fv t (c + 1)) :
    unshift c (β t s) = β (unshift (c + 1) t) (unshift c s) := by
  grind only [shift_pres_not_fv, shift_unshift_comm, sub_unshift_comm, unshift_comm]

theorem β_sub_comm {t s₁ s₂ : Term τ} {j : Nat} :
    [j ↦ s₂] (β t s₁) = β ([j + 1 ↦ ↑¹s₂] t) ([j ↦ s₂] s₁) := by
  unfold β
  generalize hc : 0 = c
  have hj : c ≤ j := by omega
  revert hj
  clear hc
  induction t generalizing j c s₁ s₂ <;>
    grind only [shift_comm, shift_sub, shift_unshift, sub, sub_shift_comm, unshift]
