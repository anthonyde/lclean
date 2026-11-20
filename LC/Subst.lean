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

-- β-reduction
theorem β_shift_comm {t s : Term τ} {c : Nat} :
    shift c (↑⁻¹[0 ↦ ↑¹s] t) = ↑⁻¹[0 ↦ ↑¹(shift c s)] (shift (c + 1) t) := by
  generalize hc' : 0 = c'
  have hc : c' ≤ c := by omega
  revert hc
  clear hc'
  induction t generalizing s c c' <;> grind only [shift, shift_comm, shift_unshift, sub, unshift]

theorem β_sub_comm {t s₁ s₂ : Term τ} {j : Nat} :
    [j ↦ s₂] (↑⁻¹[0 ↦ ↑¹s₁] t) = ↑⁻¹[0 ↦ ↑¹[j ↦ s₂] s₁] ([j + 1 ↦ ↑¹s₂] t) := by
  generalize hc : 0 = c
  have hj : c ≤ j := by omega
  revert hj
  clear hc
  induction t generalizing j c s₁ s₂ <;>
    grind only [shift_comm, shift_sub, shift_unshift, sub, sub_shift_comm, unshift]
