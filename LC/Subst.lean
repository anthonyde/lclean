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

-- TAPL 6.2.4
def sub (j : Nat) (s : Term τ) : Term τ → Term τ
  | .a => .a
  | .var k => if k = j then s else .var k
  | .abs T t => .abs T (sub (j + 1) (↑¹s) t)
  | .app t₁ t₂ => .app (sub j s t₁) (sub j s t₂)

notation "[" j " ↦ " s "]" => sub j s
