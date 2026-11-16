/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

namespace Syntax

-- Nameless STLC using de Bruijn indices
inductive Term (τ : Type) : Type
  | a : Term τ
  | var : Nat → Term τ
  | abs : τ → Term τ → Term τ
  | app : Term τ → Term τ → Term τ

notation "λ" T ". " t => Term.abs T t
notation "(" t₁ t₂ ")" => Term.app t₁ t₂
