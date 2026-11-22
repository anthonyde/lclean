/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import Mathlib

namespace Relations

variable {α : Type}

-- SF2: Smallstep
inductive Multi (R : α → α → Prop) : α → α → Prop
  | refl : ∀ {x},
    Multi R x x
  | step : ∀ {x y z},
    R x y →
    Multi R y z →
    Multi R x z

theorem multi_closed {R : α → α → Prop} {x y : α} : R x y → Multi R x y := by
  intro hR
  exact .step hR .refl

theorem multi_trans {R : α → α → Prop} : Transitive (Multi R) := by
  intro x y z hx hy
  induction hx with
  | refl => exact hy
  | step hx hy ih => exact .step hx (ih hy)

def Deterministic (R : α → α → Prop) : Prop :=
  ∀ {t t₁ t₂}, R t t₁ → R t t₂ → t₁ = t₂

def NormalForm (R : α → α → Prop) (t : α) : Prop :=
  ¬(∃ t', R t t')

def NormalFormOf (R : α → α → Prop) (t t' : α) : Prop :=
  Multi R t t' ∧ NormalForm R t'

-- SF2: Norm
def Halts (R : α → α → Prop) (t : α) : Prop :=
  ∃ t', NormalFormOf R t t'
