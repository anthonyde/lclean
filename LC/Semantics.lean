/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import LC.Relations
import LC.Subst
import LC.Syntax

open Relations Subst Syntax

namespace Semantics

variable {τ : Type}

-- Call-by-name semantics
inductive CBN : Term τ → Term τ → Prop
  | app : ∀ {t₁ t₁' t₂},
    CBN t₁ t₁' →
    CBN (.app t₁ t₂) (.app t₁' t₂)
  | abs : ∀ {T t₁ t₂},
    CBN (.app (.abs T t₁) t₂) (↑⁻¹[0 ↦ ↑¹t₂] t₁)

notation t " ⟶n " t' => CBN t t'
notation t " ⟶*n " t' => Multi CBN t t'

-- Call-by-value semantics
inductive Val : Term τ → Prop
  | a :
    Val .a
  | abs : ∀ {T t},
    Val (.abs T t)
inductive CBV : Term τ → Term τ → Prop
  | app₁ : ∀ {t₁ t₁' t₂},
    CBV t₁ t₁' →
    CBV (.app t₁ t₂) (.app t₁' t₂)
  | app₂ : ∀ {v t₂ t₂'},
    Val v →
    CBV t₂ t₂' →
    CBV (.app v t₂) (.app v t₂')
  | appabs : ∀ {T t v},
    Val v →
    CBV (.app (.abs T t) v) (↑⁻¹[0 ↦ ↑¹v] t)

notation t " ⟶v " t' => CBV t t'
notation t " ⟶*v " t' => Multi CBV t t'

-- Full β-reduction semantics
inductive Beta : Term τ → Term τ → Prop
  | abs : ∀ {T t t'},
    Beta t t' →
    Beta (.abs T t) (.abs T t')
  | app₁ : ∀ {t₁ t₁' t₂},
    Beta t₁ t₁' →
    Beta (.app t₁ t₂) (.app t₁' t₂)
  | app₂ : ∀ {t₁ t₂ t₂'},
    Beta t₂ t₂' →
    Beta (.app t₁ t₂) (.app t₁ t₂')
  | appabs : ∀ {T t₁ t₂},
    Beta (.app (.abs T t₁) t₂) (↑⁻¹[0 ↦ ↑¹t₂] t₁)

notation t " ⟶β " t' => Beta t t'
notation t " ⟶*β " t' => Multi Beta t t'

-- Takahashi1995 Def. 1.1
-- Parallel β-reduction semantics
inductive PBeta : Term τ → Term τ → Prop
  | refl : ∀ {t},
    PBeta t t
  | abs : ∀ {T t t'},
    PBeta t t' →
    PBeta (.abs T t) (.abs T t')
  | app : ∀ {t₁ t₁' t₂ t₂'},
    PBeta t₁ t₁' →
    PBeta t₂ t₂' →
    PBeta (.app t₁ t₂) (.app t₁' t₂')
  | appabs : ∀ {T t₁ t₁' t₂ t₂'},
    PBeta t₁ t₁' →
    PBeta t₂ t₂' →
    PBeta (.app (.abs T t₁) t₂) (↑⁻¹[0 ↦ ↑¹t₂'] t₁')

notation t " ⟹β " t' => PBeta t t'
notation t " ⟹*β " t' => Multi PBeta t t'

example {T : τ} : CBN (.app (.abs T (.var 0)) .a) .a := by
  exact .abs

example {T : τ} : CBV (.app (.abs T (.var 0)) .a) .a := by
  exact .appabs .a

lemma val_nf {t : Term τ} : Val t → NormalForm CBV t := by
  intro v ⟨t', ht⟩
  cases v <;> contradiction

-- SF2: Smallstep
theorem cbn_det : Deterministic (@CBN τ) := by
  intro t t₁ t₂ ht₁ ht₂
  induction ht₁ generalizing t₂ with
  | app hs₁ ih =>
    cases ht₂ with
    | app hs₁' => rw [ih hs₁']
    | abs => contradiction
  | abs => cases ht₂ <;> trivial

theorem cbv_det : Deterministic (@CBV τ) := by
  intro t t₁ t₂ ht₁ ht₂
  induction ht₁ generalizing t₂ with
  | app₁ hs₁ ih₁ =>
    cases ht₂ with
    | app₁ hs₁' => rw [ih₁ hs₁']
    | app₂ hv₁ hs₂ =>
      exfalso
      apply val_nf hv₁
      exact ⟨_, hs₁⟩
    | appabs hv₂ => contradiction
  | app₂ hv hs₂ ih₂ =>
    cases ht₂ with
    | app₁ hs₁ =>
      exfalso
      apply val_nf hv
      exact ⟨_, hs₁⟩
    | app₂ hv₁ hs₂' => rw [ih₂ hs₂']
    | appabs hv₂ =>
      exfalso
      apply val_nf hv₂
      exact ⟨_, hs₂⟩
  | appabs hv =>
    cases ht₂ with
    | app₁ hs₂ => contradiction
    | app₂ hv₂ hv' =>
      exfalso
      apply val_nf hv
      exact ⟨_, hv'⟩
    | appabs hv₂ => rfl

theorem nf_unique : Deterministic (NormalFormOf (@CBV τ)) := by
  intro t t₁ t₂ hN₁ hN₂
  obtain ⟨ht₁, hN₁⟩ := hN₁
  obtain ⟨ht₂, hN₂⟩ := hN₂
  induction ht₁ generalizing t₂ with
  | refl =>
    cases ht₂ with
    | refl => rfl
    | step hs hs' =>
      exfalso
      apply hN₁
      exact ⟨_, hs⟩
  | step hs hs' ih =>
    cases ht₂ with
    | refl =>
      exfalso
      apply hN₂
      exact ⟨_, hs⟩
    | @step _ u' _ hu hu' =>
      have := cbv_det hs hu
      subst u'
      exact ih hN₁ hu' hN₂

lemma val_halts {v : Term τ} : Val v → Halts CBV v := by
  intro hv
  exists v
  exact ⟨.refl, val_nf hv⟩

lemma multi_cbv_app₂ {v t₂ t₂' : Term τ} : Val v → (t₂ ⟶*v t₂') → .app v t₂ ⟶*v .app v t₂' := by
  intro hv ht₂
  induction ht₂ with
  | refl => exact .refl
  | step ht₂ ht₂' ih => exact .step (.app₂ hv ht₂) ih
