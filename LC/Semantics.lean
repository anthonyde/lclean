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

lemma multi_beta_abs {T : τ} {t t' : Term τ} : (t ⟶*β t') → .abs T t ⟶*β .abs T t' := by
  intro ht
  induction ht with
  | refl => exact .refl
  | step ht ht' ih => exact .step (.abs ht) ih

lemma multi_beta_app₁ {t₁ t₁' t₂ : Term τ} : (t₁ ⟶*β t₁') → .app t₁ t₂ ⟶*β .app t₁' t₂ := by
  intro ht₁
  induction ht₁ with
  | refl => exact .refl
  | step ht₁ ht₁' ih => exact .step (.app₁ ht₁) ih

lemma multi_beta_app₂ {t₁ t₂ t₂' : Term τ} : (t₂ ⟶*β t₂') → .app t₁ t₂ ⟶*β .app t₁ t₂' := by
  intro ht₂
  induction ht₂ with
  | refl => exact .refl
  | step ht₂ ht₂' ih => exact .step (.app₂ ht₂) ih

lemma pbeta_abs_inv {T : τ} {t t' : Term τ} : (.abs T t ⟹β .abs T t') → t ⟹β t' := by
  intro ht
  cases ht with
  | refl => exact .refl
  | abs ht => exact ht

lemma pbeta_abs_inv₁ {T : τ} {t₁ t' : Term τ} :
    (.abs T t₁ ⟹β t') → ∃ t₁', t' = .abs T t₁' ∧ t₁ ⟹β t₁' := by
  intro ht
  cases ht with
  | refl => exact ⟨_, rfl, .refl⟩
  | abs ht₁ => exact ⟨_, rfl, ht₁⟩

-- Takahashi1995 §1 (1)
lemma pbeta_closed {t t' : Term τ} : (t ⟶β t') → t ⟹β t' := by
  intro ht
  induction ht with
  | abs T ht => exact .abs ht
  | app₁ ht₁ ih => exact .app ih .refl
  | app₂ ht₂ ih => exact .app .refl ih
  | appabs => exact .appabs .refl .refl

-- Takahashi1995 §1 (2)
lemma multi_beta_closed {t t' : Term τ} : (t ⟹β t') → t ⟶*β t' := by
  intro ht
  induction t generalizing t' with
  | a =>
    cases ht
    exact .refl
  | var k =>
    cases ht
    exact .refl
  | abs T t ih =>
    cases ht with
    | refl => exact .refl
    | abs ht => exact multi_beta_abs (ih ht)
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht with
    | refl => exact .refl
    | app ht₁ ht₂ => exact multi_trans (multi_beta_app₁ (ih₁ ht₁)) (multi_beta_app₂ (ih₂ ht₂))
    | appabs ht₁ ht₂ =>
      exact multi_trans (multi_beta_app₁ (ih₁ (.abs ht₁))) (multi_trans (multi_beta_app₂ (ih₂ ht₂))
        (multi_closed .appabs))

lemma pbeta_free_pres {t t' : Term τ} {j : Nat} : (t ⟹β t') → ¬fv t j → ¬fv t' j := by
  intro ht hf
  induction ht generalizing j with
  | refl => exact hf
  | abs ht ih => grind only [fv]
  | app ht₁ ht₂ ih₁ ih₂ => grind only [fv]
  | appabs ht₁ ht₂ ih₁ ih₂ =>
    rw [fv, not_or] at hf
    obtain ⟨hf₁, hf₂⟩ := hf
    exact β_pres_not_fv (ih₂ hf₂) (ih₁ hf₁)

lemma pbeta_shift {c : Nat} {t t' : Term τ} : (t ⟹β t') → shift c t ⟹β shift c t' := by
  intro ht
  induction ht generalizing c with
  | refl => exact .refl
  | abs T ih => exact .abs ih
  | app ht₁ ht₂ ih₁ ih₂ => exact .app ih₁ ih₂
  | appabs ht₁ ht₂ ih₁ ih₂ =>
    rw [β_shift_comm]
    exact .appabs ih₁ ih₂

lemma pbeta_unshift {t t' : Term τ} {c : Nat} :
    ¬fv t c → (t ⟹β t') → unshift c t ⟹β unshift c t' := by
  intro hf ht
  induction ht generalizing c with
  | refl => exact .refl
  | abs ht ih => exact .abs (ih hf)
  | app ht₁ ht₂ ih₁ ih₂ =>
    rw [fv, not_or] at hf
    obtain ⟨hf₁, hf₂⟩ := hf
    exact .app (ih₁ hf₁) (ih₂ hf₂)
  | appabs ht₁ ht₂ ih₁ ih₂ =>
    rw [fv, not_or] at hf
    obtain ⟨hf₁, hf₂⟩ := hf
    rw [β_unshift_comm]
    · exact .appabs (ih₁ hf₁) (ih₂ hf₂)
    · exact pbeta_free_pres ht₂ hf₂
    · exact pbeta_free_pres ht₁ hf₁

lemma pbeta_sub {t t' s s' : Term τ} {j : Nat} :
    (t ⟹β t') → (s ⟹β s') → ([j ↦ s] t) ⟹β [j ↦ s'] t' := by
  intro ht hs
  induction t generalizing t' s s' j with
  | a =>
    cases ht
    exact .refl
  | var k =>
    cases ht
    dsimp [sub]
    split
    · exact hs
    · exact .refl
  | abs T t₁ ih =>
    cases ht with
    | refl => exact .abs (ih .refl (pbeta_shift hs))
    | abs ht₁ => exact .abs (ih ht₁ (pbeta_shift hs))
  | app t₁ t₂ ih₁ ih₂ =>
    cases ht with
    | refl => exact .app (ih₁ .refl hs) (ih₂ .refl hs)
    | app ht₁ ht₂ => exact .app (ih₁ ht₁ hs) (ih₂ ht₂ hs)
    | appabs ht₁ ht₂ =>
      rw [β_sub_comm]
      exact .appabs (pbeta_abs_inv (ih₁ (.abs ht₁) hs)) (ih₂ ht₂ hs)

-- Takahashi1995 §1 (3)
lemma pbeta_β {t t' s s' : Term τ} :
    (t ⟹β t') → (s ⟹β s') → (↑⁻¹[0 ↦ ↑¹s] t) ⟹β ↑⁻¹[0 ↦ ↑¹s'] t' := by
  intro ht hs
  exact pbeta_unshift (sub_pres_not_fv shift_not_fv) (pbeta_sub ht (pbeta_shift hs))

lemma pbeta_appabs_inv {T : τ} {t₁ t₂ t' : Term τ} :
    (.app (.abs T t₁) t₂ ⟹β t') →
    ∃ t₁' t₂', (t₁ ⟹β t₁') ∧ (t₂ ⟹β t₂') ∧ (t' = .app (.abs T t₁') t₂' ∨ t' = ↑⁻¹[0 ↦ ↑¹t₂'] t₁') := by
  intro ht
  cases ht with
  | refl => exact ⟨_, _, .refl, .refl, .inl rfl⟩
  | app ht ht₂ =>
    obtain ⟨t₁', rfl, ht₁⟩ := pbeta_abs_inv₁ ht
    exact ⟨_, _, ht₁, ht₂, .inl rfl⟩
  | appabs ht₁ ht₂ => exact ⟨_, _, ht₁, ht₂, .inr rfl⟩

-- Takahashi1995 §1 (5)
def star : Term τ → Term τ
  | .a => .a
  | .var k => .var k
  | .abs T t => .abs T (star t)
  | .app (.abs _ t₁) t₂ => ↑⁻¹[0 ↦ ↑¹(star t₂)] (star t₁)
  | .app t₁ t₂ => .app (star t₁) (star t₂)
theorem pbeta_star {t t' : Term τ} : (t ⟹β t') → t' ⟹β star t := by
  intro ht
  induction t generalizing t' with
  | a
  | var k =>
    cases ht
    exact .refl
  | abs T t₁ ih =>
    obtain ⟨t₁', rfl, ht₁⟩ := pbeta_abs_inv₁ ht
    exact .abs (ih ht₁)
  | app t₁ t₂ ih₁ ih₂ =>
    cases t₁ with
    | a
    | var
    | app =>
      cases ht with
      | refl => exact .app (ih₁ .refl) (ih₂ .refl)
      | app ht₁ ht₂ => exact .app (ih₁ ht₁) (ih₂ ht₂)
    | abs T t₁ =>
      obtain ⟨t₁', t₂', ht₁', ht₂', ht'⟩ := pbeta_appabs_inv ht
      have ht₁'' := pbeta_abs_inv (ih₁ (.abs ht₁'))
      cases ht' <;> subst t'
      · exact .appabs ht₁'' (ih₂ ht₂')
      · exact pbeta_β ht₁'' (ih₂ ht₂')

-- Takahashi1995 §1 (4)
theorem pbeta_diamond : Diamond (@PBeta τ) := by
  intro t s₁ s₂ ht₁ ht₂
  exact ⟨_, pbeta_star ht₁, pbeta_star ht₂⟩

-- PLFA: Confluence
lemma pbeta_strip {t s s' : Term τ} : (t ⟹β s) → (t ⟹*β s') → ∃ t', (s ⟹*β t') ∧ s' ⟹β t' := by
  intro ht ht'
  induction ht' generalizing s with
  | refl => exact ⟨_, .refl, ht⟩
  | step hs hs' ih =>
    obtain ⟨t', ht', ht''⟩ := ih (pbeta_star hs)
    exact ⟨_, .step (pbeta_star ht) ht', ht''⟩

lemma multi_pbeta_diamond : Diamond (Multi (@PBeta τ)) := by
  intro t s₁ s₂ ht₁ ht₂
  induction ht₁ generalizing s₂ with
  | refl => exact ⟨_, ht₂, .refl⟩
  | step ht₁ ht₁' ih =>
    obtain ⟨t', hs₁, hs₂⟩ := pbeta_strip ht₁ ht₂
    obtain ⟨t'', hs₁', hs₂'⟩ := ih hs₁
    exact ⟨_, hs₁', .step hs₂ hs₂'⟩

lemma multi_pbeta_closed {t t' : Term τ} : (t ⟶*β t') → t ⟹*β t' := by
  intro ht
  induction ht with
  | refl => exact .refl
  | step ht ht' ih => exact .step (pbeta_closed ht) ih

lemma multi_beta_closed' {t t' : Term τ} : (t ⟹*β t') → t ⟶*β t' := by
  intro ht
  induction ht with
  | refl => exact .refl
  | step ht ht' ih => exact multi_trans (multi_beta_closed ht) ih

theorem church_rosser : Diamond (Multi (@Beta τ)) := by
  intro t s₁ s₂ ht₁ ht₂
  obtain ⟨t', ht₁', ht₂'⟩ := multi_pbeta_diamond (multi_pbeta_closed ht₁) (multi_pbeta_closed ht₂)
  exact ⟨_, multi_beta_closed' ht₁', multi_beta_closed' ht₂'⟩
