/-
Copyright (C) 2026 Anthony DeRossi
SPDX-License-Identifier: Apache-2.0
Authors: Anthony DeRossi
-/

import LC.Context
import LC.Multi
import LC.Relations
import LC.Semantics
import LC.Subst
import LC.Syntax
import LC.Types
import Mathlib.Tactic.Linarith

open Context Mathlib Multi Relations Semantics Subst Syntax Types

namespace Norm

-- SF2: Norm
def R (T : Ty) (t : Term Ty) : Prop :=
  (⬝ ⊢ t : T) ∧
  Halts CBV t ∧
  match T with
  | .a => True
  | .f T₁ T₂ => ∀ s, R T₁ s → R T₂ (.app t s)

-- TAPL 12.1.3
lemma R_halts {T : Ty} {t : Term Ty} : R T t → Halts CBV t := by
  unfold R
  intro hR
  obtain ⟨hT, hH, -⟩ := hR
  exact hH

lemma R_closed_wt {T : Ty} {t : Term Ty} : R T t → ⬝ ⊢ t : T := by
  unfold R
  intro hR
  obtain ⟨hT, hH, -⟩ := hR
  exact hT

lemma cbv_pres_halt {t t' : Term Ty} (ht : t ⟶v t') : Halts CBV t ↔ Halts CBV t' := by
  constructor
  · intro hH
    obtain ⟨s'', ht, hN⟩ := hH
    cases ht with
    | refl =>
      exfalso
      apply hN
      exists t'
    | step hs hs' =>
      have := cbv_det _ _ _ ht hs
      subst t'
      exists s''
  · intro hH
    obtain ⟨t'', ht', hN⟩ := hH
    exists t''
    exact ⟨.step ht ht', hN⟩

lemma cbv_pres_R' {T : Ty} {t t' : Term Ty} : (t ⟶v t') → R T t → R T t' := by
  intro ht hR
  induction T generalizing t t' with
  | a =>
    split_ands
    · exact preservation (R_closed_wt hR) ht
    · exact (cbv_pres_halt ht).mp (R_halts hR)
    · trivial
  | f T₁ T₂ ih₁ ih₂ =>
    obtain ⟨hT, hH, hR⟩ := hR
    split_ands
    · exact preservation hT ht
    · exact (cbv_pres_halt ht).mp hH
    · intro s hR₁
      exact ih₂ (.app₁ ht) (hR _ hR₁)

lemma cbv_pres_R'' {T : Ty} {t t' : Term Ty} : (⬝ ⊢ t : T) → (t ⟶v t') → R T t' → R T t := by
  intro hT ht hR
  induction T generalizing t t' with
  | a =>
    split_ands
    · exact hT
    · exact (cbv_pres_halt ht).mpr (R_halts hR)
    · trivial
  | f T₁ T₂ ih₁ ih₂ =>
    obtain ⟨hT', hH, hR⟩ := hR
    split_ands
    · exact hT
    · exact (cbv_pres_halt ht).mpr hH
    · intro s hR₁
      exact ih₂ (.app hT (R_closed_wt hR₁)) (.app₁ ht) (hR _ hR₁)

-- TAPL 12.1.4
lemma cbv_pres_R {T : Ty} {t t' : Term Ty} : (⬝ ⊢ t : T) → (t ⟶v t') → (R T t ↔ R T t') := by
  intro hT ht
  exact ⟨cbv_pres_R' ht, cbv_pres_R'' hT ht⟩

lemma multi_pres_R {T : Ty} {t t' : Term Ty} : (⬝ ⊢ t : T) → (t ⟶*v t') → (R T t ↔ R T t') := by
  intro hT ht
  induction ht with
  | refl => rfl
  | @step _ t' _ ht ht' ih =>
    trans R T t'
    · exact cbv_pres_R hT ht
    · exact ih (preservation hT ht)

-- SF2: Norm
inductive Inst : Nat → List Ty → List (Term Ty) → Prop
  | nil :
    Inst 0 [] []
  | cons : ∀ {n T v Δ σ},
    Val v →
    R T v →
    Inst n Δ σ →
    Inst (n + 1) (T :: Δ) (v :: σ)

def ClosedEnv : List (Term Ty) → Prop
  | [] => True
  | t :: σ' => (∃ T, ⬝ ⊢ t : T) ∧ ClosedEnv σ'

lemma msub_closed' {n j : Nat} {Γ : Ctx n} {T : Ty} {t : Term Ty} {σ : List (Term Ty)} :
    n ≤ j → (Γ ⊢ t : T) → msub j σ t = t := by
  intro hj hT
  induction σ generalizing n j with
  | nil => rfl
  | cons v σ' ih =>
    dsimp [msub]
    rw [ih _ hT, sub_closed' _ hT] <;> linarith

lemma msub_closed {T : Ty} {t : Term Ty} {j : Nat} {σ : List (Term Ty)} :
    (⬝ ⊢ t : T) → msub j σ t = t := by
  apply msub_closed'
  linarith

lemma msub_a {j : Nat} {σ : List (Term Ty)} : msub j σ .a = .a := by
  exact msub_closed .a

lemma sub_comm {i j : Nat} {T T' : Ty} {t s s' : Term Ty} :
    (⬝ ⊢ s : T) → (⬝ ⊢ s' : T') → i ≠ j → [i ↦ s] ([j ↦ s'] t) = [j ↦ s'] ([i ↦ s] t) := by
  intro hT hT' hi
  induction t generalizing i j s s' with
  | a => rfl
  | var k =>
    dsimp [sub]
    split <;> split
    · grind only
    · dsimp [sub]
      split
      · rw [sub_closed hT']
      · contradiction
    · dsimp [sub]
      split
      · rw [sub_closed hT]
      · contradiction
    · dsimp [sub]
      grind only
  | abs T₁ t ih =>
    dsimp [sub]
    rw [shift_closed hT, shift_closed hT', ih hT hT']
    grind only
  | app t₁ t₂ ih₁ ih₂ =>
    dsimp [sub]
    rw [ih₁ hT hT' hi, ih₂ hT hT' hi]

lemma sub_msub_comm {i j : Nat} {σ : List (Term Ty)} {T : Ty} {t s : Term Ty} :
    (⬝ ⊢ s : T) → ClosedEnv σ → i < j → [i ↦ s] (msub j σ t) = msub j σ ([i ↦ s] t) := by
  intro hT hσ hi
  induction σ generalizing j with
  | nil => rfl
  | cons s' σ' ih =>
    obtain ⟨⟨T', hT'⟩, hσ'⟩ := hσ
    dsimp [msub]
    rw [sub_comm hT hT', ih hσ'] <;> linarith

lemma msub_var {j k : Nat} {σ : List (Term Ty)} :
    ClosedEnv σ → msub j σ (.var k) =
    if h : j ≤ k ∧ k - j < σ.length then σ[k - j]'(by linarith) else .var k := by
  intro hσ
  induction σ generalizing j with
  | nil =>
    dsimp [msub]
    grind only
  | cons v σ' ih =>
    obtain ⟨⟨T, hT⟩, hσ'⟩ := hσ
    dsimp [msub]
    rw [sub_msub_comm hT hσ']
    · dsimp [sub]
      split <;> split
      case' cons.isTrue.isTrue => rw [msub_closed hT]
      all_goals
        grind only [= List.getElem_cons]
    · linarith

lemma msub_abs {j : Nat} {σ : List (Term Ty)} {T : Ty} {t : Term Ty} :
    ClosedEnv σ → msub j σ (.abs T t) = .abs T (msub (j + 1) σ t) := by
  intro hC
  induction σ generalizing j t with
  | nil => rfl
  | cons v σ' ih =>
    obtain ⟨⟨T', hT'⟩, hC'⟩ := hC
    dsimp [msub]
    rw [ih hC']
    dsimp [sub]
    rw [shift_closed hT']

lemma msub_app {j : Nat} {σ : List (Term Ty)} {t₁ t₂ : Term Ty} :
    msub j σ (.app t₁ t₂) = .app (msub j σ t₁) (msub j σ t₂) := by
  induction σ generalizing j t₁ t₂ with
  | nil => rfl
  | cons v σ' ih =>
    dsimp [msub]
    rw [ih]
    rfl

lemma inst_Δ_length_eq {n : Nat} {Δ : List Ty} {σ : List (Term Ty)} :
    Inst n Δ σ → Δ.length = n := by
  intro hI
  induction hI <;> grind only [= List.length_cons, = List.length_nil]

lemma inst_σ_length_eq {n : Nat} {Δ : List Ty} {σ : List (Term Ty)} :
    Inst n Δ σ → σ.length = n := by
  intro hI
  induction hI <;> grind only [= List.length_cons, = List.length_nil]

lemma inst_closed_env {n : Nat} {Δ : List Ty} {σ : List (Term Ty)} : Inst n Δ σ → ClosedEnv σ := by
  intro hI
  induction hI with
  | nil => constructor
  | cons hv hR hI' ih =>
    constructor
    · exact ⟨_, R_closed_wt hR⟩
    · exact ih

lemma inst_R {n : Nat} {Δ : List Ty} {σ : List (Term Ty)} :
    (hI : Inst n Δ σ) → ∀ (i : Nat) T t, (h : i < n) →
    Δ[i]'(by rw [inst_Δ_length_eq hI]; exact h) = T →
    σ[i]'(by rw [inst_σ_length_eq hI]; exact h) = t → R T t := by
  intro hI
  induction hI <;> grind only [= List.getElem_cons, = List.length_nil]

lemma msub_pres {n m : Nat} {Δ : List Ty} {σ : List (Term Ty)} {Γ : Ctx m} {T : Ty} {t : Term Ty} :
    Inst n Δ σ → (mextend Δ Γ ⊢ t : T) → Γ ⊢ msub m σ t : T := by
  intro hI hT
  induction t generalizing m Γ T with
  | a =>
    cases hT with
    | a =>
      rw [msub_a]
      exact .a
  | var k =>
    cases hT with
    | var k hT =>
      have hΔl := inst_Δ_length_eq hI
      have hσl := inst_σ_length_eq hI
      rw [msub_var (inst_closed_env hI)]
      rw [mextend_mem] at hT
      subst T
      split <;> split
      · have hR := inst_R hI (k - m) Δ[k - m] σ[k - m] (by linarith) rfl rfl
        exact weakening_closed (R_closed_wt hR)
      · linarith
      · omega
      · apply Typed.var (k.castLT _)
        rfl
  | abs T₁ t ih =>
    cases hT with
    | abs hT₂ =>
      rw [msub_abs (inst_closed_env hI)]
      rw [mextend_extend] at hT₂
      exact .abs (ih hT₂)
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT with
    | app hT₁ hT₂ =>
      rw [msub_app]
      exact .app (ih₁ hT₁) (ih₂ hT₂)

lemma msub_R {n : Nat} {Δ : List Ty} {σ : List (Term Ty)} {T : Ty} {t : Term Ty} :
    (mextend Δ ⬝ ⊢ t : T) → Inst n Δ σ → R T (msub 0 σ t) := by
  intro hT hI
  induction t generalizing n Δ σ T with
  | a =>
    cases hT with
    | a =>
      rw [msub_a]
      split_ands
      · exact .a
      · exact val_halts .a
      · trivial
  | var k =>
    cases hT with
    | var k hT =>
      have hΔl := inst_Δ_length_eq hI
      have hσl := inst_σ_length_eq hI
      rw [msub_var (inst_closed_env hI)]
      rw [mextend_mem] at hT
      apply inst_R hI k
      case var.var.h => omega
      all_goals
        grind only
  | abs T₁ t ih =>
    cases hT with
    | abs hT₂ =>
      rw [msub_abs (inst_closed_env hI)]
      rw [mextend_extend] at hT₂
      have hT₂' := msub_pres hI hT₂
      split_ands
      · exact .abs hT₂'
      · exact val_halts .abs
      · intro s hR
        obtain ⟨v, hs, hN⟩ := R_halts hR
        have hT₁ := R_closed_wt hR
        have hR' := (multi_pres_R hT₁ hs).mp hR
        have hT₁' := R_closed_wt hR'
        have hv := nf_val hT₁' hN
        rw [← mextend_nil, ← mextend_cons] at hT₂'
        have hT₂'' := msub_pres (.cons hv hR' .nil) hT₂'
        apply (multi_pres_R _ (multi_trans (multi_app₂ .abs hs) (multi_closed (.appabs hv)))).mpr
        · rw [shift_closed hT₁']
          dsimp [msub] at hT₂''
          rw [unshift_closed hT₂'']
          exact ih hT₂ (.cons hv hR' hI)
        · exact .app (.abs hT₂') hT₁
  | app t₁ t₂ ih₁ ih₂ =>
    cases hT with
    | app hT₁ hT₂ =>
      rw [msub_app]
      obtain ⟨hT₁, hH₁, hR₁⟩ := ih₁ hT₁ hI
      exact hR₁ _ (ih₂ hT₂ hI)

-- TAPL 12.1.6
theorem normalization {T : Ty} {t : Term Ty} : (⬝ ⊢ t : T) → Halts CBV t := by
  intro hT
  rw [← mextend_nil] at hT
  exact R_halts (msub_R hT .nil)
