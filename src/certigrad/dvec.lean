/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Dependently-typed vectors.

These are necessary to store multiple tensors of arbitrary shapes.
-/
import .util

inductive dvec {X : Type} (Y : X → Type) : list X → Type
| nil {}  : dvec []
| cons : Π {x : X}, Y x → Π {xs : list X}, dvec xs → dvec (x::xs)

namespace dvec
reserve infixr ` ::: `:67
notation h `:::` t  := cons h t

notation `⟦` l:(foldr `, ` (h t, cons h t) nil `⟧`) := l

def head {X : Type} {Y : X → Type} {x : X} {xs : list X} : dvec Y (x::xs) → Y x
| (cons y ys) := y

def tail {X : Type} {Y : X → Type} {x : X} {xs : list X} : dvec Y (x::xs) → dvec Y xs
| (cons y ys) := ys

def head2 {X : Type} {Y : X → Type} {x₁ x₂ : X} {xs : list X} : dvec Y (x₁::x₂::xs) → Y x₂
| (cons y₁ (cons y₂ ys)) := y₂

def head3 {X : Type} {Y : X → Type} {x₁ x₂ x₃ : X} {xs : list X} : dvec Y (x₁::x₂::x₃::xs) → Y x₃
| (cons y₁ (cons y₂ (cons y₃ ys))) := y₃

def get {X : Type} [decidable_eq X] {Y : X → Type} (x₀ : X) [inhabited (Y x₀)] : Π {xs : list X}, dvec Y xs → ℕ → Y x₀
| []      _           _     := default (Y x₀)
| (x::xs) (cons y ys) 0     := if H : x = x₀ then eq.rec_on H y else default (Y x₀)
| (x::xs) (cons y ys) (n+1) := get ys n

lemma singleton_congr {X : Type} {Y : X → Type} {x : X} (y₁ y₂ : Y x) : y₁ = y₂ → ⟦y₁⟧ = ⟦y₂⟧ := assume H, by rw H

lemma get₀_head {X : Type} [decidable_eq X] {Y : X → Type} (x₀ : X) [inhabited (Y x₀)] :
  ∀ {xs : list X} (ys : dvec Y (x₀::xs)), get x₀ ys 0 = head ys
| xs (y:::ys)   := begin dunfold head get, simp [dif_ctx_simp_congr, dif_pos] end

def update_at {X : Type} [decidable_eq X] {Y : X → Type} {x₀ : X} (y₀ : Y x₀) : Π {xs : list X} (ys : dvec Y xs) (idx : ℕ), dvec Y xs
| []      _                 _     := ⟦⟧
| (x::xs) (cons y ys) 0     := if H : x₀ = x then cons (eq.rec_on H y₀) ys else cons y ys
| (x::xs) (cons y ys) (n+1) := cons y (update_at ys n)

protected def to_string_aux {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] : Π {xs : list X}, dvec Y xs → string
| [] _                  := "-------------"
| (x::xs) (cons y ys)  := to_string y ++ "\n" ++ to_string_aux ys

protected def to_string {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] {xs : list X} (ys : dvec Y xs) : string :=
  "-------------\n" ++ dvec.to_string_aux ys

instance {X : Type} {Y : X → Type} [∀ x, has_to_string (Y x)] {xs : list X} : has_to_string (dvec Y xs) :=
⟨dvec.to_string⟩

attribute [simp] head tail head2 head3 get update_at

end dvec
