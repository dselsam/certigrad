/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Stochastic programs.

An `sprog` represents an abstract stochastic computation, in which all primitive stochastic choices
are reified. We denote an `sprog` to a PDF to reason about mathematically, and to an RNG computation
to execute.
-/
import .det .rand

namespace certigrad

structure dist (ishapes : list S) : Type := (ev : Π {oshape : S}, (dvec T ishapes → T oshape) → T oshape)

noncomputable def pdf {ishapes : list S} (h : dvec T ishapes → ℝ) : dist ishapes :=
⟨λ (oshape : S) (f : dvec T ishapes → T oshape), T.dintegral (λ x, h x ⬝ f x)⟩

def delta {ishapes : list S} (x : dvec T ishapes) : dist ishapes :=
⟨λ (oshape : S) (f : dvec T ishapes → T oshape), f x⟩

notation `δ` := delta

def ev {ishapes : list S} {oshape : S} (d : dist ishapes) (f : dvec T ishapes → T oshape) : T oshape := d^.ev f

inductive sprog : Π (shapes : list S), Type
| ret  : Π {shapes : list S}, dvec T shapes → sprog shapes
| bind : Π {shapes₁ shapes₂ : list S}, sprog shapes₁ → (dvec T shapes₁ → sprog shapes₂) → sprog shapes₂
| prim : Π {ishapes : list S} {oshape : S}, rand.op ishapes oshape → dvec T ishapes → sprog [oshape]


noncomputable def E {oshape : S} : Π {shapes : list S}, sprog shapes → (dvec T shapes → T oshape) → T oshape
| shapes (@sprog.ret .(shapes) xs) f := f xs

| shapes (@sprog.bind shapes₁ .(shapes) start rest) f := (E start) (λ (x : dvec T shapes₁), (E (rest x) f))

| ([oshape]) (@sprog.prim ishapes .(oshape) pd args) f := T.dintegral (λ (x : dvec T [oshape]), pd^.pdf args (dvec.head x) ⬝ f x)

namespace sprog

def to_rngprog : Π {shapes : list S}, sprog shapes → state RNG (dvec T shapes)
| shapes (@ret .(shapes) xs) := return xs
| shapes (@bind shapes₁ .(shapes) start rest) := do xs ← (to_rngprog start), to_rngprog (rest xs)
| ([oshape]) (@prim ishapes .(oshape) pd args) := do x ← pd^.run args, return ⟦x⟧

end sprog

end certigrad
