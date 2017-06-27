/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Interface for deterministic operators.
-/
import .tgrads .util .tcont

namespace certigrad
open T list

namespace det

def function (ishapes : list S) (oshape : S) : Type := dvec T ishapes → T oshape
def precondition (shapes : list S) : Type := dvec T shapes → Prop
def pullback (ishapes : list S) (oshape : S) : Type := Π (xs : dvec T ishapes) (y gy : T oshape) (idx : ℕ) (fshape : S), T fshape

noncomputable def is_odifferentiable {ishapes : list S} {oshape : S} (f : dvec T ishapes → T oshape) (f_pre : dvec T ishapes → Prop) : Prop :=
    ∀ (xs : dvec T ishapes), f_pre xs →
    ∀ (idx : ℕ) (fshape : S), at_idx ishapes idx fshape →
    ∀ (k : T oshape → ℝ), is_cdifferentiable k (f xs) → is_cdifferentiable (λ θ₀, k (f $ dvec.update_at θ₀ xs idx)) (dvec.get fshape xs idx)

noncomputable def pullback_correct {ishapes : list S} {oshape : S}
               (f : dvec T ishapes → T oshape)
               (f_pre : dvec T ishapes → Prop)
               (f_pb : dvec T ishapes → T oshape → T oshape → ℕ → Π fshape, T fshape) : Prop :=
    ∀ (xs : dvec T ishapes) (y : T oshape), y = f xs →
      ∀ (g_out : T oshape) {idx : ℕ} {fshape : S}, at_idx ishapes idx fshape →
              f_pre xs →
              f_pb xs y g_out idx fshape
               =
              T.tmulT (T.D (λ θ₀, f (dvec.update_at θ₀ xs idx)) (dvec.get fshape xs idx)) g_out

noncomputable def is_ocontinuous {ishapes : list S} {oshape : S} (f : dvec T ishapes → T oshape) (f_pre : dvec T ishapes → Prop) : Prop :=
  ∀ (xs : dvec T ishapes) {idx : ℕ} {ishape : S}, at_idx ishapes idx ishape →
      f_pre xs → T.is_continuous (λ θ₀, f (dvec.update_at θ₀ xs idx)) (dvec.get ishape xs idx)

inductive op : Π (ishapes : list S) (oshape : S),  Type
| mk : ∀ {ishapes : list S} {oshape : S} (id : string)
         (f :function ishapes oshape) (f_pre : precondition ishapes) (f_pb : pullback ishapes oshape),
         is_odifferentiable f f_pre → pullback_correct f f_pre f_pb → is_ocontinuous f f_pre →
         op ishapes oshape

-- Note: we keep this separate because we use it in a program transformation
-- (we want to be able to pattern match on it)
| mvn_iso_empirical_kl : Π (shape : S), op [shape, shape, shape] []


namespace op

def f : Π {ishapes : list S} {oshape : S}, op ishapes oshape → function ishapes oshape
| ._ ._ (@op.mk ishapes id oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  := fn
| ._ ._ (@op.mvn_iso_empirical_kl shape) := λ xs, T.mvn_iso_empirical_kl xs^.head xs^.head2 xs^.head3

def pre : Π {ishapes : list S} {oshape : S}, op ishapes oshape → precondition ishapes
| ._ ._ (@op.mk id ishapes oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  := f_pre
| ._ ._ (@mvn_iso_empirical_kl shape) := λ xs, false

def pb : Π {ishapes : list S} {oshape : S}, op ishapes oshape → pullback ishapes oshape
| ._ ._ (@op.mk id ishapes oshape fn f_pre f_pb is_odiff pb_correct is_continuous)  := f_pb
| ._ ._ (@mvn_iso_empirical_kl shape) := λ xs y gy idx fshape, T.error "mvn_iso_empirical_kl: gradients not implemented"

def is_odiff : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), is_odifferentiable op^.f op^.pre
| ._ ._ (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) := f_is_odiff
| ._ ._ (@mvn_iso_empirical_kl shape) := λ xs H_pre idx fshape H_fshape_at_idx k H_k, false.rec _ H_pre

def pb_correct : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), pullback_correct op^.f op^.pre op^.pb
| ._ ._ (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) := f_pb_correct
| ._ ._ (@mvn_iso_empirical_kl shape) := λ xs y _ g_out _ _ H_at_idx H_pre, false.rec _ H_pre

def is_ocont : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), is_ocontinuous op^.f op^.pre
| ._ ._ (@op.mk id ishapes oshape fn f_pre f_pb f_is_odiff f_pb_correct f_is_continuous) := f_is_continuous
| ._ ._ (@mvn_iso_empirical_kl shape) := λ xs idx ishape H_ishape_at_idx H_pre, false.rec _ H_pre

end op
end det
end certigrad
