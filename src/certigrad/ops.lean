/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Deterministic operators.
-/
import .tgrads .util .tcont .det

namespace certigrad
open T list

namespace ops

section tactic
open tactic

meta def idx_over : tactic unit :=
do exfalso, to_expr ```(at_idx_over H_at_idx dec_trivial) >>= exact

meta def simp_simple : tactic unit :=
do s₀ ← simp_lemmas.mk_default,
   s ← return $ simp_lemmas.erase s₀ $ [`add_comm, `add_left_comm, `mul_comm, `mul_left_comm],
   simplify_goal s {} >> try triv >> try (reflexivity reducible)

meta def prove_odiff : tactic unit :=
do get_local `f_odiff >>= clear,
   to_expr ```(shape = fshape) >>= λ ty, to_expr ```(eq.symm H_at_idx^.right) >>= λ val, assertv `H_fshape_eq ty val,
   get_local `H_fshape_eq >>= subst,
   dunfold [`certigrad.det.is_odifferentiable],
   try simp_simple,
   try dsimp,
   prove_differentiable

meta def prove_pb_correct_init : tactic unit :=
do get_local `f_pb_correct >>= clear,
   to_expr ```(shape = fshape) >>= λ ty, to_expr ```(eq.symm H_at_idx^.right) >>= λ val, assertv `H_fshape_eq ty val,
   get_local `H_fshape_eq >>= subst,
   to_expr ```(T shape → ℝ) >>= λ ty, to_expr ```(λ (z : T shape), T.dot z g_out) >>= definev `k ty,
   to_expr ```(∇ k y = g_out) >>= assert `H_k_grad, dsimp, rewrite `certigrad.T.grad_dot₁,
   get_local `H_k_grad >>= rewrite_core reducible tt tt occurrences.all tt,
   get_local `H_y >>= subst

meta def prove_pb_correct : tactic unit :=
do prove_pb_correct_init,
   try simp_simple,
   try dsimp,
   mk_const `certigrad.T.grad_tmulT >>= rewrite_core reducible tt tt occurrences.all tt,
   simplify_grad,
   try simp,
   try reflexivity

meta def prove_ocont_init : tactic unit :=
do get_local `f_ocont >>= clear,
   to_expr ```(shape = ishape) >>= λ ty, to_expr ```(eq.symm H_at_idx^.right) >>= λ val, assertv `H_ishape_eq ty val,
   get_local `H_ishape_eq >>= subst,
   try simp_simple,
   try dsimp

meta def prove_ocont : tactic unit :=
do prove_ocont_init,
   repeat (prove_continuous_core <|> prove_preconditions_core)

end tactic

open det

namespace scale

def f (α : ℝ) {shape : S} (xs : dvec T [shape]) : T shape := α ⬝ xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb (α : ℝ) {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (α ⬝ gy) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff (α : ℝ) {shape : S} : is_odifferentiable (@f α shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct (α : ℝ) {shape : S} : pullback_correct (@f α shape) (@f_pre shape) (@f_pb α shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont (α : ℝ) {shape : S} : is_ocontinuous (@f α shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end scale

section open scale
def scale (α : ℝ) (shape : S) : det.op [shape] shape :=
det.op.mk "scale" (f α) f_pre (f_pb α) (f_odiff α) (f_pb_correct α) (f_ocont α)

end

namespace neg

def f {shape : S} (xs : dvec T [shape]) : T shape := - xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (-gy) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end neg

section open neg
def neg (shape : S) : det.op [shape] shape :=
det.op.mk "neg" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace exp

def f {shape : S} (xs : dvec T [shape]) : T shape := exp xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy * y) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end exp

section open exp
def exp (shape : S) : det.op [shape] shape :=
det.op.mk "exp" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace log

def f {shape : S} (xs : dvec T [shape]) : T shape := log xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, xs^.head > 0
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy / xs^.head) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end log

section open log
def log (shape : S) : det.op [shape] shape :=
det.op.mk "log" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace sqrt

def f {shape : S} (xs : dvec T [shape]) : T shape := sqrt xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, 0 < xs^.head
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy / (2 * y)) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end sqrt

section open sqrt
def sqrt (shape : S) : det.op [shape] shape :=
det.op.mk "sqrt" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace sigmoid

def f {shape : S} (xs : dvec T [shape]) : T shape := sigmoid xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape :=
force (gy * y * (1 - y)) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end sigmoid

section open sigmoid
def sigmoid (shape : S) : det.op [shape] shape :=
det.op.mk "sigmoid" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace softplus

def f {shape : S} (xs : dvec T [shape]) : T shape := softplus xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape :=
force (gy / (1 + T.exp (- xs^.head))) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| xs H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| xs (n+1) ishape H_at_idx H_pre := by idx_over

end softplus

section open softplus
def softplus (shape : S) : det.op [shape] shape :=
det.op.mk "softplus" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace add

def f {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head + xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧ H_pre 0 fshape H_at_idx k H_k := by { prove_odiff }
| ⟦x, y⟧ H_pre 1 fshape H_at_idx k H_k := by { prove_odiff }
| xs    H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_at_idx H_pre := by prove_pb_correct
| xs      y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧ 0     ishape H_at_idx H_pre := by prove_ocont
| ⟦x₁, x₂⟧ 1     ishape H_at_idx H_pre := by prove_ocont
| xs      (n+2) ishape H_at_idx H_pre := by idx_over

end add

section open add
def add (shape : S) : det.op [shape, shape] shape :=
det.op.mk "add" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace mul

def f {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head * xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, true

def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy * xs^.head2) fshape
| 1     fshape := force (gy * xs^.head) fshape
| (n+2) fshape := T.error "mul: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧ H_pre 0 fshape H_at_idx k H_k := by { prove_odiff }
| ⟦x, y⟧ H_pre 1 fshape H_at_idx k H_k := by { prove_odiff }
| xs    H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_at_idx H_pre := by prove_pb_correct
| xs      y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧ 0     ishape H_at_idx H_pre := by prove_ocont
| ⟦x₁, x₂⟧ 1     ishape H_at_idx H_pre := by prove_ocont
| xs      (n+2) ishape H_at_idx H_pre := by idx_over

end mul

section open mul
def mul (shape : S) : det.op [shape, shape] shape :=
det.op.mk "mul" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace sub

def f {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head - xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, true

def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy) fshape
| 1     fshape := force (- gy) fshape
| (n+2) fshape := T.error "sub: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧ H_pre 0 fshape H_at_idx k H_k := by { prove_odiff }
| ⟦x, y⟧ H_pre 1 fshape H_at_idx k H_k := by { prove_odiff }
| xs    H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_at_idx H_pre := by prove_pb_correct
| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_at_idx H_pre := by prove_pb_correct
| xs      y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧ 0     ishape H_at_idx H_pre := by prove_ocont
| ⟦x₁, x₂⟧ 1     ishape H_at_idx H_pre := by prove_ocont
| xs      (n+2) ishape H_at_idx H_pre := by idx_over

end sub

section open sub
def sub (shape : S) : det.op [shape, shape] shape :=
det.op.mk "sub" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace div

def f {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head / xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, 0 < T.square xs^.head2

def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy / xs^.head2) fshape
| 1     fshape := force (- (gy * xs^.head) / (T.square xs^.head2)) fshape
| (n+2) fshape := T.error "div: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x, y⟧ H_pre 0 fshape H_at_idx k H_k := by { prove_odiff }
| ⟦x, y⟧ H_pre 1 fshape H_at_idx k H_k := by { prove_odiff }
| xs    H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_at_idx H_pre := begin prove_pb_correct end
| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_at_idx H_pre := by prove_pb_correct
| xs      y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x₁, x₂⟧ 0     ishape H_at_idx H_pre := by prove_ocont
| ⟦x₁, x₂⟧ 1     ishape H_at_idx H_pre := by prove_ocont
| xs      (n+2) ishape H_at_idx H_pre := by idx_over

end div

section open div
def div (shape : S) : det.op [shape, shape] shape :=
det.op.mk "div" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace sum

def f {shape : S} (xs : dvec T [shape]) : ℝ := T.sum xs^.head
def f_pre {shape : S} : precondition [shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape]) (y gy : ℝ) (idx : ℕ) (fshape : S) : T fshape := force (T.const gy shape) fshape

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦x⟧ H_pre 0 fshape H_at_idx k H_k := by prove_odiff
| ⟦x⟧ H_pre (n+1) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦x⟧ y H_y g_out 0 fshape H_at_idx H_pre :=
begin
clear f_pb_correct,
assertv H_fshape_eq : shape = fshape := eq.symm H_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
simp, dsimp,
dunfold dvec.get dvec.head dvec.update_at,
rw -T.grad_tmulT,
rw T.grad_sum k,
simp [T.smul.def]
end

| xs y H_y g_out (n+1) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦x⟧ 0 ishape H_at_idx H_pre := by prove_ocont
| ⟦x⟧ (n+1) ishape H_at_idx H_pre := by idx_over

end sum

section open sum
-- TODO(dhs): why won't it find `f` without `sum.`? Bug in Lean?
def sum (shape : S) : det.op [shape] [] :=
det.op.mk "sum" sum.f sum.f_pre sum.f_pb sum.f_odiff sum.f_pb_correct sum.f_ocont
end

namespace gemm

def f {m n p : ℕ} (xs : dvec T [[m, n], [n, p]]) : T [m, p] := gemm xs^.head xs^.head2
def f_pre {m n p : ℕ} : precondition [[m, n], [n, p]] := λ xs, true
def f_pb {m n p : ℕ} (xs : dvec T [[m, n], [n, p]]) (y gy : T [m, p]) : Π (idx : ℕ) (fshape : S), T fshape
| 0 fshape := force (T.gemm gy (transpose $ xs^.head2)) fshape
| 1 fshape := force (T.gemm (transpose $ xs^.head) gy) fshape
| (n+2) fshape := T.error "gemm: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {m n p : ℕ} : is_odifferentiable (@f m n p) (@f_pre m n p)
| ⟦x₁, x₂⟧ H_pre 0 fshape H_at_idx k H_k := begin definev shape : S := [m, n], prove_odiff end
| ⟦x₁, x₂⟧ H_pre 1 fshape H_at_idx k H_k := begin definev shape : S := [n, p], prove_odiff end
| xs      H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {m n p : ℕ} : pullback_correct (@f m n p) (@f_pre m n p) (@f_pb m n p)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear f_pb_correct,
assertv H_fshape_eq : [m, n] = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : T [m, p] → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
simp, dsimp,
rw [-T.grad_tmulT, T.grad_gemm₁ k]
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear f_pb_correct,
assertv H_fshape_eq : [n, p] = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : T [m, p] → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
simp, dsimp,
rw [-T.grad_tmulT, T.grad_gemm₂ k]
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma f_ocont {m n p : ℕ} : is_ocontinuous (@f m n p) (@f_pre m n p)
| ⟦x₁, x₂⟧ 0     ishape H_at_idx H_pre := by { pose shape := [m, n], prove_ocont }
| ⟦x₁, x₂⟧ 1     ishape H_at_idx H_pre := by { pose shape := [n, p], prove_ocont }
| xs      (n+2) ishape H_at_idx H_pre := by idx_over

end gemm

section open gemm
def gemm (m n p : ℕ) : det.op [[m, n], [n, p]] [m, p] :=
det.op.mk "gemm" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace mvn_iso_kl

def f {shape : S} (xs : dvec T [shape, shape]) : ℝ := mvn_iso_kl xs^.head xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, 0 < xs^.head2

def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : ℝ) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy ⬝ xs^.head) fshape
| 1     fshape := force (gy ⬝ (xs^.head2 - (1 / xs^.head2))) fshape
| (n+2) fshape := T.error "mvn_iso_kl: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦μ, σ⟧ H_pre 0     fshape H_at_idx k H_k := by prove_odiff
| ⟦μ, σ⟧ H_pre 1     fshape H_at_idx k H_k := by prove_odiff
| xs    H_pre (n+2) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦μ, σ⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear f_pb_correct,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
simp,
rw -T.grad_tmulT,
simplify_grad,
simp [T.smul.def]
end

| ⟦μ, σ⟧ y H_y g_out 1 fshape H_at_idx H_pre :=
have H_σ₂ : square σ > 0, from square_pos_of_pos H_pre,
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * (-2⁻¹ * T.sum (1 + T.log (square θ₀) - square μ - square σ))) σ, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * (-2⁻¹ * T.sum (1 + T.log (square σ) - square μ - square θ₀))) σ, by prove_differentiable,
begin
clear f_pb_correct,
assertv H_fshape_eq : shape = fshape := eq.symm H_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
simp,
rw -T.grad_tmulT,
dunfold T.mvn_iso_kl,

rw (T.grad_binary (λ θ₁ θ₂, g_out * ((- 2⁻¹) * T.sum (1 + T.log (square θ₁) - square μ - square θ₂))) _ H_diff₁ H_diff₂),
dsimp,
simplify_grad,

simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero,
      T.const_one, T.const_bit0, T.const_bit1, T.const_inv,
      left_distrib, right_distrib],
rw T.mul_inv_cancel two_pos,
erw T.neg_div,
simp [mul_neg_eq_neg_mul_symm, neg_mul_eq_neg_mul_symm],
apply congr_arg, apply congr_arg,
simp only [T.mul_div_mul, square],
rw [-mul_assoc, T.mul_div_mul, (@T.div_self_square _ σ H_pre)],
simp,
rw [T.mul_inv_cancel two_pos],
simp,
rw T.div_mul_inv,
end

| ⟦μ, σ⟧ y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦μ, σ⟧ 0     ishape H_at_idx H_pre := by { prove_ocont, apply T.continuous_mvn_iso_kl₁, exact H_pre }
| ⟦μ, σ⟧ 1     ishape H_at_idx H_pre := by { prove_ocont }
| ⟦μ, σ⟧ (n+2) ishape H_at_idx H_pre := by idx_over

end mvn_iso_kl

section open mvn_iso_kl
def mvn_iso_kl (shape : S) : det.op [shape, shape] [] :=
det.op.mk "mvn_iso_kl" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

-- Seems silly but saves some fresh-name tracking in reparam
namespace mul_add

def f {shape : S} (xs : dvec T [shape, shape, shape]) : T shape := (xs^.head * xs^.head2) + xs^.head3
def f_pre {shape : S} : precondition [shape, shape, shape] := λ xs, true
def f_pb {shape : S} (xs : dvec T [shape, shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy * xs^.head2) fshape
| 1     fshape := force (gy * xs^.head) fshape
| 2     fshape := force gy fshape
| (n+3) _      := T.error "mul_add: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦z, σ, μ⟧ H_pre 0     fshape H_at_idx k H_k := by prove_odiff
| ⟦z, σ, μ⟧ H_pre 1     fshape H_at_idx k H_k := by prove_odiff
| ⟦z, σ, μ⟧ H_pre 2     fshape H_at_idx k H_k := by prove_odiff
| xs       H_pre (n+3) fshape H_at_idx k H_k := by idx_over

lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦z, σ, μ⟧ y H_y g_out 0 fshape H_at_idx H_pre :=
begin
prove_pb_correct_init,
simp only [f, f_pre, f_pb, force_ok, dif_pos],
dsimp,
simp only [dif_pos, dif_neg],
dsimp,
rw -T.grad_tmulT,
simplify_grad,
reflexivity
end

| ⟦z, σ, μ⟧ y H_y g_out 1 fshape H_at_idx H_pre :=
begin
prove_pb_correct_init,
simp without mul_comm add_comm,
dsimp,
rw -T.grad_tmulT,
simplify_grad,
reflexivity
end

| ⟦z, σ, μ⟧ y H_y g_out 2 fshape H_at_idx H_pre :=
begin
prove_pb_correct_init,
simp without mul_comm add_comm,
dsimp,
rw -T.grad_tmulT,
simplify_grad,
reflexivity
end

| xs y H_y g_out (n+3) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦z, σ, μ⟧ 0     ishape H_at_idx H_pre := by prove_ocont
| ⟦z, σ, μ⟧ 1     ishape H_at_idx H_pre := by prove_ocont
| ⟦z, σ, μ⟧ 2     ishape H_at_idx H_pre := by prove_ocont
| xs       (n+3) ishape H_at_idx H_pre := by idx_over

end mul_add

section open mul_add
def mul_add (shape : S) : det.op [shape, shape, shape] shape :=
det.op.mk "mul_add" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

namespace bernoulli_neglogpdf

def f {shape : S} (xs : dvec T [shape, shape]) : ℝ := bernoulli_neglogpdf xs^.head xs^.head2
def f_pre {shape : S} : precondition [shape, shape] := λ xs, 0 < xs^.head ∧ xs^.head < 1

def f_pb {shape : S} (xs : dvec T [shape, shape]) (y gy : ℝ) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy ⬝ (1 - xs^.head2) / (eps shape + (1 - xs^.head)) - gy ⬝ (xs^.head2 / (eps shape + xs^.head))) fshape
| 1     fshape := force (gy ⬝ T.log (eps shape + (1 - xs^.head)) - gy ⬝ T.log (eps shape + xs^.head)) fshape
| (n+2) fshape := T.error "bernoulli_neglogpdf: index too large"

attribute [simp] f f_pre f_pb

lemma f_odiff {shape : S} : is_odifferentiable (@f shape) (@f_pre shape)
| ⟦p, z⟧ H_pre 0 fshape H_at_idx k H_k :=
have H_p₁ : p > 0, from H_pre^.left,
have H_p₂ : p < 1, from H_pre^.right,
by prove_odiff

| ⟦p, z⟧ H_pre 1 fshape H_at_idx k H_k := by prove_odiff
| ⟦μ, σ⟧ H_pre (n+2) fshape H_at_idx k H_k := by idx_over


lemma f_pb_correct {shape : S} : pullback_correct (@f shape) (@f_pre shape) (@f_pb shape)
| ⟦p, z⟧ y H_y g_out 0 fshape H_at_idx H_pre :=
have H_p : p > 0, from H_pre^.left,
have H_1mp : 1 - p > 0, from lt1_alt H_pre^.right,
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log (eps shape + θ₀) + (1 - z) * T.log (eps shape + (1 - p)))) p, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log (eps shape + p) + (1 - z) * T.log (eps shape + (1 - θ₀)))) p, by prove_differentiable,

begin
clear f_pb_correct,
assertv H_fshape_eq : shape = fshape := eq.symm H_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
simp ,
rw -T.grad_tmulT,
dunfold T.bernoulli_neglogpdf,
rw T.grad_binary (λ θ₁ θ₂, g_out * - T.sum (z * T.log (eps shape + θ₁) + (1 - z) * T.log (eps shape + (1 - θ₂)))) _ H_diff₁ H_diff₂,
dsimp,
note H₁ := H_pre^.left,
note H₂ := lt1_alt H_pre^.right,
simplify_grad,
simp [T.smul.def, T.neg_div, T.const_neg],
rw [T.mul_div_mul],
simp [T.div_mul_inv],
end

| ⟦p, z⟧ y H_y g_out 1 fshape H_at_idx H_pre :=
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (θ₀ * T.log (eps shape + p) + (1 - z) * T.log (eps shape + (1 - p)))) z, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log (eps shape + p) + (1 - θ₀) * T.log (eps shape + (1 - p)))) z, by prove_differentiable,

begin
clear f_pb_correct,
assertv H_fshape_eq : shape = fshape := eq.symm H_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
simp,
rw -T.grad_tmulT,
dunfold T.bernoulli_neglogpdf,
rw T.grad_binary (λ θ₁ θ₂, g_out * - T.sum (θ₁ * T.log (eps shape + p) + (1 - θ₂) * T.log (eps shape + (1 - p)))) _ H_diff₁ H_diff₂,
dsimp,
simplify_grad,
simp [T.smul.def, const_neg],
end

| xs y H_y g_out (n+2) fshape H_at_idx H_pre := by idx_over

lemma f_ocont {shape : S} : is_ocontinuous (@f shape) (@f_pre shape)
| ⟦μ, σ⟧ 0     ishape H_at_idx H_pre := by { prove_ocont_init, apply continuous_bernoulli_neglogpdf₁, exact H_pre^.left, exact lt1_alt H_pre^.right }
| ⟦μ, σ⟧ 1     ishape H_at_idx H_pre := by { prove_ocont_init, apply continuous_bernoulli_neglogpdf₂, exact H_pre^.left, exact lt1_alt H_pre^.right }
| ⟦μ, σ⟧ (n+2) ishape H_at_idx H_pre := by idx_over

end bernoulli_neglogpdf

section
open bernoulli_neglogpdf
def bernoulli_neglogpdf (shape : S) : det.op [shape, shape] [] :=
det.op.mk "bernoulli_neglogpdf" f f_pre f_pb f_odiff f_pb_correct f_ocont
end

end ops

-- TODO(dhs): confirm I don't need this any more
/-
lemma mvn_iso_kl_pre {shape : S} (xs : dvec T [shape, shape]) :
  det.op.pre (det.op.special (det.special.mvn_iso_kl shape)) xs = (dvec.head2 xs > 0) := rfl
-/
end certigrad
