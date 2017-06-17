/-
Copyright (c) 2017 Daniel Selsam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Daniel Selsam

Deterministic operators.

Note: many of the proofs in this file could be automated by simple meta-programs.
-/
import .tgrads library_dev_extras.util .tcont

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


noncomputable def continuous {ishapes : list S} {oshape : S} (f : dvec T ishapes → T oshape) (f_pre : dvec T ishapes → Prop) : Prop :=
  ∀ (xs : dvec T ishapes) {idx : ℕ} {ishape : S}, at_idx ishapes idx ishape →
      f_pre xs → T.is_continuous (λ θ₀, f (dvec.update_at θ₀ xs idx)) (dvec.get ishape xs idx)

namespace function

def neg {shape : S} (xs : dvec T [shape]) : T shape := - xs^.head
def exp {shape : S} (xs : dvec T [shape]) : T shape := exp xs^.head
def log {shape : S} (xs : dvec T [shape]) : T shape := log xs^.head
def sqrt {shape : S} (xs : dvec T [shape]) : T shape := sqrt xs^.head
def scale (α : ℝ) {shape : S} (xs : dvec T [shape]) := α ⬝ xs^.head
def softplus {shape : S} (xs : dvec T [shape]) : T shape := softplus xs^.head
def sigmoid {shape : S} (xs : dvec T [shape]) : T shape := sigmoid xs^.head

def add {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head + xs^.head2
def sub {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head - xs^.head2
def mul {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head * xs^.head2
def div {shape : S} (xs : dvec T [shape, shape]) : T shape := xs^.head / xs^.head2

def sum {shape : S} (xs : dvec T [shape]) : ℝ := sum xs^.head
def gemv {m n : ℕ} (xs : dvec T [[m, n], [n]]) : T [m] := gemv xs^.head xs^.head2
def gemm {m n p : ℕ} (xs : dvec T [[m, n], [n, p]]) : T [m, p] := gemm xs^.head xs^.head2

def mvn_iso_logpdf {shape : S} (xs : dvec T [shape, shape, shape]) : ℝ := T.mvn_iso_logpdf xs^.head xs^.head2 xs^.head3
def mvn_iso_std_logpdf {shape : S} (xs : dvec T [shape]) : ℝ := T.mvn_iso_logpdf xs^.head 0 1
def get_col {m n : ℕ} (cidx : ℕ) (xs : dvec T [[m, n]]) : T [m] := T.get_col xs^.head cidx
def get_col_range {m n : ℕ} (ncols : ℕ) (xs : dvec T [[m, n], []]) : T [m, ncols] := T.get_col_range ncols xs^.head (T.round xs^.head2)
def replicate_col {m : ℕ} (n : ℕ) (xs : dvec T [[m]]) : T [m, n] := T.replicate_col xs^.head n

def mul_add {shape : S} (xs : dvec T [shape, shape, shape]) : T shape := (xs^.head * xs^.head2) + xs^.head3
def mvn_iso_kl {shape : S} (xs : dvec T [shape, shape]) : ℝ := T.mvn_iso_kl xs^.head xs^.head2
def mvn_iso_empirical_kl {shape : S} (xs : dvec T [shape, shape, shape]) : ℝ := T.mvn_iso_empirical_kl xs^.head xs^.head2 xs^.head3
def bernoulli_neglogpdf {shape : S} (xs : dvec T [shape, shape]) : ℝ := T.bernoulli_neglogpdf xs^.head xs^.head2

end function

namespace preconditions

namespace predicates
def top (ishapes : list S) : precondition ishapes := λ xs, true
def bot (ishapes : list S) : precondition ishapes := λ xs, false
def pos (shape : S) : precondition [shape] := λ xs, 0 < xs^.head
end predicates
open predicates

def neg {shape : S} : precondition [shape] := top [shape]
def exp {shape : S} : precondition [shape] := top [shape]
def log {shape : S} : precondition [shape] := pos shape
def sqrt {shape : S} : precondition [shape] := pos shape
def scale (α : ℝ) {shape : S} : precondition [shape] := top [shape]
def softplus {shape : S} : precondition [shape] := top [shape]
def sigmoid {shape : S} : precondition [shape] := top [shape]

def add {shape : S} : precondition [shape, shape] := top [shape, shape]
def sub {shape : S} : precondition [shape, shape] := top [shape, shape]
def mul {shape : S} : precondition [shape, shape] := top [shape, shape]
def div {shape : S} : precondition [shape, shape] := λ xs, 0 < square xs^.head2

def sum {shape : S} : precondition [shape] := top [shape]
def gemv {m n : ℕ} : precondition [[m, n], [n]] := bot [[m, n], [n]] -- Note: gemv not claiming to be differentiable
def gemm {m n p : ℕ} : precondition [[m, n], [n, p]] := top [[m, n], [n, p]]

def replicate_col {m : ℕ} (n : ℕ) (xs : dvec T [[m]]) : precondition [[m]] := top [[m]]

def mul_add {shape : S} : precondition [shape, shape, shape] := top [shape, shape, shape]
def mvn_iso_kl {shape : S} : precondition [shape, shape] := λ xs, 0 < xs^.head2
def mvn_iso_empirical_kl {shape : S} : precondition [shape, shape, shape] := bot [shape, shape, shape] -- Note: mvn_iso_empirical_kl not claiming to be differentiable
def bernoulli_neglogpdf {shape : S} : precondition [shape, shape] := λ xs, 0 < xs^.head ∧ xs^.head < 1

end preconditions

namespace pullback

def dummy {ishapes : list S} {oshape : S} : pullback ishapes oshape := λ xs y gy idx fshape, 0
def serror {ishapes : list S} {oshape : S} : pullback ishapes oshape := λ xs y gy idx fshape, T.silent_fail _
def error {ishapes : list S} {oshape : S} (f : string) : pullback ishapes oshape := λ xs y gy idx fshape, T.error ("pullback for '" ++ f ++ "' not implemented")

def neg {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (-gy) fshape
def exp {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy * y) fshape
def log {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy / xs^.head) fshape
def sqrt {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (gy / (2 * y)) fshape
def scale (α : ℝ) {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force (α ⬝ gy) fshape
def softplus {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape :=
  force (gy / (1 + T.exp (- xs^.head))) fshape

def sigmoid {shape : S} (xs : dvec T [shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape :=
  force (gy * y * (1 - y)) fshape

def add {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) (idx : ℕ) (fshape : S) : T fshape := force gy fshape
def sub {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force gy fshape
| 1     fshape := force (- gy) fshape
| (n+2) fshape := T.error "sub: index too large"

def mul {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy * xs^.head2) fshape
| 1     fshape := force (gy * xs^.head) fshape
| (n+2) fshape := T.error "mul: index too large"

def div {shape : S} (xs : dvec T [shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy / xs^.head2) fshape
| 1     fshape := force (- (gy * xs^.head) / (T.square xs^.head2)) fshape
| (n+2) fshape := T.error "div: index too large"

def sum {shape : S} (xs : dvec T [shape]) (y gy : ℝ) (idx : ℕ) (fshape : S) : T fshape := force (gy ⬝ (1 : T shape)) fshape

def gemm {m n p : ℕ} (xs : dvec T [[m, n], [n, p]]) (y gy : T [m, p]) : Π (idx : ℕ) (fshape : S), T fshape
| 0 fshape := force (T.gemm gy (transpose $ xs^.head2)) fshape
| 1 fshape := force (T.gemm (transpose $ xs^.head) gy) fshape
| (n+2) fshape := T.error "gemm: index too large"

def replicate_col {m : ℕ} (n : ℕ) (xs : dvec T [[m]]) (y gy : T [m, n]) (idx : ℕ) (fshape : S) : T fshape :=
force (T.sum_cols gy) fshape

def mul_add {shape : S} (xs : dvec T [shape, shape, shape]) (y gy : T shape) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy * xs^.head2) fshape
| 1     fshape := force (gy * xs^.head) fshape
| 2     fshape := force gy fshape
| (n+3) _      := T.error "mul_add: index too large"

def mvn_iso_kl {shape : S} (xs : dvec T [shape, shape]) (y gy : ℝ) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy ⬝ xs^.head) fshape
| 1     fshape := force (gy ⬝ (xs^.head2 - (1 / xs^.head2))) fshape
| (n+2) fshape := T.error "mvn_iso_kl: index too large"

def mvn_iso_empirical_kl {shape : S} (xs : dvec T [shape, shape, shape]) (y gy : ℝ) (idx : ℕ) (fshape : S) : T fshape :=
T.error "mvn_iso_empirical_kl: gradients not implemented"

def bernoulli_neglogpdf {shape : S} (xs : dvec T [shape, shape]) (y gy : ℝ) : Π (idx : ℕ) (fshape : S), T fshape
| 0     fshape := force (gy ⬝ (1 - xs^.head2) / (1 - xs^.head) - gy ⬝ (xs^.head2 / xs^.head)) fshape
| 1     fshape := force (gy ⬝ T.log (1 - xs^.head) - gy ⬝ T.log xs^.head) fshape
| (n+2) fshape := T.error "bernoulli_neglogpdf: index too large"

end pullback

namespace odifferentiable

def dummy {ishapes : list S} {oshape : S} {f : dvec T ishapes → T oshape} : is_odifferentiable f (λ xs, false) :=
assume xs H_pre idx fshape H_fshape_at_idx k Hk, false.rec _ H_pre

section
open tactic

meta def start_odiff : tactic unit :=
do to_expr ```(shape = fshape) >>= λ ty, to_expr ```(eq.symm H_fshape_at_idx^.right) >>= λ val, assertv `H_fshape_eq ty val,
   get_local `H_fshape_eq >>= subst,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3],
   try simp,
   dsimp,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3]

end

lemma neg (shape : S) : is_odifferentiable (@function.neg shape) (@preconditions.neg shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.neg, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma exp (shape : S) : is_odifferentiable (@function.exp shape) (@preconditions.exp shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.exp, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma log (shape : S) : is_odifferentiable (@function.log shape) (@preconditions.log shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.log, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sqrt (shape : S) : is_odifferentiable (@function.sqrt shape) (@preconditions.sqrt shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.sqrt, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma scale (α : ℝ) (shape : S) : is_odifferentiable (@function.scale α shape) (@preconditions.scale α shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.scale, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma softplus (shape : S) : is_odifferentiable (@function.softplus shape) (@preconditions.softplus shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k :=
  have H : T.exp x + 1 > 0, from plus_one_pos exp_pos,
  by { start_odiff, dsimp [function.softplus, T.softplus, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sigmoid (shape : S) : is_odifferentiable (@function.sigmoid shape) (@preconditions.sigmoid shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k :=
  have H : square (1 + T.exp (- x)) > 0, from square_pos_of_pos (one_plus_pos exp_pos),
  by { start_odiff, dsimp [function.sigmoid, T.sigmoid, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma add (shape : S) : is_odifferentiable (@function.add shape) (@preconditions.add shape)
| ⟦x, y⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.add, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.add, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mul (shape : S) : is_odifferentiable (@function.mul shape) (@preconditions.mul shape)
| ⟦x, y⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mul, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mul, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sub (shape : S) : is_odifferentiable (@function.sub shape) (@preconditions.sub shape)
| ⟦x, y⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.sub, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.sub, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma div (shape : S) : is_odifferentiable (@function.div shape) (@preconditions.div shape)
| ⟦x, y⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.div, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.div, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sum (shape : S) : is_odifferentiable (@function.sum shape) (@preconditions.sum shape)
| ⟦x⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.sum, dvec.head], prove_differentiable }
| ⟦x⟧ H_pre (n+1) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma gemm (m n p : ℕ) : is_odifferentiable (@function.gemm m n p) (@preconditions.gemm m n p)
| ⟦x, y⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { pose shape := [m, n], start_odiff, dsimp [function.gemm, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { pose shape := [n, p], start_odiff, dsimp [function.gemm, dvec.head, dvec.head2], prove_differentiable }
| ⟦x, y⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mul_add (shape : S) : is_odifferentiable (@function.mul_add shape) (@preconditions.mul_add shape)
| ⟦z, σ, μ⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mul_add, dvec.head, dvec.head2, dvec.head3], prove_differentiable }
| ⟦z, σ, μ⟧ H_pre 1 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mul_add, dvec.head, dvec.head2, dvec.head3], prove_differentiable }
| ⟦z, σ, μ⟧ H_pre 2 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mul_add, dvec.head, dvec.head2, dvec.head3], prove_differentiable }
| ⟦z, σ, μ⟧ H_pre (n+3) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mvn_iso_kl (shape : S) : is_odifferentiable (@function.mvn_iso_kl shape) (@preconditions.mvn_iso_kl shape)
| ⟦μ, σ⟧ H_pre 0 fshape H_fshape_at_idx k H_k := by { start_odiff, dsimp [function.mvn_iso_kl, T.mvn_iso_kl, dvec.head, dvec.head2], prove_differentiable }
| ⟦μ, σ⟧ H_pre 1 fshape H_fshape_at_idx k H_k :=
have H_σ₂ : square σ > 0, from square_pos_of_pos H_pre,
begin
start_odiff, dsimp [function.mvn_iso_kl, T.mvn_iso_kl, dvec.head, dvec.head2],
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-2⁻¹ * T.sum (1 + T.log (square θ₁) + -square μ + -square θ₂))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
end

| ⟦μ, σ⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mvn_iso_empirical_kl (shape : S) : is_odifferentiable (@function.mvn_iso_empirical_kl shape) (@preconditions.mvn_iso_empirical_kl shape) :=
assume xs H_pre idx fshape H_fshape_at_idx k H_k, false.rec _ H_pre

lemma bernoulli_neglogpdf (shape : S) : is_odifferentiable (@function.bernoulli_neglogpdf shape) (@preconditions.bernoulli_neglogpdf shape)
| ⟦p, z⟧ H_pre 0 fshape H_fshape_at_idx k H_k :=
have H_p : p > 0, from H_pre^.left,
have H_1mp : 1 - p > 0, from lt1_alt H_pre^.right,
begin
start_odiff, dsimp [function.bernoulli_neglogpdf, T.bernoulli_neglogpdf, dvec.head, dvec.head2],
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-T.sum (z * T.log θ₁ + (1 + -z) * T.log (1 + -θ₂)))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
end

| ⟦p, z⟧ H_pre 1 fshape H_fshape_at_idx k H_k :=
begin
start_odiff, dsimp [function.bernoulli_neglogpdf, T.bernoulli_neglogpdf, dvec.head, dvec.head2],
apply is_cdifferentiable_binary (λ θ₁ θ₂, k (-T.sum (θ₁ * T.log p + (1 + -θ₂) * T.log (1 + -p)))),
{ dsimp, prove_differentiable },
{ dsimp, prove_differentiable }
end

| ⟦μ, σ⟧ H_pre (n+2) fshape H_fshape_at_idx k H_k := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

end odifferentiable

namespace pullback_correct

def dummy {ishapes : list S} {oshape : S} {f : dvec T ishapes → T oshape} {f_pb : dvec T ishapes → T oshape → T oshape → ℕ → Π fshape, T fshape}
  : pullback_correct f (λ xs, false) f_pb :=
assume xs y H_y g_out idx fshape H_fshape_at_idx H_pre, false.rec _ H_pre

section
open tactic
meta def start_pb_correct : tactic unit :=
do to_expr ```(shape = fshape) >>= λ ty, to_expr ```(eq.symm H_fshape_at_idx^.right) >>= λ val, assertv `H_fshape_eq ty val,
   get_local `H_fshape_eq >>= subst,
   to_expr ```(T shape → ℝ) >>= λ ty, to_expr ```(λ (z : T shape), T.dot z g_out) >>= definev `k ty,
   to_expr ```(∇ k y = g_out) >>= assert `H_k_grad, dsimp, rewrite `certigrad.T.grad_dot₁,
   get_local `H_k_grad >>= rewrite_core reducible tt tt occurrences.all tt,
   get_local `H_y >>= subst,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3],
   try simp,
   dsimp,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3]

end

lemma neg (shape : S) : pullback_correct (@function.neg shape) (@preconditions.neg shape) (@pullback.neg shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear neg, start_pb_correct, rw -T.grad_tmulT,
dunfold function.neg dvec.head, rw (T.grad_neg k), dunfold pullback.neg, simp
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma exp (shape : S) : pullback_correct (@function.exp shape) (@preconditions.exp shape) (@pullback.exp shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear exp, start_pb_correct, rw -T.grad_tmulT,
dunfold function.exp dvec.head, rw (T.grad_exp k), dunfold pullback.exp, simp
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma log (shape : S) : pullback_correct (@function.log shape) (@preconditions.log shape) (@pullback.log shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear log, start_pb_correct, rw -T.grad_tmulT,
dunfold function.log dvec.head, rw (T.grad_log k x H_pre), dunfold pullback.log, simp,
reflexivity
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sqrt (shape : S) : pullback_correct (@function.sqrt shape) (@preconditions.sqrt shape) (@pullback.sqrt shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear sqrt, start_pb_correct, rw -T.grad_tmulT,
dunfold function.sqrt dvec.head, rw (T.grad_sqrt k x H_pre), dunfold pullback.sqrt, simp,
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma scale (α : ℝ) (shape : S) : pullback_correct (@function.scale α shape) (@preconditions.scale α shape) (@pullback.scale α shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear scale, start_pb_correct, rw -T.grad_tmulT,
dunfold function.scale dvec.head, rw (T.grad_scale k), dunfold pullback.scale, simp
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma softplus (shape : S) : pullback_correct (@function.softplus shape) (@preconditions.softplus shape) (@pullback.softplus shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear softplus, start_pb_correct, rw -T.grad_tmulT,
dunfold function.softplus dvec.head, rw (T.grad_softplus k), dunfold pullback.softplus, simp, reflexivity
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sigmoid (shape : S): pullback_correct (@function.sigmoid shape) (@preconditions.sigmoid shape) (@pullback.sigmoid shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear sigmoid, start_pb_correct, rw -T.grad_tmulT,
dunfold function.sigmoid dvec.head, rw (T.grad_sigmoid k), dunfold pullback.sigmoid, simp
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma add (shape : S) : pullback_correct (@function.add shape) (@preconditions.add shape) (@pullback.add shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear add, start_pb_correct, rw -T.grad_tmulT,
dunfold function.add dvec.head dvec.head2, rw (T.grad_add₁ k), dunfold pullback.add, simp
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear add, start_pb_correct, rw -T.grad_tmulT,
dunfold function.add dvec.head dvec.head2, rw (T.grad_add₂ k), dunfold pullback.add, simp
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sub (shape : S) : pullback_correct (@function.sub shape) (@preconditions.sub shape) (@pullback.sub shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear sub, start_pb_correct, rw -T.grad_tmulT,
dunfold function.sub dvec.head dvec.head2, rw (T.grad_sub₁ k), dunfold pullback.sub, simp
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear sub, start_pb_correct, rw -T.grad_tmulT,
dunfold function.sub dvec.head dvec.head2, rw (T.grad_sub₂ k), dunfold pullback.sub, simp
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mul (shape : S) : pullback_correct (@function.mul shape) (@preconditions.mul shape) (@pullback.mul shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear mul, start_pb_correct, rw -T.grad_tmulT,
dunfold function.mul dvec.head dvec.head2, rw (T.grad_mul₁ k), dunfold pullback.mul dvec.head2, simp
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear mul, start_pb_correct, rw -T.grad_tmulT,
dunfold function.mul dvec.head dvec.head2, rw (T.grad_mul₂ k), dunfold pullback.mul dvec.head dvec.head2, simp
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma div (shape : S) : pullback_correct (@function.div shape) (@preconditions.div shape) (@pullback.div shape)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear div, start_pb_correct, rw -T.grad_tmulT,
dunfold function.div dvec.head dvec.head2, rw (T.grad_div₁ k x₁ x₂ H_pre), dunfold pullback.div dvec.head2, simp
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear div, start_pb_correct, rw -T.grad_tmulT,
dunfold function.div dvec.head dvec.head2, rw (T.grad_div₂ k x₁ x₂ H_pre), dunfold pullback.div dvec.head dvec.head2, simp,
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma sum (shape : S) : pullback_correct (@function.sum shape) (@preconditions.sum shape) (@pullback.sum shape)
| ⟦x⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
-- Note: we don't use start_pb_correct because the shapes are non-standard
clear sum,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
dunfold function.sum dvec.get dvec.head dvec.update_at,
simp, dsimp,
dunfold dvec.get dvec.head dvec.update_at,
rw -T.grad_tmulT,
rw T.grad_sum k,
dunfold pullback.sum, simp,
end

| xs y H_y g_out (n+1) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))


lemma gemm (m n p : ℕ) : pullback_correct (@function.gemm m n p) (@preconditions.gemm m n p) (@pullback.gemm m n p)
| ⟦x₁, x₂⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear gemm,
assertv H_fshape_eq : [m, n] = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : T [m, p] → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
dunfold function.gemm dvec.head dvec.head2 dvec.update_at dvec.get,
simp, dsimp,
dunfold dvec.head dvec.head2 dvec.update_at dvec.get,
rw -T.grad_tmulT,
rw T.grad_gemm₁ k,
dunfold pullback.gemm dvec.head2,
simp,
end

| ⟦x₁, x₂⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear gemm,
assertv H_fshape_eq : [n, p] = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : T [m, p] → ℝ := (λ θ, dot g_out θ),
assert H_grad : ∇ k y = g_out,
{ change ∇ (λ θ, dot g_out θ) y = g_out, rw certigrad.T.grad_dot₂ },
rw -H_grad,
subst H_y,
dunfold function.gemm dvec.head dvec.head2 dvec.update_at dvec.get,
simp, dsimp,
dunfold dvec.head dvec.head2 dvec.update_at dvec.get,
rw -T.grad_tmulT,
rw T.grad_gemm₂ k,
dunfold pullback.gemm dvec.head dvec.head2,
simp
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mul_add (shape : S) : pullback_correct (@function.mul_add shape) (@preconditions.mul_add shape) (@pullback.mul_add shape)
| ⟦z, σ, μ⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear mul_add,
start_pb_correct,
rw -T.grad_tmulT,
dunfold function.mul_add dvec.head dvec.head2 dvec.head3,
simplify_grad,
dunfold pullback.mul_add dvec.head2,
simp,
end

| ⟦z, σ, μ⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
begin
clear mul_add,
start_pb_correct,
rw -T.grad_tmulT,
dunfold function.mul_add dvec.head dvec.head2 dvec.head3,
simplify_grad,
dunfold pullback.mul_add dvec.head,
simp
end

| ⟦z, σ, μ⟧ y H_y g_out 2 fshape H_fshape_at_idx H_pre :=
begin
clear mul_add,
start_pb_correct,
rw -T.grad_tmulT,
dunfold function.mul_add dvec.head dvec.head2 dvec.head3,
simplify_grad,
dunfold pullback.mul_add dvec.head,
simp
end

| xs y H_y g_out (n+3) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mvn_iso_kl (shape : S) : pullback_correct (@function.mvn_iso_kl shape) (@preconditions.mvn_iso_kl shape) (@pullback.mvn_iso_kl shape)
| ⟦μ, σ⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
begin
clear mvn_iso_kl,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2 dvec.head3,
simp,
dsimp,
rw -T.grad_tmulT,

dunfold function.mvn_iso_kl T.mvn_iso_kl dvec.head dvec.head2 dvec.head3,
simplify_grad,
dunfold pullback.mvn_iso_kl dvec.head,
simp [T.smul.def, T.const_neg, T.const_mul, T.const_zero, T.const_one, T.const_bit0, T.const_bit1, T.const_inv],
rw T.mul_inv_cancel two_pos,
simp
end

| ⟦μ, σ⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
have H_σ₂ : square σ > 0, from square_pos_of_pos H_pre,

have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * (-2⁻¹ * T.sum (1 + T.log (square θ₀) - square μ - square σ))) σ, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * (-2⁻¹ * T.sum (1 + T.log (square σ) - square μ - square θ₀))) σ, by prove_differentiable,

begin
clear mvn_iso_kl,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2 dvec.head3,
simp,
dsimp,
rw -T.grad_tmulT,
dunfold function.mvn_iso_kl T.mvn_iso_kl dvec.head dvec.head2 dvec.head3,
rw (T.grad_binary (λ θ₁ θ₂, g_out * ((- 2⁻¹) * T.sum (1 + T.log (square θ₁) - square μ - square θ₂))) _ H_diff₁ H_diff₂),
dsimp,
simplify_grad,
dsimp [pullback.mvn_iso_kl, dvec.head, dvec.head2],
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

| ⟦μ, σ⟧ y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

lemma mvn_iso_empirical_kl (shape : S) : pullback_correct (@function.mvn_iso_empirical_kl shape) (@preconditions.mvn_iso_empirical_kl shape) (@pullback.mvn_iso_empirical_kl shape) :=
assume xs y H_y g_out idx fshape H_fshape_at_idx H_pre, false.rec _ H_pre

lemma bernoulli_neglogpdf (shape : S) : pullback_correct (@function.bernoulli_neglogpdf shape) (@preconditions.bernoulli_neglogpdf shape) (@pullback.bernoulli_neglogpdf shape)
| ⟦p, z⟧ y H_y g_out 0 fshape H_fshape_at_idx H_pre :=
have H_p : p > 0, from H_pre^.left,
have H_1mp : 1 - p > 0, from lt1_alt H_pre^.right,
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log θ₀ + (1 - z) * T.log (1 - p))) p, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log p + (1 - z) * T.log (1 - θ₀))) p, by prove_differentiable,

begin
clear bernoulli_neglogpdf,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2 dvec.head3,
simp,
dsimp,
rw -T.grad_tmulT,
dunfold function.bernoulli_neglogpdf T.bernoulli_neglogpdf dvec.head dvec.head2 dvec.head3,
rw T.grad_binary (λ θ₁ θ₂, g_out * - T.sum (z * T.log θ₁ + (1 - z) * T.log (1 - θ₂))) _ H_diff₁ H_diff₂,
dsimp,
note H₁ := H_pre^.left,
note H₂ := lt1_alt H_pre^.right,
simplify_grad,
dsimp [pullback.bernoulli_neglogpdf, dvec.head, dvec.head2],
simp [T.smul.def, const_neg, T.neg_div],
rw [T.mul_div_mul],
simp [T.div_mul_inv],
end

| ⟦p, z⟧ y H_y g_out 1 fshape H_fshape_at_idx H_pre :=
have H_diff₁ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (θ₀ * T.log p + (1 - z) * T.log (1 - p))) z, by prove_differentiable,
have H_diff₂ : is_cdifferentiable (λ (θ₀ : T shape), g_out * -T.sum (z * T.log p + (1 - θ₀) * T.log (1 - p))) z, by prove_differentiable,

begin
clear bernoulli_neglogpdf,
assertv H_fshape_eq : shape = fshape := eq.symm H_fshape_at_idx^.right,
subst H_fshape_eq,
definev k : ℝ → ℝ := λ (x : ℝ), x * g_out,
assertv H_k_grad : ∇ k y = g_out :=  by { dsimp, erw [T.grad_mul₁ id, T.grad_id, one_mul] },
rw -H_k_grad,
subst H_y,
dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2 dvec.head3,
simp,
dsimp,
rw -T.grad_tmulT,
dunfold function.bernoulli_neglogpdf T.bernoulli_neglogpdf dvec.head dvec.head2,
rw T.grad_binary (λ θ₁ θ₂, g_out * - T.sum (θ₁ * T.log p + (1 - θ₂) * T.log (1 - p))) _ H_diff₁ H_diff₂,
dsimp,
simplify_grad,
dsimp [pullback.bernoulli_neglogpdf, dvec.head, dvec.head2],
simp [T.smul.def, const_neg],
end

| xs y H_y g_out (n+2) fshape H_fshape_at_idx H_pre := false.rec _ (at_idx_over H_fshape_at_idx (by tactic.dec_triv))

end pullback_correct

namespace continuous
open tactic

def dummy {ishapes : list S} {oshape : S} {f : dvec T ishapes → T oshape} : continuous f (λ xs, false) :=
assume xs idx ishape H_at_idx H_pre, false.rec _ H_pre

section
open tactic
meta def start_continuous : tactic unit :=
do to_expr ```(shape = ishape) >>= λ ty, to_expr ```(eq.symm H_ishape_at_idx^.right) >>= λ val, assertv `H_ishape_eq ty val,
   get_local `H_ishape_eq >>= subst,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3],
   try simp,
   dsimp,
   dunfold [`dvec.get, `dvec.update_at, `dvec.head, `dvec.head2, `dvec.head3]
end

lemma neg (shape : S) : continuous (@function.neg shape) (@preconditions.neg shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.neg, start_continuous, exact T.continuous_neg }
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma exp (shape : S) : continuous (@function.exp shape) (@preconditions.exp shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.exp, start_continuous, exact T.continuous_exp }
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma log (shape : S) : continuous (@function.log shape) (@preconditions.log shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.log, start_continuous, apply T.continuous_log, exact H_pre }
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma sqrt (shape : S) : continuous (@function.sqrt shape) (@preconditions.sqrt shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.sqrt, start_continuous, apply T.continuous_sqrt, exact H_pre }
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma scale (α : ℝ) (shape : S) : continuous (@function.scale α shape) (@preconditions.scale α shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.scale, start_continuous, apply T.continuous_scale }
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma softplus (shape : S) : continuous (@function.softplus shape) (@preconditions.softplus shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.softplus softplus, start_continuous,
assertv H_pos : 0 < 1 + T.exp x := one_plus_pos exp_pos,
prove_continuous
end

| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma sigmoid (shape : S): continuous (@function.sigmoid shape) (@preconditions.sigmoid shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.sigmoid sigmoid, start_continuous,
assertv H_pos : 1 + T.exp (T.neg x) > 0 := one_plus_pos exp_pos,
assertv H_square_pos : T.square (1 + T.exp (T.neg x)) > 0 := square_pos_of_pos H_pos,
prove_continuous
end

| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma add (shape : S) : continuous (@function.add shape) (@preconditions.add shape)
| ⟦x₁, x₂⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.add, start_continuous, apply continuous_add₂ }
| ⟦x₁, x₂⟧ 1 ishape H_ishape_at_idx H_pre :=
by { dunfold function.add, start_continuous, apply continuous_add₂ }
| ⟦x₁, x₂⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma sub (shape : S) : continuous (@function.sub shape) (@preconditions.sub shape)
| ⟦x₁, x₂⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.sub, start_continuous, apply continuous_sub₁ }
| ⟦x₁, x₂⟧ 1 ishape H_ishape_at_idx H_pre :=
by { dunfold function.sub, start_continuous, apply continuous_sub₂ }
| ⟦x₁, x₂⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma mul (shape : S) : continuous (@function.mul shape) (@preconditions.mul shape)
| ⟦x₁, x₂⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.mul, start_continuous, apply continuous_mul₂ }
| ⟦x₁, x₂⟧ 1 ishape H_ishape_at_idx H_pre :=
by { dunfold function.mul, start_continuous, apply continuous_mul₂ }
| ⟦x₁, x₂⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma div (shape : S) : continuous (@function.div shape) (@preconditions.div shape)
| ⟦x₁, x₂⟧ 0 ishape H_ishape_at_idx H_pre :=
by { dunfold function.div, start_continuous, apply continuous_div₁, exact H_pre }
| ⟦x₁, x₂⟧ 1 ishape H_ishape_at_idx H_pre :=
by { dunfold function.div, start_continuous, apply continuous_div₂, exact H_pre }
| ⟦x₁, x₂⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma sum (shape : S) : continuous (@function.sum shape) (@preconditions.sum shape)
| ⟦x⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.sum sum, start_continuous, apply continuous_sum
end
| ⟦x⟧ (n+1) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma gemm (m n p : ℕ) : continuous (@function.gemm m n p) (@preconditions.gemm m n p)
| ⟦x₁, x₂⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.gemm,
assertv H_ishape_eq : ishape = [m, n] := H_ishape_at_idx^.right, subst H_ishape_eq,
dunfold dvec.get dvec.update_at dvec.head dvec.head2, simp, dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2,
apply continuous_gemm₁
end
| ⟦x₁, x₂⟧ 1 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.gemm,
assertv H_ishape_eq : ishape = [n, p] := H_ishape_at_idx^.right, subst H_ishape_eq,
dunfold dvec.get dvec.update_at dvec.head dvec.head2, simp, dsimp,
dunfold dvec.get dvec.update_at dvec.head dvec.head2,
apply continuous_gemm₂
end
| ⟦x₁, x₂⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma mul_add (shape : S) : continuous (@function.mul_add shape) (@preconditions.mul_add shape)
| ⟦z, σ, μ⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.mul_add, start_continuous, prove_continuous
end
| ⟦z, σ, μ⟧ 1 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.mul_add, start_continuous, prove_continuous
end
| ⟦z, σ, μ⟧ 2 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.mul_add, start_continuous,
apply continuous_add₂
end
| ⟦z, σ, μ⟧ (n+3) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma mvn_iso_kl (shape : S) : continuous (@function.mvn_iso_kl shape) (@preconditions.mvn_iso_kl shape)
| ⟦μ, σ⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.mvn_iso_kl mvn_iso_kl, start_continuous, prove_continuous
end

| ⟦μ, σ⟧ 1 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.mvn_iso_kl mvn_iso_kl, start_continuous,
assertv H_sq_σ : square σ > 0 := square_pos_of_pos H_pre,
apply continuous_binary (λ θ₁ θ₂, - (2⁻¹ * T.sum (1 + (-square μ + (T.log (square θ₁) + -square θ₂))))) σ,
{ dsimp, prove_continuous },
{ dsimp, prove_continuous }
end

| ⟦μ, σ⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

lemma mvn_iso_empirical_kl (shape : S) : continuous (@function.mvn_iso_empirical_kl shape) (@preconditions.mvn_iso_empirical_kl shape)
| ⟦μ, σ, z⟧ idx ishape H_ishape_at_idx H_pre := false.rec _ H_pre

lemma bernoulli_neglogpdf (shape : S) : continuous (@function.bernoulli_neglogpdf shape) (@preconditions.bernoulli_neglogpdf shape)
| ⟦p, x⟧ 0 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.bernoulli_neglogpdf bernoulli_neglogpdf, start_continuous,
assertv H_p : p > 0 := H_pre^.left,
assertv H_q : 1 - p > 0 := lt1_alt H_pre^.right,
apply continuous_binary (λ θ₁ θ₂, - T.sum (x * T.log θ₁ + (1 + -x) * T.log (1 + -θ₂))),
{ dsimp, prove_continuous },
{ dsimp, prove_continuous }
end

| ⟦p, x⟧ 1 ishape H_ishape_at_idx H_pre :=
begin
dunfold function.bernoulli_neglogpdf bernoulli_neglogpdf, start_continuous,
apply continuous_binary (λ θ₁ θ₂, - T.sum (T.log p * θ₁ + T.log (1 + -p) * (1 + -θ₂))),
{ dsimp, prove_continuous },
{ dsimp, prove_continuous }
end

| ⟦p, x⟧ (n+2) ishape H_ishape_at_idx H_pre := false.rec _ (at_idx_over H_ishape_at_idx (by tactic.dec_triv))

end continuous

inductive cwise1 (shape : S) : Type
| neg {} : cwise1
| exp {} : cwise1
| log {} : cwise1
| sqrt {} : cwise1
| scale {} : ℝ → cwise1
| softplus {} : cwise1
| sigmoid {} : cwise1

namespace cwise1

def f {shape : S} : cwise1 shape → function [shape] shape
| neg := @function.neg shape
| exp := @function.exp shape
| log := @function.log shape
| sqrt := @function.sqrt shape
| (scale α) := @function.scale α shape
| softplus := @function.softplus shape
| sigmoid := @function.sigmoid shape

def pre {shape : S} : cwise1 shape → precondition [shape]
| neg := @preconditions.neg shape
| exp := @preconditions.exp shape
| log := @preconditions.log shape
| sqrt := @preconditions.sqrt shape
| (scale α) := @preconditions.scale α shape
| softplus := @preconditions.softplus shape
| sigmoid := @preconditions.sigmoid shape


def pb {shape : S} : cwise1 shape → pullback [shape] shape
| neg := @pullback.neg shape
| exp := @pullback.exp shape
| log := @pullback.log shape
| sqrt := @pullback.sqrt shape
| (scale α) := @pullback.scale α shape
| softplus := @pullback.softplus shape
| sigmoid := @pullback.sigmoid shape

def is_odiff {shape : S} : Π (c1 : cwise1 shape), is_odifferentiable c1^.f c1^.pre
| neg := @odifferentiable.neg shape
| exp := @odifferentiable.exp shape
| log := @odifferentiable.log shape
| sqrt := @odifferentiable.sqrt shape
| (scale α) := @odifferentiable.scale α shape
| softplus := @odifferentiable.softplus shape
| sigmoid := @odifferentiable.sigmoid shape

def pb_correct {shape : S} : Π (c1 : cwise1 shape), pullback_correct c1^.f c1^.pre c1^.pb
| neg := @pullback_correct.neg shape
| exp := @pullback_correct.exp shape
| log := @pullback_correct.log shape
| sqrt := @pullback_correct.sqrt shape
| (scale α) := @pullback_correct.scale α shape
| softplus := @pullback_correct.softplus shape
| sigmoid := @pullback_correct.sigmoid shape

def cont {shape : S} : Π (c1 : cwise1 shape), continuous c1^.f c1^.pre
| neg := @continuous.neg shape
| exp := @continuous.exp shape
| log := @continuous.log shape
| sqrt := @continuous.sqrt shape
| (scale α) := @continuous.scale α shape
| softplus := @continuous.softplus shape
| sigmoid := @continuous.sigmoid shape

end cwise1

inductive cwise2 (shape : S) : Type
| add {} : cwise2
| sub {} : cwise2
| mul {} : cwise2
| div {} : cwise2

namespace cwise2

def f {shape : S} : cwise2 shape → function [shape, shape] shape
| add := @function.add shape
| sub := @function.sub shape
| mul := @function.mul shape
| div := @function.div shape

def pre {shape : S} : cwise2 shape → precondition [shape, shape]
| add := @preconditions.add shape
| sub := @preconditions.sub shape
| mul := @preconditions.mul shape
| div := @preconditions.div shape

def pb {shape : S} : cwise2 shape → pullback [shape, shape] shape
| add := @pullback.add shape
| sub := @pullback.sub shape
| mul := @pullback.mul shape
| div := @pullback.div shape

def is_odiff {shape : S} : Π (c2 : cwise2 shape), is_odifferentiable c2^.f c2^.pre
| add := @odifferentiable.add shape
| sub := @odifferentiable.sub shape
| mul := @odifferentiable.mul shape
| div := @odifferentiable.div shape

def pb_correct {shape : S} : Π (c2 : cwise2 shape), pullback_correct c2^.f c2^.pre c2^.pb
| add := @pullback_correct.add shape
| sub := @pullback_correct.sub shape
| mul := @pullback_correct.mul shape
| div := @pullback_correct.div shape

def cont {shape : S} : Π (c2 : cwise2 shape), continuous c2^.f c2^.pre
| add := @continuous.add shape
| sub := @continuous.sub shape
| mul := @continuous.mul shape
| div := @continuous.div shape

end cwise2

inductive special : list S → S → Type
| sum : Π (shape : S), special [shape] []
| gemv : Π (m n : ℕ), special [[m, n], [n]] [m]
| gemm : Π (m n p : ℕ), special [[m, n], [n, p]] [m, p]
| mvn_iso_logpdf : Π (shape : S), special [shape, shape, shape] []
| mvn_iso_std_logpdf : Π (shape : S), special [shape] []
| get_col : Π (m n cidx : ℕ), special [[m, n]] [m]
| get_col_range : Π (m n ncols : ℕ), special [[m, n], []] [m, ncols]
| replicate_col : Π (m n : ℕ), special [[m]] [m, n]
| mul_add : Π (shape : S), special [shape, shape, shape] shape
| mvn_iso_kl : Π (shape : S), special [shape, shape] []
| bernoulli_neglogpdf : Π (shape : S), special [shape, shape] []

namespace special

def f : Π {shapes : list S} {shape : S}, special shapes shape → function shapes shape
| ._ ._ (@sum shape) := @function.sum shape
| ._ ._ (@gemv m n)  := @function.gemv m n
| ._ ._ (@gemm m n p) := @function.gemm m n p
| ._ ._ (@mvn_iso_logpdf shape) := @function.mvn_iso_logpdf shape
| ._ ._ (@mvn_iso_std_logpdf shape) := @function.mvn_iso_std_logpdf shape
| ._ ._ (@get_col m n cidx) := @function.get_col m n cidx
| ._ ._ (@get_col_range m n ncols) := @function.get_col_range m n ncols
| ._ ._ (@replicate_col m n) := @function.replicate_col m n
| ._ ._ (@mul_add shape) := @function.mul_add shape
| ._ ._ (@mvn_iso_kl shape) := @function.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @function.bernoulli_neglogpdf shape

def pre : Π {shapes : list S} {shape : S}, special shapes shape → precondition shapes
| ._ ._ (@sum shape) := preconditions.sum
| ._ ._ (@gemv m n)  := preconditions.gemv
| ._ ._ (@gemm m n p) := preconditions.gemm
| ._ ._ (@mvn_iso_logpdf shape) := λ xs, false -- Note: mvn_iso_logpdf not claiming to be differentiable
| ._ ._ (@mvn_iso_std_logpdf shape) := λ xs, false -- Note: mvn_iso_logpdf not claiming to be differentiable
| ._ ._ (@get_col m n cidx) := λ xs, false
| ._ ._ (@get_col_range m n ncols) := λ xs, false
| ._ ._ (@replicate_col m n) := λ xs, false
| ._ ._ (@mul_add shape) := λ xs, true
| ._ ._ (@mvn_iso_kl shape) := @preconditions.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @preconditions.bernoulli_neglogpdf shape

def pb : Π {shapes : list S} {shape : S}, special shapes shape → pullback shapes shape
| ._ ._ (@sum shape) := @pullback.sum shape
| ._ ._ (@gemv m n)  := pullback.error "gemv"
| ._ ._ (@gemm m n p) := @pullback.gemm m n p
| ._ ._ (@mvn_iso_logpdf shape) := pullback.error "mvn_iso_logpdf"
| ._ ._ (@mvn_iso_std_logpdf shape) := pullback.error "mvn_iso_std_logpdf"
| ._ ._ (@get_col m n cidx) := pullback.error "get_col"
| ._ ._ (@get_col_range m n ncols) := pullback.serror
| ._ ._ (@replicate_col m n) := @pullback.replicate_col m n
| ._ ._ (@mul_add shape) := @pullback.mul_add shape
| ._ ._ (@mvn_iso_kl shape) := @pullback.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @pullback.bernoulli_neglogpdf shape

def is_odiff : Π {shapes : list S} {shape : S} (sp : special shapes shape), is_odifferentiable sp^.f sp^.pre
| ._ ._ (@sum shape) := @odifferentiable.sum shape
| ._ ._ (@gemv m n)  := odifferentiable.dummy
| ._ ._ (@gemm m n p) := @odifferentiable.gemm m n p
| ._ ._ (@mvn_iso_logpdf shape) := odifferentiable.dummy
| ._ ._ (@mvn_iso_std_logpdf shape) := odifferentiable.dummy
| ._ ._ (@get_col m n cidx) := odifferentiable.dummy
| ._ ._ (@get_col_range m n ncols) := odifferentiable.dummy
| ._ ._ (@replicate_col m n) := odifferentiable.dummy
| ._ ._ (@mul_add shape) := @odifferentiable.mul_add shape
| ._ ._ (@mvn_iso_kl shape) := @odifferentiable.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @odifferentiable.bernoulli_neglogpdf shape

def pb_correct : Π {shapes : list S} {shape : S} (sp : special shapes shape), pullback_correct sp^.f sp^.pre sp^.pb
| ._ ._ (@sum shape) := @pullback_correct.sum shape
| ._ ._ (@gemv m n)  := pullback_correct.dummy
| ._ ._ (@gemm m n p) := @pullback_correct.gemm m n p
| ._ ._ (@mvn_iso_logpdf shape) := pullback_correct.dummy
| ._ ._ (@mvn_iso_std_logpdf shape) := pullback_correct.dummy
| ._ ._ (@get_col m n cidx) := pullback_correct.dummy
| ._ ._ (@get_col_range m n ncols) := pullback_correct.dummy
| ._ ._ (@replicate_col m n) := pullback_correct.dummy
| ._ ._ (@mul_add shape) := @pullback_correct.mul_add shape
| ._ ._ (@mvn_iso_kl shape) := @pullback_correct.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @pullback_correct.bernoulli_neglogpdf shape

def cont : Π {shapes : list S} {shape : S} (sp : special shapes shape), continuous sp^.f sp^.pre
| ._ ._ (@sum shape) := @continuous.sum shape
| ._ ._ (@gemv m n)  := continuous.dummy
| ._ ._ (@gemm m n p) := @continuous.gemm m n p
| ._ ._ (@mvn_iso_logpdf shape) := continuous.dummy
| ._ ._ (@mvn_iso_std_logpdf shape) := continuous.dummy
| ._ ._ (@get_col m n cidx) := continuous.dummy
| ._ ._ (@get_col_range m n ncols) := continuous.dummy
| ._ ._ (@replicate_col m n) := continuous.dummy
| ._ ._ (@mul_add shape) := @continuous.mul_add shape
| ._ ._ (@mvn_iso_kl shape) := @continuous.mvn_iso_kl shape
| ._ ._ (@bernoulli_neglogpdf shape) := @continuous.bernoulli_neglogpdf shape

end special

inductive op : Π (ishapes : list S) (oshape : S),  Type
| const : Π {shape : S}, T shape → op [] shape
| unary : Π {shape : S}, cwise1 shape → op [shape] shape
| binary : Π {shape : S}, cwise2 shape → op [shape, shape] shape
| special : Π {shapes : list S} {shape : S}, special shapes shape → op shapes shape
-- Note: we keep this separate because we use it in a program transformation
-- We group the "special" ones just to avoid needing to pattern match on all them on dead branches
| mvn_iso_empirical_kl : Π (shape : S), op [shape, shape, shape] []

namespace op

def f : Π {ishapes : list S} {oshape : S}, op ishapes oshape → function ishapes oshape
| ._ ._ (@const shape x)    := λ xs, x
| ._ ._ (@unary shape c1)   := c1^.f
| ._ ._ (@binary shape c2)  := c2^.f
| ._ ._ (@special shapes shape sp) := sp^.f
| ._ ._ (@mvn_iso_empirical_kl shape) := @function.mvn_iso_empirical_kl shape

def pre : Π {ishapes : list S} {oshape : S}, op ishapes oshape → precondition ishapes
| ._ ._ (@const shape x)    := λ xs, false
| ._ ._ (@unary shape c1)   := c1^.pre
| ._ ._ (@binary shape c2)  := c2^.pre
| ._ ._ (@special shapes shape sp) := sp^.pre
| ._ ._ (@mvn_iso_empirical_kl shape) := @preconditions.mvn_iso_empirical_kl shape

def pb : Π {ishapes : list S} {oshape : S}, op ishapes oshape → pullback ishapes oshape
| ._ ._ (@const shape x)   := pullback.error "const"
| ._ ._ (@unary shape c1)   := c1^.pb
| ._ ._ (@binary shape c2)  := c2^.pb
| ._ ._ (@special shapes shape sp) := sp^.pb
| ._ ._ (@mvn_iso_empirical_kl shape) := @pullback.mvn_iso_empirical_kl shape

def is_odiff : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), is_odifferentiable op^.f op^.pre
| ._ ._ (@const shape x)   := odifferentiable.dummy
| ._ ._ (@unary shape c1)   := c1^.is_odiff
| ._ ._ (@binary shape c2)  := c2^.is_odiff
| ._ ._ (@special shapes shape sp) := sp^.is_odiff
| ._ ._ (@mvn_iso_empirical_kl shape) := odifferentiable.mvn_iso_empirical_kl shape

def pb_correct : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), pullback_correct op^.f op^.pre op^.pb
| ._ ._ (@const shape x)    := pullback_correct.dummy
| ._ ._ (@unary shape c1)   := c1^.pb_correct
| ._ ._ (@binary shape c2)  := c2^.pb_correct
| ._ ._ (@special shapes shape sp) := sp^.pb_correct
| ._ ._ (@mvn_iso_empirical_kl shape) := pullback_correct.mvn_iso_empirical_kl shape

def cont : Π {ishapes : list S} {oshape : S} (op : op ishapes oshape), continuous op^.f op^.pre
| ._ ._ (@const shape x)    := continuous.dummy
| ._ ._ (@unary shape c1)   := c1^.cont
| ._ ._ (@binary shape c2)  := c2^.cont
| ._ ._ (@special shapes shape sp) := sp^.cont
| ._ ._ (@mvn_iso_empirical_kl shape) := continuous.mvn_iso_empirical_kl shape

end op
end det

lemma mvn_iso_kl_pre {shape : S} (xs : dvec T [shape, shape]) :
  det.op.pre (det.op.special (det.special.mvn_iso_kl shape)) xs = (dvec.head2 xs > 0) := rfl

end certigrad
