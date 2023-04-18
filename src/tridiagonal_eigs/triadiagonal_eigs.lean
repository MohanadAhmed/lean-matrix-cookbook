/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
import data.complex.basic
import data.real.basic
import data.matrix.basic
import data.matrix.notation
import data.fin.vec_notation

import linear_algebra.matrix.hermitian
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.adjugate
import linear_algebra.eigenspace

/-
Eq 12 and other eigenvalue related stuff in the lean-matrix-cookbook were avoided
probably because of the rather annoying manner of dealing with eigenvalues in mathlib
(just guessing here). As preparation to deal with that I am going to try to formalize
the eigenvalues of a tridiagonal toeplitz matrices, which are known in closed form.
They are sufficiently non-trivial that they will exercise some mathlib muscles and 
force me to learn some of the stuff I don't know!!!
Useful References:
Stanford CME 302 Numerical Linear Algebra Notes (Gene Golub 2005/2006): Lecture 14
https://www.stat.uchicago.edu/~lekheng/courses/302/notes14.pdf

https://www.math.kent.edu/~reichel/publications/toep3.pdf

https://math.stackexchange.com/questions/955168/how-to-find-the-eigenvalues-of-tridiagonal-toeplitz-matrix

https://drive.google.com/file/d/1S7raWuA9xwLHk28-P4L5jjZWMGTmfe7b/view

-/
namespace useful_idents
variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[comm_ring R]

lemma vecn_eq_vecn_iff
  {w: n → R }
  {v: n → R }
  : w = v ↔  (∀ k : n, w k = v k) := 
begin
  split,
  
  intros h k,
  apply_fun (λ z, (z k)) at h, assumption,

  intro hcomp,
  funext k, specialize hcomp k, assumption,
end
end useful_idents

namespace tridiagonal_eigs
open useful_idents
open_locale matrix big_operators

variables {n: Type*}[fintype n][decidable_eq n]
variables a b c : ℝ

def T (n: ℕ) (α β γ: ℝ) : matrix (fin n) (fin n) ℝ := 
  matrix.of (
    λ i j : (fin n) , 
      if i = j then α else (
        ite ((j + 1) = i) β 0
      )
    )

def T3 := (T 3)

-- lemma trash (v: (fin 4) → ℝ) : (T4 2 0 0).mul_vec v = 2•v := begin
--   rw T4, rw T, 
--   -- simp only [coe_coe, one_mul, if_t_t, nsmul_eq_mul, 
--   -- nat.cast_bit0, algebra_map.coe_one],
--   -- simp only [coe_coe],
--   -- rw nsmul_eq_mul,
--   rw vecn_eq_vecn_iff,
--   simp only [one_mul, if_t_t, pi.coe_nat, nat.cast_bit0, algebra_map.coe_one, pi.mul_apply],
--   intro k,
--   -- rw matrix.of_apply,
--   rw coe_fn, 
--   rw matrix.of, 
--   simp only [coe_coe, nsmul_eq_mul, pi.coe_nat, nat.cast_bit0, algebra_map.coe_one, pi.mul_apply],
--   funext i,
--   sorry,
-- end

lemma trash3_diag (v: (fin 3) → ℝ) : (T3 2 0 0) = 
  matrix.diagonal (λ i : (fin 3), 2) 
  := begin
  unfold matrix.diagonal,
  rw T3, rw T,
end

end tridiagonal_eigs