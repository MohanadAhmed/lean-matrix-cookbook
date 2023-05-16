import data.matrix.basic
import data.matrix.notation
import data.complex.basic

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open matrix
open_locale matrix big_operators

lemma coerce_to_matrices
  (A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
  (row u) ⬝ A ⬝ (col v) = ↑(u ⬝ᵥ (A.mul_vec v)) :=
begin
  -- Type Checks : But Need to prove it
  sorry,
end

lemma coercre_to_scalars
  (A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
  (row u) ⬝ A ⬝ (col v) = (u ⬝ᵥ (A.mul_vec v)) :=
begin
  -- Does NOT Type Check
  -- Lean is not happy!!
end

lemma go_to_scalars (z: ℂ):
  (↑z: matrix unit unit ℂ) = ↑z := 
begin
  refl,
end

lemma smul_row_col_mul
(A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
  (col u) ⬝ (row u ⬝ A ⬝ col v)  = 
  (u ⬝ᵥ (A.mul_vec v)) • (col u) :=
begin
  funext k m, rw mul_apply, 
  simp only [fintype.univ_punit, col_apply, finset.sum_singleton, 
  pi.smul_apply, algebra.id.smul_eq_mul],
  rw dot_product_mul_vec,
  rw dot_product, 
  rw ← punit_eq_star m,
  by_cases huk: (u k) = 0, {
    rw huk, rw zero_mul, rw mul_zero,
  },
  rw mul_comm _ (u k), rw mul_right_inj' huk, rw mul_apply,
  conv_lhs {
    apply_congr, skip, rw mul_apply, rw col_apply,
  }, 
  conv_rhs {
    apply_congr, skip, rw vec_mul, rw dot_product,
  },  refl,
end

lemma smul_row_col_mul_add_scalar
(A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
  (col u) ⬝ (row u ⬝ A ⬝ col v)  = 
  (u ⬝ᵥ (A.mul_vec v)) • (col u) :=
begin
  funext k m, rw mul_apply, 
  simp only [fintype.univ_punit, col_apply, finset.sum_singleton, 
  pi.smul_apply, algebra.id.smul_eq_mul],
  rw dot_product_mul_vec,
  rw dot_product, 
  rw ← punit_eq_star m,
  by_cases huk: (u k) = 0, {
    rw huk, rw zero_mul, rw mul_zero,
  },
  rw mul_comm _ (u k), rw mul_right_inj' huk, rw mul_apply,
  conv_lhs {
    apply_congr, skip, rw mul_apply, rw col_apply,
  }, 
  conv_rhs {
    apply_congr, skip, rw vec_mul, rw dot_product,
  },  refl,
end

lemma row_mul_col_inv
(A: matrix n n ℂ)(b: n → ℂ)(c: n → ℂ):
  col b ⬝ (1 + row c ⬝ A ⬝ col b) ⬝ row c = 
  (1 + c ⬝ᵥ A.mul_vec b) • col b ⬝ row c := 
begin
  funext m k,
  rw pi.smul_apply, rw pi.smul_apply,
  rw mul_apply,
  simp only [fintype.univ_punit, row_apply, finset.sum_singleton, 
    algebra.id.smul_eq_mul], 
  rw mul_apply,
  simp only [fintype.univ_punit, row_apply, finset.sum_singleton, 
    algebra.id.smul_eq_mul], 
  rw col_apply, rw pi.add_apply, rw pi.add_apply,
  rw one_apply_eq, 
  -- set α := row c ⬝ A,
  
  rw mul_apply,
  simp only [col_apply], 
  rw mul_apply, conv_rhs {
    congr, skip,
    conv {
      apply_congr, skip,
      rw col_apply, rw row_apply,
    },
    rw fintype.univ_punit, rw finset.sum_singleton,
  },
  
  conv_lhs {
    rw mul_assoc, rw mul_comm _ (c k), rw ← mul_assoc,
    congr,skip, congr, skip, apply_congr, skip,
    rw matrix.mul, dsimp, rw dot_product,
    dsimp, 
  }, 

  rw mul_comm, by_cases h: (b m * c k = 0), {
    rw h, rw mul_zero,rw mul_zero,
  },
  rw ← ne.def at h,
  rw mul_left_inj' h,
  -- conv_lhs {
  --   congr, congr, skip, congr, skip, 
  --   apply_congr, skip, rw mul_apply,  conv {
  --     congr, congr, skip, 
  --   },
  -- }, 
end

