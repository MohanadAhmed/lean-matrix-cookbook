import data.matrix.basic
import data.matrix.notation
import data.complex.basic
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse
import data.fintype.big_operators

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open matrix
open_locale matrix big_operators

-- lemma coerce_to_matrices
--   (A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
--   (row u) ⬝ A ⬝ (col v) = ↑(u ⬝ᵥ (A.mul_vec v)) :=
-- begin
--   -- Type Checks : But Need to prove it
--   sorry,
-- end

-- lemma coercre_to_scalars
--   (A: matrix n n ℂ)(u: n → ℂ)(v: n → ℂ):
--   (row u) ⬝ A ⬝ (col v) = (u ⬝ᵥ (A.mul_vec v)) :=
-- begin
--   -- Does NOT Type Check
--   -- Lean is not happy!!
-- end

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
  simp only [add_right_inj], rw dot_product_mul_vec,
  rw dot_product, conv_rhs {
    apply_congr, skip, rw vec_mul, rw dot_product,
  }, 
end

.

lemma lemma_coercion_to_scalars
(u: n → ℂ)(v: n → ℂ)(s: ℂ)(sm: matrix unit unit ℂ) (h: s = (sm punit.star punit.star)):
  (col u ⬝ sm ⬝ row v)  = s • (col u ⬝ row v) :=
begin
  funext m k,
  rw mul_apply, rw fintype.univ_punit, rw finset.sum_singleton, rw row_apply, 
  rw mul_apply, rw fintype.univ_punit, rw finset.sum_singleton, rw col_apply,
  rw ← h,
  rw pi.smul_apply,
  rw pi.smul_apply, simp only [algebra.id.smul_eq_mul], rw mul_apply, 
  rw fintype.univ_punit, rw finset.sum_singleton, rw row_apply, rw col_apply, 
  ring,
end

lemma row_mul_mat_mul_col (A : matrix m m ℂ) (b c : m → ℂ) :
  c ⬝ᵥ A.mul_vec b = (row c ⬝ A ⬝ col b) punit.star punit.star:= 
begin
  rw mul_apply,
  rw dot_product,
  conv_rhs {
    apply_congr, skip, rw col_apply, 
    rw mul_apply, conv {
      congr, apply_congr, skip, rw row_apply,
    }, rw finset.sum_mul,
  },
  
  conv_lhs {
    apply_congr, skip, rw mul_vec, dsimp, rw dot_product,
    rw finset.mul_sum, conv {
      apply_congr, skip, rw ← mul_assoc,
    } ,
  } ,
  apply finset.sum_comm,
end

lemma row_mul_col_inv'
(A: matrix n n ℂ)(b: n → ℂ)(c: n → ℂ):
  col b ⬝ (1 + row c ⬝ A ⬝ col b) ⬝ row c = 
  (1 + c ⬝ᵥ A.mul_vec b) • col b ⬝ row c := 
begin
  have h: (1 + c ⬝ᵥ A.mul_vec b) = (1 + row c ⬝ A ⬝ col b)  punit.star punit.star, {
    rw pi.add_apply,
    rw pi.add_apply,rw one_apply_eq,
    simp only [add_right_inj],
    apply row_mul_mat_mul_col,
  },
  apply lemma_coercion_to_scalars b c, exact h,
end

lemma one_add_row_mul_mat_col_inv (A : matrix m m ℂ)
  (b c : m → ℂ) (habc: (1 + c ⬝ᵥ A.mul_vec b) ≠ 0):
  (1 + c ⬝ᵥ A.mul_vec b)⁻¹ =
    (1 + row c ⬝ A ⬝ col b)⁻¹ punit.star punit.star :=
begin
  -- set β := (1 + row c ⬝ A⁻¹ ⬝ col b)⁻¹ punit.star punit.star,
  set γ := 1 + c ⬝ᵥ A.mul_vec b, 
  rw ← mul_left_inj' habc, rw inv_mul_cancel habc,
  rw mul_comm, rw inv_def, rw adjugate,
  simp only [
    det_unique, punit.default_eq_star, pi.add_apply, 
    one_apply_eq, ring.inverse_eq_inv', of_apply, pi.smul_apply,
    cramer_subsingleton_apply, pi.single_eq_same, 
    algebra.id.smul_eq_mul, mul_one
  ],
  rw ← row_mul_mat_mul_col, symmetry', apply mul_inv_cancel, exact habc,
end


lemma eq_159 (A : matrix m m ℂ) (B : matrix m n ℂ) (C : matrix n m ℂ)
  {hA: is_unit A.det} {h: is_unit (1 + C ⬝ A⁻¹ ⬝ B).det} :
  (A + B⬝C)⁻¹ = A⁻¹ - A⁻¹⬝B⬝(1 + C⬝A⁻¹⬝B)⁻¹⬝C⬝A⁻¹ :=
begin
  sorry,
end

lemma eq_160 (A : matrix m m ℂ) {hA: is_unit A.det} (b c : m → ℂ) 
  (habc: 1 + c ⬝ᵥ A⁻¹.mul_vec b ≠ 0):
  (A + col b ⬝ row c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ (A⁻¹.mul_vec b))⁻¹ • (A⁻¹⬝(col b ⬝ row c)⬝A⁻¹) :=
begin
  rw eq_159, simp only [sub_right_inj],
  apply_fun (λ x, x⬝A),  dsimp, rw nonsing_inv_mul_cancel_right,
  rw ← matrix.smul_mul, rw nonsing_inv_mul_cancel_right,
  apply_fun (λ x, A⬝x),  dsimp, rw ← matrix.mul_smul,
  repeat {rw matrix.mul_assoc A⁻¹},
  rw mul_nonsing_inv_cancel_left,
  rw mul_nonsing_inv_cancel_left,
  assumption',
  rw lemma_coercion_to_scalars,
  apply one_add_row_mul_mat_col_inv, assumption',
  sorry,
end
