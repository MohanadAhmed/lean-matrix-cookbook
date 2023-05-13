import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import data.complex.basic

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]
open matrix
open_locale matrix big_operators

lemma eq_157 (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ) 
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + V ⬝ A⁻¹ ⬝ U).det}:
  (A + U⬝B⬝V)⁻¹ = A⁻¹ - A⁻¹⬝U⬝(B⁻¹+V⬝A⁻¹⬝U)⁻¹⬝V ⬝ A⁻¹ := 
begin
  apply inv_eq_right_inv,
  rw matrix.add_mul,
  rw matrix.mul_sub, rw mul_nonsing_inv,
  repeat {rw matrix.mul_assoc A⁻¹ _ _},
  rw mul_nonsing_inv_cancel_left,
  set Q := (B⁻¹+V⬝A⁻¹⬝U),
  rw matrix.mul_sub,
  rw sub_add_sub_comm,
  rw matrix.mul_assoc _ Q⁻¹ _,  
  rw matrix.mul_assoc U (Q⁻¹⬝V) _,
  have : U ⬝ B ⬝ V ⬝ (A⁻¹ ⬝ (U ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹))) 
    = (U ⬝ B ⬝ V ⬝ A⁻¹ ⬝ U) ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹), {
      rw ← matrix.mul_assoc _ A⁻¹ _,
      rw ← matrix.mul_assoc _ U _,
  }, rw this, clear this,
  rw ← matrix.add_mul,
  nth_rewrite 1 ← matrix.mul_one U,
  rw ←  mul_nonsing_inv B, rw ← matrix.mul_assoc _ B _,
  repeat {rw matrix.mul_assoc (U⬝B) _ _},
  rw ← matrix.mul_add (U⬝B) _ _,
  rw matrix.mul_assoc (U⬝B),
  rw matrix.mul_assoc Q⁻¹,
  rw mul_nonsing_inv_cancel_left, simp only [add_sub_cancel],
  assumption',
end

lemma eq_156 (A : matrix m m ℂ) (B : matrix n n ℂ) (C : matrix m n ℂ)
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + Cᵀ ⬝ A⁻¹ ⬝ C).det}: 
  (A + C⬝B⬝Cᵀ)⁻¹ = A⁻¹ - A⁻¹⬝C⬝(B⁻¹+Cᵀ⬝A⁻¹⬝C)⁻¹⬝Cᵀ ⬝ A⁻¹ :=  
begin
  apply eq_157,
  assumption',
end

noncomputable lemma invertible_of_pos_def {A : matrix m m ℂ} {hA: matrix.pos_def A}:
  invertible A := begin
  cases hA with hAH hA_pos,
  unfold is_hermitian at *,
  
-- apply invertible_of_is_unit_det,
end

lemma is_unit_if_pos_def {A : matrix m m ℂ} {hA: matrix.pos_def A}: 
  is_unit A.det := 
begin
  apply is_unit_det_of_invertible,
end

lemma rank_up_pos_def_is_pos_def 
  (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  [invertible P] [invertible R]
  {hP: matrix.pos_def P} {hR: matrix.pos_def R} :
  matrix.pos_def (B⬝P⬝Bᴴ + R) := 
begin
  cases hP with hPH hP_pos,
  cases hR with hRH hR_pos,

  split,
  -- (B ⬝ P ⬝ Bᴴ + R).is_hermitian
  unfold is_hermitian at *, rw conj_transpose_add,
  rw conj_transpose_mul,
  rw conj_transpose_mul, rw conj_transpose_conj_transpose,
  rw [hPH, hRH], rw ← matrix.mul_assoc,

  rintros x hx, simp only [is_R_or_C.re_to_complex],
  -- 0 < ⇑is_R_or_C.re (star x ⬝ᵥ (B ⬝ P ⬝ Bᴴ + R).mul_vec x)
  rw add_mul_vec,
  rw ← mul_vec_mul_vec,
  rw dot_product_add,
  rw complex.add_re,
  replace hR_pos := hR_pos x hx, 
  rw is_R_or_C.re_to_complex at hR_pos,

  replace hP_pos := hP_pos (Bᴴ.mul_vec x), 
  rw is_R_or_C.re_to_complex at hP_pos,

  rw dot_product_mul_vec,
  nth_rewrite 0  ← transpose_transpose B,
  rw ← vec_mul_mul_vec Bᵀ P (star x),
  have : star(Bᴴ.mul_vec x) = Bᵀ.mul_vec (star x), {
    rw star_mul_vec, rw conj_transpose_conj_transpose,
    funext k, rw mul_vec, rw vec_mul, dsimp, rw dot_product,
    rw dot_product, conv_rhs {
      apply_congr, skip, rw transpose_apply, rw mul_comm,
    },
  }, rw ← this, rw ← dot_product_mul_vec,
  
  by_cases hBHx: (Bᴴ.mul_vec x = 0 ), {
    rw hBHx, rw mul_vec_zero, rw dot_product_zero,
    simp only [complex.zero_re, zero_add],
    exact hR_pos,
  }, {
    exact add_pos (hP_pos hBHx) hR_pos,
  },
end

lemma eq_158 (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  [invertible P] [invertible R]
  {hP: matrix.pos_def P} {hR: matrix.pos_def R} : 
  (P⁻¹ + Bᵀ⬝R⁻¹⬝B)⁻¹⬝Bᵀ⬝R⁻¹ = P⬝Bᵀ⬝(B⬝P⬝Bᵀ + R)⁻¹ := 
begin
  -- This is equation 80:
  -- http://www.stat.columbia.edu/~liam/teaching/neurostat-spr12/papers/hmm/KF-welling-notes.pdf

  rw add_comm _ R,
  -- rw eq_156 R P B,  --set α := P⁻¹ + Bᵀ ⬝ R⁻¹ ⬝ B,
  nth_rewrite 1 ← transpose_transpose B,
  rw eq_156 P⁻¹ R⁻¹ Bᵀ,  --set α := P⁻¹ + Bᵀ ⬝ R⁻¹ ⬝ B,
  -- have invP: invertible P, by sorry,
  -- have invR: invertible R, by sorry,
  simp only [inv_inv_of_invertible, transpose_transpose],
  apply_fun (matrix.mul P⁻¹), rw ←  matrix.mul_assoc P⁻¹ _ _,
  repeat {rw ← matrix.mul_assoc},  
  repeat {rw matrix.mul_sub},
  repeat {rw ← matrix.mul_assoc},
  rw nonsing_inv_mul, repeat {rw matrix.one_mul}, repeat {rw matrix.mul_sub},
  repeat {rw matrix.sub_mul}, repeat {rw matrix.one_mul},
  rw sub_eq_iff_eq_add,
  apply_fun (λ a, a⬝R), dsimp,
  rw matrix.add_mul,
  repeat {rw nonsing_inv_mul_cancel_right},
  rw matrix.mul_assoc (Bᵀ ⬝ (R + B ⬝ P ⬝ Bᵀ)⁻¹),
  rw matrix.mul_assoc (Bᵀ ⬝ (R + B ⬝ P ⬝ Bᵀ)⁻¹),

  -- nth_rewrite 0 ← matrix.mul_one (Bᵀ ⬝ (R + B ⬝ P ⬝ Bᵀ)⁻¹),
  rw ←  matrix.mul_add (Bᵀ ⬝ (R + B ⬝ P ⬝ Bᵀ)⁻¹), rw nonsing_inv_mul_cancel_right,

end
-- Checks

section randomstuff
variables (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ)
#check A
#check U⬝B⬝V
end randomstuff