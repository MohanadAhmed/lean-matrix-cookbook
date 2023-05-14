import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
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

lemma eq_156_hermitianized (A : matrix m m ℂ) (B : matrix n n ℂ) (C : matrix m n ℂ)
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + Cᴴ ⬝ A⁻¹ ⬝ C).det}: 
  (A + C⬝B⬝Cᴴ)⁻¹ = A⁻¹ - A⁻¹⬝C⬝(B⁻¹+Cᴴ⬝A⁻¹⬝C)⁻¹⬝Cᴴ ⬝ A⁻¹ :=  
begin
  apply eq_157,
  assumption',
end

lemma is_unit_of_pos_def {A : matrix m m ℂ} (hA: matrix.pos_def A): 
  is_unit A.det := 
begin
  rw is_unit_iff_ne_zero,
  apply ne.symm,
  cases hA with hAH hpos,
  rw is_hermitian.det_eq_prod_eigenvalues hAH,
  norm_cast,
  rw ← ne.def,
  apply ne_of_lt,
  apply finset.prod_pos,
  intros i _,
  rw hAH.eigenvalues_eq,
  apply hpos _ (λ h, _),
  have h_det : (hAH.eigenvector_matrix)ᵀ.det = 0,
    from matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j),
  simpa only [h_det, not_is_unit_zero] using
    is_unit_det_of_invertible hAH.eigenvector_matrixᵀ,
end

noncomputable lemma invertible_of_pos_def {A : matrix m m ℂ} {hA: matrix.pos_def A}:
  invertible A := 
begin  
  apply invertible_of_is_unit_det,
  apply is_unit_of_pos_def,
  exact hA,
end

lemma A_add_B_P_Bt_pos_if_A_pos_B_pos 
  (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  -- [invertible P] [invertible R]
  (hP: matrix.pos_def P) (hR: matrix.pos_def R) :
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

lemma right_mul_inj_of_invertible (P : matrix m m ℂ) [invertible P] :
  function.injective (λ (x : matrix n m ℂ), x ⬝ P) := 
begin
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix n m ℂ), x ⬝ P⁻¹) hax,
  dsimp at hax, 
  rw mul_nonsing_inv_cancel_right at hax,
  rw mul_nonsing_inv_cancel_right at hax, exact hax,
  apply is_unit_det_of_invertible,
  apply is_unit_det_of_invertible,
end

lemma left_mul_inj_of_invertible (P : matrix m m ℂ) [invertible P] :
  function.injective (λ (x : matrix m n ℂ), P ⬝ x) := 
begin
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n ℂ), P⁻¹ ⬝ x) hax,
  dsimp at hax, 
  rw nonsing_inv_mul_cancel_left at hax,
  rw nonsing_inv_mul_cancel_left at hax,
  exact hax,
  apply is_unit_det_of_invertible,
  apply is_unit_det_of_invertible,
end

lemma eq_158_hermitianized (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  [invertible P] [invertible R]
  {hP: matrix.pos_def P} {hR: matrix.pos_def R} : 
  (P⁻¹ + Bᴴ⬝R⁻¹⬝B)⁻¹⬝Bᴴ⬝R⁻¹ = P⬝Bᴴ⬝(B⬝P⬝Bᴴ + R)⁻¹ := 
begin
  -- This is equation 80:
  -- http://www.stat.columbia.edu/~liam/teaching/neurostat-spr12/papers/hmm/KF-welling-notes.pdf

  -- have hP_inv: invertible P,  {apply invertible_of_pos_def, exact hP,},
  -- have hR_inv: invertible R,  {apply invertible_of_pos_def, exact hR,},

  have hP_unit: is_unit P.det, by exact is_unit_of_pos_def hP,
  have hR_unit: is_unit R.det, by exact is_unit_of_pos_def hR,
  have hP_inv_unit := is_unit_nonsing_inv_det P hP_unit,
  have hR_inv_unit := is_unit_nonsing_inv_det R hR_unit,
  have hComb_unit: is_unit (R + B ⬝ P ⬝ Bᴴ).det, {
    rw add_comm, apply is_unit_of_pos_def, apply A_add_B_P_Bt_pos_if_A_pos_B_pos,  
    assumption',
  },
  have : is_unit (R⁻¹⁻¹ + Bᴴᴴ ⬝ P⁻¹⁻¹ ⬝ Bᴴ).det, {
    simp only [inv_inv_of_invertible, conj_transpose_conj_transpose],
    apply hComb_unit,
  },

  rw add_comm _ R,
  nth_rewrite 1 ← conj_transpose_conj_transpose B,
  rw eq_156_hermitianized P⁻¹ R⁻¹ Bᴴ,
  simp only [inv_inv_of_invertible, conj_transpose_conj_transpose],
  rw matrix.sub_mul, rw matrix.sub_mul, 
  rw sub_eq_iff_eq_add,
  apply_fun (matrix.mul P⁻¹), rw matrix.mul_add,
  repeat {rw ←  matrix.mul_assoc P⁻¹ _ _}, rw nonsing_inv_mul, rw matrix.one_mul,
  apply_fun (λ x, x⬝R),  dsimp,
  rw matrix.add_mul,
  rw nonsing_inv_mul_cancel_right,
  rw nonsing_inv_mul_cancel_right,
  repeat {rw matrix.mul_assoc (Bᴴ⬝(R + B ⬝ P ⬝ Bᴴ)⁻¹)},
  rw ← matrix.mul_add (Bᴴ⬝(R + B ⬝ P ⬝ Bᴴ)⁻¹), rw nonsing_inv_mul_cancel_right,

  rw add_comm, apply is_unit_of_pos_def, apply A_add_B_P_Bt_pos_if_A_pos_B_pos,
  assumption',
  apply right_mul_inj_of_invertible,
  apply left_mul_inj_of_invertible,
end
-- Checks

section randomstuff
variables (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ)
#check A
#check U⬝B⬝V
end randomstuff