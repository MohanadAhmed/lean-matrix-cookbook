import data.complex.basic
import data.complex.exponential

import data.matrix.basic
import data.matrix.reflection

-- import analysis.fourier.add_circle

import analysis.special_functions.trigonometric.basic

import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.circulant
import linear_algebra.vandermonde

import algebra.geom_sum


open_locale real matrix big_operators complex_conjugate
open matrix
open equiv equiv.perm finset
open complex
open polynomial

-- eq_403 : Twiddle Factors
-- noncomputable def Wkn {N: ℕ} (k n: fin N) : ℂ :=  
-- exp(2 * π * I * k * n / N)

-- -- Inverse Twiddle Factors
-- noncomputable def iWkn {N: ℕ} (k n: fin N) : ℂ :=  
-- exp(- 2 * π * I * k * n / N)

-- noncomputable def mfourier {N: ℕ}(k : ℤ) := (@fourier ↑N k)
-- noncomputable def mWₙ{N: ℕ}(k n : ℤ) := mfourier k ↑n

-- Forward DFT Matrix
noncomputable def Wₙ {N: ℕ}: matrix (fin N) (fin N) ℂ :=
λ k n, exp(-2 * π * I * k * n / N)

-- Conjugate DFT Matrix: Just the complex conjugate
noncomputable def sWₙ {N: ℕ} : matrix (fin N) (fin N) ℂ :=
λ k n, exp(2 * π * I * k * n / N)

-- Inverse DFT Matrix: Conjugate divided by N
noncomputable def iWₙ {N: ℕ} : matrix (fin N) (fin N) ℂ := 
(1/N:ℂ)•(sWₙ)

lemma exp_pow_s {N:ℕ}{hN: ne_zero N} (i k n: fin N):
  exp(2 * π * I * i * (k - n) / N) = 
    exp(2 * π * I * (k - n) / N) ^ (i:ℕ) := 
begin
  have : 2 * ↑π * I * i * (k - n) / N = i * (2 * π * I * (k - n) / N), {
    by ring,
  },
  rw this, rw coe_coe,
  rw exp_nat_mul _ ↑i,
end

lemma Wkn_dot_iWKn_offdiag {N:ℕ} {hN: N ≠ 0} 
  {k n: fin N} {h_k_ne_n: ¬(k = n)} :
    ∑ (i : fin N), exp(2 * π * I * i * (k - n) / N) = 0 := 
begin
  have hN_ne_zero : (↑N:ℂ) ≠ 0, 
    by { simp only [ne.def, nat.cast_eq_zero], exact hN,},

  conv_lhs { 
    apply_congr, skip,
     rw @exp_pow_s N (ne_zero_iff.2 hN) x k n,
  },
  rw fin.sum_univ_eq_sum_range,
  rw geom_sum_eq, 
  simp only [_root_.div_eq_zero_iff],
  left,
  rw sub_eq_zero, 

  simp_rw [← complex.exp_nat_mul, mul_comm ↑N _],
  rw [div_mul_cancel, mul_comm],

  rw complex.exp_eq_one_iff, use (↑k:ℤ) - ↑n,
  simp only [coe_coe, int.cast_sub, int.cast_coe_nat], 
  exact hN_ne_zero,

  by_contra hc,
  rw complex.exp_eq_one_iff at hc,
  cases hc with m hm,
  set α := 2*↑π*I,
  set β:ℂ := ↑k - ↑n,
  
  rw [mul_comm _ α] at hm, 
  rw mul_div_assoc at hm,
  rw (mul_right_inj' two_pi_I_ne_zero) at hm,
  
  change β with ↑k - ↑n at hm,
  simp only [coe_coe] at hm,
  
  set ak : ℕ := ↑k,
  set an : ℕ := ↑n,
  rw (div_eq_iff_mul_eq hN_ne_zero) at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ ak at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ an at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ N at hm,
  set aN : ℤ := ↑N,
  rw ← int.cast_sub (↑ak) (↑an) at hm,
  rw ← int.cast_mul m aN at hm,
  rw int.cast_inj at hm,
  apply_fun (% N) at hm, 
  simp only [int.mul_mod_left] at hm,
  
  replace hm := hm.symm,
  
  rw ← int.mod_eq_mod_iff_mod_sub_eq_zero at hm,
  rw int.mod_eq_of_lt at hm,
  rw int.mod_eq_of_lt at hm,
  rw int.coe_nat_eq_coe_nat_iff at hm,
  change ak with ↑k at hm, change an with ↑n at hm,
  rw fin.coe_eq_coe at hm,
  exact h_k_ne_n hm,
  simp only [nat.cast_nonneg],
  simp only [nat.cast_lt, fin.is_lt],
  simp only [nat.cast_nonneg],
  simp only [nat.cast_lt, fin.is_lt],
end

lemma Wₙ_mul_sWₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⬝sWₙ = (N:ℂ)•1 := 
begin
  rw Wₙ, rw sWₙ,
  funext k n,
  rw pi.smul_apply, rw pi.smul_apply,
  rw matrix.mul, dsimp, rw dot_product,
  rw neg_mul,
  rw neg_mul,
  set η := 2*↑π*I,
  conv_lhs {  
    apply_congr, skip, rw mul_comm,
    rw ← exp_add, rw ← add_div,
    rw neg_mul, rw neg_mul,rw ← sub_eq_add_neg, 
    rw mul_assoc, rw mul_assoc η _ _,
    rw ← mul_sub, rw mul_comm ↑↑k, rw ← mul_sub, rw ← mul_assoc,
  },
  by_cases hkn: (n = k), {
    rw hkn, rw one_apply_eq, rw sub_self,
    simp only [mul_zero, zero_div, exp_zero, 
    sum_const, card_fin, nat.smul_one_eq_coe, mul_one],
  }, { -- k ≠ n
    rw ← ne.def at hkn,
    rw one_apply_ne' hkn, rw mul_zero,
    apply Wkn_dot_iWKn_offdiag,
    exact ne_zero_iff.1 hN, apply hkn,
  },
end

lemma inverse_Wₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⁻¹ = (1/N:ℂ)•(λ k n, exp(2 * π * I * k * n / N)) :=
begin
  have hNz: (N:ℂ) ≠ 0, {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },
  apply inv_eq_right_inv, rw matrix.mul_smul,
  apply_fun (has_smul.smul (N:ℂ)), rw one_div, rw smul_inv_smul₀,
  rw ← sWₙ,
  apply @Wₙ_mul_sWₙ N hN,
  exact hNz,
  apply smul_right_injective,
  exact hNz,
end

lemma Wₙ_mul_iWₙ_eq_one {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⬝iWₙ = 1 :=
begin
  have hNz: (N:ℂ) ≠ 0, 
    {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },

  rw iWₙ, rw matrix.mul_smul, rw one_div, rw inv_smul_eq_iff₀,
   apply @Wₙ_mul_sWₙ N hN,
  assumption,
end

lemma Wₙ_symmetric {N: ℕ} {hN: ne_zero N} :
  (Wₙ: matrix (fin N) (fin N) ℂ)ᵀ = Wₙ :=
begin
  funext k n,
  rw transpose_apply, rw Wₙ,
  ring_nf,
end

lemma twiddle_comm' {N: ℕ}(k n: fin N) :
  Wₙ k n = Wₙ n k := begin
  rw Wₙ, dsimp, ring_nf,
end

lemma twiddle_sum {N: ℕ}{hN: ne_zero N}(k m n: fin N) :
  Wₙ k m * Wₙ k n  = Wₙ k (m + n) := 
begin
  rw Wₙ, dsimp, 
  -- repeat {rw Wkn},
  have hNz: (↑N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, rwa ne_zero_iff at hN, 
  },
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_div,
  rw neg_div,
  rw neg_div,
  rw exp_neg,
  rw exp_neg,
  rw exp_neg,
  rw ← mul_inv, rw inv_eq_iff_eq_inv, rw inv_inv,

  rw ← exp_add, 
  rw exp_eq_exp_iff_exists_int,
  let a:ℤ := ((↑m + ↑n)/N),
  let w:ℤ := k*a,
  use w, 
  
  rw ← add_div, rw ← mul_add (2 * ↑π * I * ↑↑k),
  set α := (2 * ↑π * I),
  rw mul_comm _ α, 
  rw mul_assoc, rw mul_div_assoc,
  rw mul_assoc α _ _, rw mul_div_assoc α,
  rw ←  mul_add α,
  rw mul_right_inj' two_pi_I_ne_zero,
  rw div_eq_iff hNz, rw add_mul, 
  rw div_mul_cancel _ hNz ,
  change w with k*a,
  rw int.cast_mul, simp only [coe_coe, int.cast_coe_nat],
  rw ← coe_coe,
  rw mul_assoc,
  rw ← mul_add (↑k:ℂ),
  by_cases hk: (↑k:ℂ) ≠ 0, {
    -- rw mul_eq_mul_left_iff, left,
    rw mul_right_inj' hk,
    norm_cast, rw fin.coe_add,
    change a with ((↑m + ↑n)/N),
    simp only [coe_coe, int.cast_coe_nat], norm_cast,
    rw nat.mod_add_div' (↑m + ↑n) N,
  }, {
    simp only [not_not] at hk,
    rw hk, rw zero_mul, rw zero_mul,
  },
end

lemma conj_Wₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)ᵀᴴ = sWₙ :=
begin
  rw @Wₙ_symmetric N hN, funext,
  rw Wₙ, rw sWₙ, dsimp, rw ← exp_conj,
  rw neg_mul, rw neg_mul, rw mul_comm (2*↑π:ℂ), rw ← neg_mul,
  rw mul_assoc, rw mul_assoc, rw mul_div_assoc,
  rw star_ring_end_apply, rw star_mul', rw ← star_ring_end_apply,
  rw conj_neg_I,
  rw exp_eq_exp_iff_exists_int, use 0, 
  simp only [coe_coe, is_R_or_C.star_def, map_div₀, 
  _root_.map_mul, is_R_or_C.conj_bit0, _root_.map_one, is_R_or_C.conj_of_real,
  map_nat_cast, algebra_map.coe_zero, zero_mul, add_zero],
  ring_nf,

end

-- eq_404
noncomputable def dft {N: ℕ} (x: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), ∑ (n : fin N), (Wₙ k n) * (x n)

-- eq_405
noncomputable def idft {N: ℕ} (X: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), (1/N)*(∑ (n : fin N),  (Wₙ) (-k) n * (X n))

lemma eq_406 {N: ℕ} (x: fin N → ℂ) : 
dft x = matrix.mul_vec Wₙ x := 
by {funext k, rw [dft], refl}

lemma eq_407 {N: ℕ} {hN: ne_zero N} (X: fin N → ℂ) : 
idft X = (matrix.mul_vec (Wₙ⁻¹) X) := 
begin
  have hNz: (N:ℂ) ≠ 0, {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },
  funext k, rw idft, rw inverse_Wₙ, rw Wₙ, dsimp, rw mul_vec, rw dot_product,
  dsimp, rw mul_sum, 
  rw neg_mul,
  rw neg_mul, 
  rw neg_mul, rw ← mul_neg, 
  set η := 2*↑π*I,
  by_cases hk: (k) = 0, {
    rw hk, simp only [neg_zero, fin.coe_zero, char_p.cast_eq_zero, 
    mul_zero, zero_mul, zero_div, exp_zero, one_mul, mul_one],
  },{ -- 1 ≤ k < N,
    rw fin.coe_neg k,
    have khgt: ↑(0:(fin N)) < (↑k:ℕ), by {
      rw ← fin.lt_iff_coe_lt_coe,
      rw ← ne.def at hk,
      exact (fin.pos_iff_ne_zero k).2 hk,
    },
    have hNk: N - ↑k < N, {
      exact (nat.sub_lt_of_pos_le ↑k N khgt) (le_of_lt (fin.is_lt k)),
    },
    rw (nat.mod_eq_of_lt hNk),
    rw nat.cast_sub, rw neg_sub,
    conv_lhs {
      apply_congr, skip,
      rw mul_sub, rw sub_mul,rw sub_div,
      rw mul_assoc _ ↑N ↑↑x, rw mul_comm ↑N ↑↑x,
      rw ← mul_assoc _ ↑↑x ↑N, rw mul_div_cancel _ hNz,
      rw exp_sub, rw mul_comm η ↑↑x, rw exp_nat_mul_two_pi_mul_I,
      rw div_one, rw ← mul_assoc _ _ (X x),
    },
    simp only [fin.is_le'],
  },
  assumption',
end

lemma eq_408 {N: ℕ} {hN: ne_zero N} :   
  (Wₙ: matrix (fin N) (fin N) ℂ )⁻¹ = (N:ℂ)⁻¹ • sWₙ :=
begin
  rw inverse_Wₙ, rw inv_eq_one_div,
  rw sWₙ,
  exact hN,
end

lemma eq_409 {N: ℕ} {hN: N ≠ 0} : 
(Wₙ: matrix (fin N) (fin N) ℂ) ⬝ (sWₙ) = 
  (N:ℂ)•(1) := 
begin
  apply Wₙ_mul_sWₙ,
  exact ne_zero_iff.2 hN,
end

lemma eq_410 {N: ℕ} : 
(star Wₙ : matrix (fin N) (fin N) ℂ) = Wₙᴴ :=
begin
  unfold star,
end

lemma two_pi_I_by_N_piInt_pos {N : ℕ}
  (h2 : 2 < N) :
  (2 * ↑π * I / ↑N).im < π :=
begin
  have hNlt0 : 0 < (N:ℝ), by {
    simp only [nat.cast_pos],
    linarith,
  },
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,

  rw div_lt_iff hNlt0, rw mul_comm, 
  rw mul_lt_mul_left real.pi_pos,
  norm_cast, exact h2,
end

lemma two_pi_I_by_N_piInt_neg {N : ℕ}
  (h2 : 2 < N) :
  -π < ((2) * ↑π * I / ↑N).im :=
begin
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,
  have neg_pi_lt_zero: -π < 0, {
    exact neg_lt_zero.2 real.pi_pos,
  },
  set η : ℝ := ↑N,
  have zero_lt_η: 0 < η,{
    change η with ↑N,
    simp only [nat.cast_pos],
    linarith,
  },
  have pi_div_N_lt_zero: 0 < 2*π/η, {
    exact div_pos real.two_pi_pos zero_lt_η,
  },
  rw lt_div_iff zero_lt_η, 
  rw neg_mul, rw mul_comm, rw ← neg_mul, 
  rw mul_lt_mul_right real.pi_pos,
  rw neg_lt_iff_pos_add',
  change η with ↑N,
  exact add_pos zero_lt_η zero_lt_two,
end


lemma twiddle_neg_half_cycle_eq_neg' {N: ℕ} {hN: 2 ≤ N}:
  exp(-2 * π * I / N)^((N:ℂ)/(2:ℂ)) = 
  -1 :=
begin
  by_cases h2: (N = 2),
  rw h2, ring_nf,
  have: (1/(2:ℂ)*↑2) = 1, by {
    simp only [one_div, nat.cast_bit0, 
    algebra_map.coe_one,
     inv_mul_cancel_of_invertible],
  },
  rw this, simp only [cpow_one], rw exp_neg,
  rw mul_comm, rw exp_pi_mul_I,
  norm_num,
  rw le_iff_lt_or_eq at hN,
  cases hN with hNlt2 hNeq2,
  rw cpow_def_of_ne_zero,
  rw log_exp,
  rw div_mul,
  set η:ℂ := ↑N,
  have hη: η ≠ 0, 
    by {simp only [nat.cast_ne_zero], linarith,},

  rw div_div_cancel' hη, ring_nf,
  rw mul_comm, rw exp_neg,
  rw exp_pi_mul_I, norm_num,
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_lt_neg_iff,
  exact two_pi_I_by_N_piInt_pos hNlt2,
  
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_le,
  exact (le_of_lt (two_pi_I_by_N_piInt_neg hNlt2)),
  exact exp_ne_zero ((-2) * π * I / N),
  exfalso, exact h2 hNeq2.symm,
end


lemma eq_411 {N: ℕ}{h2: 2 ≤ N} {m: ℤ} : 
  let Wₙ := complex.exp(-2 * π * I  / N) in
  Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
begin
  dsimp only,
  set α := exp(- 2 * π * I / N),
  rw complex.cpow_add,
  simp only [cpow_int_cast],
  rw ← neg_one_mul, rw mul_comm,
  rw mul_left_inj',
  apply twiddle_neg_half_cycle_eq_neg',
  exact h2,
  rw ← exp_int_mul, ring_nf,
  exact exp_ne_zero (-(2 * (↑N)⁻¹ * I * ↑π * ↑m)),
  exact exp_ne_zero (- 2 * π * I / N),
end

def shiftk {N: ℕ}{hN: ne_zero N} (k: fin N):(fin N → fin N) 
def shiftk_equiv {N: ℕ} {hN: ne_zero N} (k: fin N) : (fin N) ≃ (fin N) :=
{
  to_fun := @shiftk N hN (-k),
  inv_fun := @shiftk N hN (k),
  left_inv := by {
    -- intro x, rw shiftk, rw shiftk, dsimp, ring,
    intro x, dsimp shiftk, 
  },
  right_inv := by {
    intro x, rw shiftk, rw shiftk, dsimp, ring,
  },
}

lemma eq_412 {N: ℕ} {hN: ne_zero N} (t: (fin N) → ℂ) :
  matrix.circulant t = (Wₙ)⁻¹ ⬝ (diagonal(dft t)) ⬝ Wₙ := 
begin
  apply_fun (matrix.mul Wₙ),
  rw ← matrix.mul_assoc,
  rw ← matrix.mul_assoc,
  rw mul_nonsing_inv,

  funext j k,
  rw mul_mul_apply,
  rw dot_product_mul_vec, simp only,
  rw Wₙ_symmetric, rw matrix.mul_apply,
  conv_lhs {
    apply_congr, skip,
    rw circulant_apply,
  },
  rw dot_product,
  
  conv_rhs {
    apply_congr, skip,
     
    rw vec_mul_diagonal,
    -- rw pi.smul_apply,
    -- rw pi.smul_apply,
    rw matrix.one_apply,
    -- rw smul_mul_assoc,
    -- rw smul_mul_assoc,
    rw ite_mul,
    rw ite_mul,
    rw zero_mul,
    rw zero_mul, rw one_mul,
    rw mul_comm,
  },
  rw sum_ite,
  simp only [sum_const_zero, add_zero],
  rw filter_eq,
  simp only [mem_univ, if_true, sum_singleton],
  rw dft, dsimp,
  rw twiddle_comm',
  rw mul_sum,
  conv_rhs {
    apply_congr, skip,
    rw ← mul_assoc,
    rw @twiddle_sum N hN j k x,
  },

  -- rw Wₙ,simp only, dsimp,
  rw ← equiv.sum_comp (@shiftk_equiv N hN (-k)),
  rw shiftk_equiv, dsimp,  
  rw shiftk, simp only [neg_neg, add_sub_cancel],
  conv_lhs {
    apply_congr, skip, rw add_comm,
  }, 

  rw ne_zero_iff at hN, exact hN,
  -- extract_goal,
    rintros x a h,
  replace hinj := congr_arg (iWₙ).mul h,
  rw ← matrix.mul_assoc at hinj,
  rw ← matrix.mul_assoc at hinj,
  rw iW_N_mul_W_N at hinj,
  rw matrix.smul_mul at hinj,
  rw matrix.smul_mul at hinj,
  rw matrix.one_mul at hinj,
  rw matrix.one_mul at hinj,
  
  funext k n,
  have hz := (matrix.ext_iff.2 hinj) k n,
  repeat {rw pi.smul_apply at hz},
  have hNz : (N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, exact ne_zero_iff.1 hN,
  },
  rw ← sub_eq_zero at hz,
  rw ← smul_sub at hz,
  rw smul_eq_zero_iff_eq' hNz at hz,
  rwa sub_eq_zero at hz,
  exact hN,
end