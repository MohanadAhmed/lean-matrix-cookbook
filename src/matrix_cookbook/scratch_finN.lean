import data.complex.basic
import data.complex.exponential
import data.real.basic
import data.fin.basic
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.exponential
import analysis.special_functions.complex.log

lemma sub_ne_finN_ne_zero {N : ℕ}
  {hN : 1 < N}
  (k n : fin N)
  (h : ¬k = n)
  (hkn : (↑k:ℤ) - ↑n = 0) :
  false :=
begin
  rw int.sub_eq_zero_iff_eq at hkn,
  simp only [coe_coe, nat.cast_inj] at *,
  rw fin.coe_eq_coe at hkn,
  exact h hkn,
end

open complex 
open real
open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset

noncomputable def Wkn {N: ℕ} (k n: fin N) : ℂ :=  
exp(2 * π * I * k * n / N)

noncomputable def iWkn {N: ℕ} (k n: fin N) : ℂ :=  
exp(- 2 * π * I * k * n / N)

@[simp] lemma twiddle_mul {N:ℕ} (j k l: fin N) :
  Wkn j k * iWkn k l = 
    (exp(2 * π * I * (j - l) / N)) ^ (k:ℕ) :=
begin
  rw [Wkn, iWkn],
  rw ← complex.exp_add, simp only [ neg_mul], rw neg_div,
  rw ← sub_eq_add_neg,

  have : 2 * ↑π * I * j * k / N - 2 * ↑π * I * k * l / N
   =  k * (2 * π * I * (j - l) / N), by ring,
   rw this,
   exact exp_int_mul _ _,
end

lemma Wkn_dot_iWKn_offdiag {N:ℕ} {hN: N ≠ 0} 
  (k n: fin N) (h_k_ne_n: ¬(k = n)) :
    ∑ (i : fin N), Wkn k i * iWkn i n = 0 := 
begin
  simp_rw [twiddle_mul],
  rw fin.sum_univ_eq_sum_range,
  rw geom_sum_eq, 
  simp only [_root_.div_eq_zero_iff],
  left,
  rw sub_eq_zero, 

  simp_rw [← complex.exp_nat_mul, mul_comm ↑N _],
  rw [div_mul_cancel, mul_comm],

  have : (↑k - ↑n) * ( 2 * ↑π * I) = ((↑k - ↑n):ℤ) * ( 2 * ↑π * I), 
  by { simp only [coe_coe, int.cast_sub, int.cast_coe_nat],},
  rw this,
  
  apply exp_int_mul_two_pi_mul_I, 
  simp only [ne.def, nat.cast_eq_zero], exact hN,
  
  by_contra hc,
  rw complex.exp_eq_one_iff at hc,
  cases hc with m hm,
  set α := 2*↑π*I,
  set β:ℂ := ↑k - ↑n,
  
  rw [mul_comm _ α] at hm, rw mul_div_assoc at hm,
  -- rw mul_div_assoc' at hm,
  rw (mul_right_inj' two_pi_I_ne_zero) at hm,
  change β with ↑k - ↑n at hm,
  simp only [coe_coe] at hm,
  set ak : ℕ := ↑k,
  set an : ℕ := ↑n,
  rw div_eq_iff_mul_eq at hm,
  rw @coe_coe (ℕ) ℤ ℂ _ _ ak at hm,
  rw @coe_coe (ℕ) ℤ ℂ _ _ an at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ N at hm,
  set aN : ℤ := ↑N,
  rw ← int.cast_sub (↑ak) (↑an) at hm,
  rw ← int.cast_mul m aN at hm,
  norm_cast at hm,
  apply_fun (% N) at hm, 
  simp only [int.mul_mod_left] at hm,
  let hm1 := hm.symm,
  rw ← int.mod_eq_mod_iff_mod_sub_eq_zero at hm1,
  norm_cast at hm1,
  change ak with ↑k at hm1, change an with ↑n at hm1,
  rw (nat.mod_eq_iff_lt hN).2 at hm1,
  rw (nat.mod_eq_iff_lt hN).2 at hm1,
  rw fin.coe_eq_coe at hm1,
  exact h_k_ne_n hm1,
  simp only [fin.is_lt],
  simp only [fin.is_lt],
  simp only [ne.def, nat.cast_eq_zero], exact hN,
end
