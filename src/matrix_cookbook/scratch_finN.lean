import data.complex.basic
import data.complex.exponential
import data.real.basic
import data.fin.basic
import analysis.special_functions.trigonometric.basic
import analysis.special_functions.exponential
import analysis.special_functions.complex.log
import analysis.complex.roots_of_unity

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

lemma one_lt_N_zero_ne {N: ℕ} (hN: 1 < N) : (↑N:ℂ) ≠ (0:ℂ) := begin
  simp only [ne.def, nat.cast_eq_zero], 
  linarith,
end

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

open_locale real

lemma exp_sub_kn_neg_ne_one (N : ℕ)
  (hN : 0 < N)
  (m : ℤ)
  (hm1: m < 0)
  (hm2: (-N:ℤ) < m) :
  exp (2 * ↑π * I * (↑m) / ↑N) ≠ 1 :=
begin
sorry {
  by_contra,
  let k := m + N,
  have hm : m = k - N, by simp only [add_tsub_cancel_right],
  have hk0 : 0 < k, by linarith,
  have hkN : k < N, by linarith,
  have hNz : (↑N:ℂ) ≠ 0, by {
    by_contra zxz, norm_cast at zxz, 
    exact (ne_of_lt hN) zxz.symm,
  },

  rw hm at h,
  rw complex.exp_eq_one_iff at h, 
  rw mul_div_assoc at h,
  cases h with g hg,
  rw mul_comm ↑g _ at hg,
  rw (mul_right_inj' two_pi_I_ne_zero) at hg,
  rw (div_eq_iff hNz) at hg,
  norm_cast at hg,
  apply_fun (% N) at hg, 
  simp only [int.mul_mod_left, add_tsub_cancel_right] at hg, 
  rw hm at hg,
  rw int.sub_mod at hg, rw int.mod_self at hg,
  rw sub_zero at hg, rw int.mod_mod at hg,
  rw int.mod_eq_of_lt (le_of_lt hk0) hkN at hg,
  exact (ne_of_lt hk0) hg.symm,
},
end

lemma exp_sub_kn_pos_ne_one (N : ℕ)
  (hN : 0 < N)
  (m : ℤ)
  (hm0: 0 < m)
  (hmN: m < N) :
  exp (2 * ↑π * I * (↑m) / ↑N) ≠ 1 :=
begin
sorry {  
  have hNz : (↑N:ℂ) ≠ 0, by {
    by_contra zxz, norm_cast at zxz, 
    exact (ne_of_lt hN) zxz.symm,
  },
  by_contra he,
  rw complex.exp_eq_one_iff at he,
  cases he with M hM,
  rw mul_comm ↑M _ at hM,
  -- rw div_eq_iff_eq_mul' at hM,
  rw mul_div_assoc at hM,
  rw (mul_right_inj' two_pi_I_ne_zero) at hM,
  rw (div_eq_iff hNz) at hM,
  norm_cast at hM,
  apply_fun (% N) at hM, simp only [int.mul_mod_left] at hM,
  rw (int.mod_eq_of_lt (le_of_lt hm0) hmN) at hM, 
  exact (ne_of_lt hm0) hM.symm,
},
end

lemma exp_k_sub_n_lt_N_ne_one {N : ℕ}
  {hN : 0 < N}
  (k n : fin N)
  (h : ¬(k = n)) :
  exp (2 * ↑π * I * (↑k - ↑n:ℤ) / ↑N) ≠ 1 :=
begin
  have hknP : (↑k - ↑n:ℤ) < N, {
    induction k with k hk,
    induction n with n hn,
    simp only [coe_coe, fin.coe_mk],
    rw sub_lt_iff_lt_add,
    norm_cast,
    linarith,
  },
  have hknN : (-N:ℤ) < (↑k - ↑n:ℤ), {
    induction k with k hk,
    induction n with n hn,
    simp only [coe_coe, fin.coe_mk, neg_lt_sub_iff_lt_add],
    norm_cast,
    linarith,
  },
  
  by_cases hc: k < n,
  {
    have hkn0 : (↑k - ↑n:ℤ) < (0:ℤ), {
      simp only [coe_coe, sub_neg, nat.cast_lt, 
        fin.coe_fin_lt], exact hc,
    },
    apply exp_sub_kn_neg_ne_one,
    exact hN,
    -- exact (lt_trans zero_lt_one hN),
    exact hkn0,
    exact hknN,
  }, 
  {
    have hkn0: (0:ℤ) < (↑k - ↑n), {
      push_neg at hc,
      simp only [coe_coe, sub_pos, nat.cast_lt, 
        fin.coe_fin_lt],
      rw le_iff_lt_or_eq at hc,
      cases hc with hc1 hc2, 
      exact hc1, exfalso, exact h hc2.symm,
    },
    apply exp_sub_kn_pos_ne_one,
    exact hN,
    -- exact (lt_trans zero_lt_one hN),
    exact hkn0,
    exact hknP,
  }
  
end

lemma exp_k_sub_n_lt_N_ne_one' {N : ℕ}
  {hN : 0 < N}
  (k n : fin N)
  (h : ¬(k = n)) :
  exp (2 * ↑π * I * ((↑k - ↑n):ℂ) / ↑N) ≠ 1 :=
begin
  have hknP : (↑k - ↑n:ℤ) < N, {
    induction k with k hk,
    induction n with n hn,
    simp only [coe_coe, fin.coe_mk],
    rw sub_lt_iff_lt_add,
    norm_cast,
    linarith,
  },
  have hknN : (-N:ℤ) < (↑k - ↑n:ℤ), {
    induction k with k hk,
    induction n with n hn,
    simp only [coe_coe, fin.coe_mk, neg_lt_sub_iff_lt_add],
    norm_cast,
    linarith,
  },
  
  by_cases hc: k < n,
  {
    have hkn0 : (↑k - ↑n) < (0:ℤ), {
      simp only [coe_coe, sub_neg, nat.cast_lt, 
        fin.coe_fin_lt], exact hc,
    },
    -- sorry,
    apply exp_sub_kn_neg_ne_one,
    -- exact hN,
    -- -- exact (lt_trans zero_lt_one hN),
    -- exact hkn0,
    -- exact hknN,
  }, 
  {
    have hkn0: (0:ℤ) < (↑k - ↑n), {
      push_neg at hc,
      simp only [coe_coe, sub_pos, nat.cast_lt, 
        fin.coe_fin_lt],
      rw le_iff_lt_or_eq at hc,
      cases hc with hc1 hc2, 
      exact hc1, exfalso, exact h hc2.symm,
    },
    apply exp_sub_kn_pos_ne_one,
    exact hN,
    -- exact (lt_trans zero_lt_one hN),
    exact hkn0,
    exact hknP,
  },
  
end


-- lemma Wkn_dot_iWKn_offdiag {N:ℕ} {hN: 1 < N} 
--   (k n: fin N) (h: ¬(k = n)) :
--     ∑ (i : fin N), Wkn k i * iWkn i n = 0 := 
-- begin
--   simp_rw [twiddle_mul],
--   rw fin.sum_univ_eq_sum_range,
--   rw geom_sum_eq, 
--   simp only [_root_.div_eq_zero_iff],
--   left,
--   rw sub_eq_zero, 

--   simp_rw [← complex.exp_nat_mul, mul_comm ↑N _],
--   rw [div_mul_cancel, mul_comm],

--   have : (↑k - ↑n) * ( 2 * ↑π * I) = ((↑k - ↑n):ℤ) * ( 2 * ↑π * I), 
--   by { simp only [coe_coe, int.cast_sub, int.cast_coe_nat],},
--   rw this,
  
--   apply exp_int_mul_two_pi_mul_I, 
--   exact one_lt_N_zero_ne hN,
--   apply (exp_k_sub_n_lt_N_ne_one k n),
-- --   extract_goal, 
-- --   -- by_contra he, 
-- --   -- apply_fun log at he, rw complex.log_one at he,
-- --   -- rw complex.log_exp at he,
-- --   -- rw div_eq_zero_iff at he, 
-- --   -- cases he with he _,
-- --   -- rw mul_eq_zero at he,
-- --   -- cases he with ha hb, exact two_pi_I_ne_zero ha,
-- --   -- apply h,
-- --   --   rw sub_eq_zero at hb,
-- --   -- simp only [coe_coe, nat.cast_inj] at hb,
-- --   -- rw fin.coe_eq_coe at hb, exact hb,

-- --   -- exact (one_lt_N_zero_ne hN) he,

-- --   -- extract_goal,
-- end
