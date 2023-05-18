import linear_algebra.matrix.trace
import linear_algebra.matrix.determinant
import data.matrix.notation
import data.matrix.pequiv
import data.matrix.block
import data.fintype.big_operators
import group_theory.perm.fin
import group_theory.perm.sign
import algebra.algebra.basic
import tactic.ring
import linear_algebra.alternating
import linear_algebra.pi
import tactic.norm_fin

variables {R : Type*}

open equiv equiv.perm finset function
namespace matrix
open_locale matrix big_operators
open matrix

-- anyone looking at the cookbook likely only cares about fields anyway!
variables [field R][group R]

lemma trace_a_fin4 {A : matrix (fin 4) (fin 4) R} :
  A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 := 
begin
  rw matrix.trace,  rw fin.sum_univ_four, repeat {rw diag,},
end

lemma trace_a_squared {A : matrix (fin 4) (fin 4) R}:
  trace (A^2) = 
    A 0 0^2 + A 1 1^2 + A 2 2^2 + A 3 3^2 + 
    2*A 0 1*A 1 0 + 2*A 0 2*A 2 0 + 2*A 0 3*A 3 0 + 
    2*A 1 2*A 2 1 + 2*A 1 3*A 3 1 + 2*A 2 3*A 3 2 := 
begin
  rw matrix.trace,
  simp only [diag],
  rw pow_two, rw mul_eq_mul, rw fin.sum_univ_four,
  repeat{rw mul_apply, rw fin.sum_univ_four},
  ring,
end

lemma trace_a_cubed {A : matrix (fin 4) (fin 4) R}:
  trace (A^3) = 
    A 0 0*(A 0 0^2 + A 0 1*A 1 0 + A 0 2*A 2 0 + A 0 3*A 3 0) + 
    A 1 1*(A 1 1^2 + A 0 1*A 1 0 + A 1 2*A 2 1 + A 1 3*A 3 1) + 
    A 2 2*(A 2 2^2 + A 0 2*A 2 0 + A 1 2*A 2 1 + A 2 3*A 3 2) + 
    A 3 3*(A 3 3^2 + A 0 3*A 3 0 + A 1 3*A 3 1 + A 2 3*A 3 2) + 
    A 1 0*(A 0 0*A 0 1 + A 0 1*A 1 1 + A 0 2*A 2 1 + A 0 3*A 3 1) + 
    A 2 0*(A 0 0*A 0 2 + A 0 1*A 1 2 + A 0 2*A 2 2 + A 0 3*A 3 2) + 
    A 0 1*(A 0 0*A 1 0 + A 1 0*A 1 1 + A 1 2*A 2 0 + A 1 3*A 3 0) + 
    A 3 0*(A 0 0*A 0 3 + A 0 1*A 1 3 + A 0 2*A 2 3 + A 0 3*A 3 3) + 
    A 2 1*(A 0 2*A 1 0 + A 1 1*A 1 2 + A 1 2*A 2 2 + A 1 3*A 3 2) + 
    A 0 2*(A 0 0*A 2 0 + A 1 0*A 2 1 + A 2 0*A 2 2 + A 2 3*A 3 0) + 
    A 3 1*(A 0 3*A 1 0 + A 1 1*A 1 3 + A 1 2*A 2 3 + A 1 3*A 3 3) + 
    A 1 2*(A 0 1*A 2 0 + A 1 1*A 2 1 + A 2 1*A 2 2 + A 2 3*A 3 1) + 
    A 0 3*(A 0 0*A 3 0 + A 1 0*A 3 1 + A 2 0*A 3 2 + A 3 0*A 3 3) + 
    A 3 2*(A 0 3*A 2 0 + A 1 3*A 2 1 + A 2 2*A 2 3 + A 2 3*A 3 3) + 
    A 1 3*(A 0 1*A 3 0 + A 1 1*A 3 1 + A 2 1*A 3 2 + A 3 1*A 3 3) + 
    A 2 3*(A 0 2*A 3 0 + A 1 2*A 3 1 + A 2 2*A 3 2 + A 3 2*A 3 3)
 := 
begin
  rw pow_three, rw matrix.trace,
  rw fin.sum_univ_four, rw mul_eq_mul, rw mul_eq_mul, simp only[diag],
  repeat{rw mul_apply, rw fin.sum_univ_four},
  ring,
end

#eval (3: fin 4).succ_above 2

lemma det4 {A : matrix (fin 4) (fin 4) R}:
A.det = 
  A 0 0*A 1 1*A 2 2*A 3 3 - A 0 0*A 1 1*A 2 3*A 3 2 - A 0 0*A 1 2*A 2 1*A 3 3 + 
  A 0 0*A 1 2*A 2 3*A 3 1 + A 0 0*A 1 3*A 2 1*A 3 2 - A 0 0*A 1 3*A 2 2*A 3 1 -

  A 0 1*A 1 0*A 2 2*A 3 3 + A 0 1*A 1 0*A 2 3*A 3 2 + A 0 1*A 1 2*A 2 0*A 3 3 - 
  A 0 1*A 1 2*A 2 3*A 3 0 - A 0 1*A 1 3*A 2 0*A 3 2 + A 0 1*A 1 3*A 2 2*A 3 0 +

  A 0 2*A 1 0*A 2 1*A 3 3 - A 0 2*A 1 0*A 2 3*A 3 1 - A 0 2*A 1 1*A 2 0*A 3 3 + 
  A 0 2*A 1 1*A 2 3*A 3 0 + A 0 2*A 1 3*A 2 0*A 3 1 - A 0 2*A 1 3*A 2 1*A 3 0 -

  A 0 3*A 1 0*A 2 1*A 3 2 + A 0 3*A 1 0*A 2 2*A 3 1 + A 0 3*A 1 1*A 2 0*A 3 2 - 
  A 0 3*A 1 1*A 2 2*A 3 0 - A 0 3*A 1 2*A 2 0*A 3 1 + A 0 3*A 1 2*A 2 1*A 3 0 := 
begin
  -- There is no way but to brute force this. "Sophisticated" tactics are too slow!!
  have s0: fin.succ (0: fin 3) = 1, {norm_fin,},
  have s1: fin.succ (1: fin 3) = 2, {norm_fin,},
  have s2: fin.succ (2: fin 3) = 3, {norm_fin,},
  have a0 : ((-1:R)^(↑(0: fin 4))) = (1:R), {rw fin.coe_zero,rw pow_zero,},
  have a1 : (-1:R)^(↑(1: fin 4)) = -1, {rw fin.coe_one,rw pow_one,},
  have a2 : (-1:R)^(↑(2: fin 4)) = 1, {
    rw neg_one_pow_eq_pow_mod_two, rw fin.coe_two, rw nat.mod_self, rw pow_zero,
  },
  have a3 : (-1:R)^(↑(3: fin 4)) = -1, {
    rw neg_one_pow_eq_pow_mod_two, have : ↑(3: fin 4) = (3:ℕ), {refl,}, 
    rw this, have : 3 % 2  = 1, by refl, rw this, rw pow_one,
  },
  
  rw matrix.det_succ_row_zero, 
  conv_lhs {
    apply_congr,skip,rw det_fin_three,
  }, rw fin.sum_univ_four, repeat {rw submatrix_apply}, 
  rw [a0, a1, a2, a3], 
  repeat {rw fin.one_succ_above_zero},
  repeat {rw fin.zero_succ_above},
  rw [s0], rw s1, rw s2,
  rw fin.one_succ_above_one,
  have : (1: fin 4).succ_above 2 = 3, {refl,},  rw this,
  have : (2: fin 4).succ_above 0 = 0, {refl,},  rw this,
  have : (2: fin 4).succ_above 1 = 1, {refl,},  rw this,
  have : (2: fin 4).succ_above 2 = 3, {refl,},  rw this,
  have : (3: fin 4).succ_above 0 = 0, {refl,},  rw this,
  have : (3: fin 4).succ_above 1 = 1, {refl,},  rw this,
  have : (3: fin 4).succ_above 2 = 2, {refl,},  rw this,
  ring,
end

lemma det4_one_add_a {A : matrix (fin 4) (fin 4) R}:
(1 + A).det = 
A 0 0 + A 1 1 + A 2 2 + A 3 3 + 
A 0 0*A 1 1 - A 0 1*A 1 0 + A 0 0*A 2 2 - A 0 2*A 2 0 + A 0 0*A 3 3 - A 0 3*A 3 0 + A 1 1*A 2 2 - A 1 2*A 2 1 + 
A 1 1*A 3 3 - A 1 3*A 3 1 + A 2 2*A 3 3 - A 2 3*A 3 2 + 
A 0 0*A 1 1*A 2 2 - A 0 0*A 1 2*A 2 1 - A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + A 0 2*A 1 0*A 2 1 - A 0 2*A 1 1*A 2 0 + A 0 0*A 1 1*A 3 3 - A 0 0*A 1 3*A 3 1 -
A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 - A 0 3*A 1 1*A 3 0 + A 0 0*A 2 2*A 3 3 - A 0 0*A 2 3*A 3 2 - A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 +
A 0 3*A 2 0*A 3 2 - A 0 3*A 2 2*A 3 0 + A 1 1*A 2 2*A 3 3 - A 1 1*A 2 3*A 3 2 - A 1 2*A 2 1*A 3 3 + A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 - A 1 3*A 2 2*A 3 1 + 
A 0 0*A 1 1*A 2 2*A 3 3 - A 0 0*A 1 1*A 2 3*A 3 2 - A 0 0*A 1 2*A 2 1*A 3 3 + A 0 0*A 1 2*A 2 3*A 3 1 + A 0 0*A 1 3*A 2 1*A 3 2 - A 0 0*A 1 3*A 2 2*A 3 1 - 
A 0 1*A 1 0*A 2 2*A 3 3 + A 0 1*A 1 0*A 2 3*A 3 2 + A 0 1*A 1 2*A 2 0*A 3 3 - A 0 1*A 1 2*A 2 3*A 3 0 - A 0 1*A 1 3*A 2 0*A 3 2 + A 0 1*A 1 3*A 2 2*A 3 0 + 
A 0 2*A 1 0*A 2 1*A 3 3 - A 0 2*A 1 0*A 2 3*A 3 1 - A 0 2*A 1 1*A 2 0*A 3 3 + A 0 2*A 1 1*A 2 3*A 3 0 + A 0 2*A 1 3*A 2 0*A 3 1 - A 0 2*A 1 3*A 2 1*A 3 0 - 
A 0 3*A 1 0*A 2 1*A 3 2 + A 0 3*A 1 0*A 2 2*A 3 1 + A 0 3*A 1 1*A 2 0*A 3 2 - A 0 3*A 1 1*A 2 2*A 3 0 - A 0 3*A 1 2*A 2 0*A 3 1 + A 0 3*A 1 2*A 2 1*A 3 0 + 
1 := begin
  rw det4,
  repeat {rw pi.add_apply}, repeat {rw one_apply_eq},
  have : (1: matrix (fin 4) (fin 4) R) 0 1 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 0 2 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 0 3 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 1 0 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 1 2 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 1 3 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 2 0 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 2 1 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 2 3 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 3 0 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 3 1 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  have : (1: matrix (fin 4) (fin 4) R) 3 2 = 0, {apply one_apply_ne, norm_num,}, repeat {rw this},
  ring,
end

lemma eq_27_lhs {A : matrix (fin 4) (fin 4) R}:
(1 + A).det - A.det - 1 = 
  A 0 0 + A 1 1 + A 2 2 + A 3 3 + 
  A 0 0*A 1 1 - A 0 1*A 1 0 + A 0 0*A 2 2 - A 0 2*A 2 0 + A 0 0*A 3 3 - A 0 3*A 3 0 + A 1 1*A 2 2 - A 1 2*A 2 1 + 
  A 1 1*A 3 3 - A 1 3*A 3 1 + A 2 2*A 3 3 - A 2 3*A 3 2 + 
  A 0 0*A 1 1*A 2 2 - A 0 0*A 1 2*A 2 1 - A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + A 0 2*A 1 0*A 2 1 - A 0 2*A 1 1*A 2 0 + A 0 0*A 1 1*A 3 3 - A 0 0*A 1 3*A 3 1 - 
  A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 - A 0 3*A 1 1*A 3 0 + A 0 0*A 2 2*A 3 3 - A 0 0*A 2 3*A 3 2 - A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 + 
  A 0 3*A 2 0*A 3 2 - A 0 3*A 2 2*A 3 0 + A 1 1*A 2 2*A 3 3 - A 1 1*A 2 3*A 3 2 - A 1 2*A 2 1*A 3 3 + A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 - A 1 3*A 2 2*A 3 1
:= 
begin
  rw det4_one_add_a, rw det4, ring,
end

lemma trace_a_all_squared {A : matrix (fin 4) (fin 4) R}:
(trace A)^2 = 
A 0 0^2 + A 1 1^2 + A 2 2^2 + A 3 3^2 + 
2*A 0 0*A 1 1 + 2*A 0 0*A 2 2 + 2*A 0 0*A 3 3 + 
2*A 1 1*A 2 2 + 2*A 1 1*A 3 3 + 2*A 2 2*A 3 3 
:= begin
  rw trace_a_fin4, rw pow_two, ring,
end

lemma eq_27_rhs_part1{A : matrix (fin 4) (fin 4) R}:
(trace A)^3 - 3*trace A * trace (A^2) + 2 * trace (A^3) = 6*(A 0 0*A 1 1*A 2 2 - A 0 0*A 1 2*A 2 1 - A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + A 0 2*A 1 0*A 2 1 - A 0 2*A 1 1*A 2 0 + A 0 0*A 1 1*A 3 3 - 
A 0 0*A 1 3*A 3 1 - A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 - A 0 3*A 1 1*A 3 0 + A 0 0*A 2 2*A 3 3 - A 0 0*A 2 3*A 3 2 - 
A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 + A 0 3*A 2 0*A 3 2 - A 0 3*A 2 2*A 3 0 + A 1 1*A 2 2*A 3 3 - A 1 1*A 2 3*A 3 2 - A 1 2*A 2 1*A 3 3 + 
A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 - A 1 3*A 2 2*A 3 1) := by {
  rw trace_a_fin4, rw trace_a_squared, rw trace_a_cubed, ring,
}

lemma eq_27_rhs_part2{A : matrix (fin 4) (fin 4) R}:
(trace A)^2 - trace (A^2) = 
  2*(A 0 0*A 1 1 - A 0 1*A 1 0 + A 0 0*A 2 2 - A 0 2*A 2 0 + A 0 0*A 3 3 - A 0 3*A 3 0 + 
A 1 1*A 2 2 - A 1 2*A 2 1 + A 1 1*A 3 3 - A 1 3*A 3 1 + A 2 2*A 3 3 - A 2 3*A 3 2) := by {
  rw trace_a_all_squared, rw trace_a_squared, ring,
}


lemma eq_27_rhs {A : matrix (fin 4) (fin 4) R}:
trace A + (1/2)*( (trace A)^2 - trace (A^2)) + 
              (1/6)*( (trace A)^3 - 3*trace A * trace (A^2) + 2 * trace (A^3) ) = 
 A 0 0 + A 1 1 + A 2 2 + A 3 3 + 
  A 0 0*A 1 1 - A 0 1*A 1 0 + A 0 0*A 2 2 - A 0 2*A 2 0 + A 0 0*A 3 3 - A 0 3*A 3 0 + A 1 1*A 2 2 - A 1 2*A 2 1 + 
  A 1 1*A 3 3 - A 1 3*A 3 1 + A 2 2*A 3 3 - A 2 3*A 3 2 + 
  A 0 0*A 1 1*A 2 2 - A 0 0*A 1 2*A 2 1 - A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + A 0 2*A 1 0*A 2 1 - A 0 2*A 1 1*A 2 0 + A 0 0*A 1 1*A 3 3 - A 0 0*A 1 3*A 3 1 - 
  A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 - A 0 3*A 1 1*A 3 0 + A 0 0*A 2 2*A 3 3 - A 0 0*A 2 3*A 3 2 - A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 + 
  A 0 3*A 2 0*A 3 2 - A 0 3*A 2 2*A 3 0 + A 1 1*A 2 2*A 3 3 - A 1 1*A 2 3*A 3 2 - A 1 2*A 2 1*A 3 3 + A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 - A 1 3*A 2 2*A 3 1
:= begin
  have m2 : (2:R)⁻¹*(2:R) = 1, {sorry,},
  have m6 : (6:R)⁻¹*(6:R) = 1, {sorry,},
  rw eq_27_rhs_part1, rw one_div (6:R), rw ← mul_assoc,  rw m6, rw one_mul,
  rw eq_27_rhs_part2, rw one_div (2:R), rw ← mul_assoc,  rw m2, rw one_mul,
  rw trace_a_fin4, ring,
end



lemma eq_27_before_last {A : matrix (fin 4) (fin 4) R} :
  det (1 + A) - det A - 1 = trace A + 
    (1/2)*( (trace A)^2 - trace (A^2)) + 
    (1/6)*( (trace A)^3 - 3*trace A * trace (A^2) + 2 * trace (A^3) ) := 
begin
  rw eq_27_lhs, rw eq_27_rhs,
end

lemma eq_27 {A : matrix (fin 4) (fin 4) R} :
  det (1 + A) = 1 + det A + trace A +  
    (1/2)*( (trace A)^2 - trace (A^2)) + 
    (1/6)*( (trace A)^3 - 3*trace A * trace (A^2) + 2 * trace (A^3) ) := 
begin
  repeat {rw add_assoc (1 + det A)}, rw ← sub_eq_iff_eq_add', rw add_comm (1:R) _,
  rw sub_add_eq_sub_sub,
  apply eq_27_before_last,
end

end matrix