import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import linear_algebra.matrix.determinant
import data.matrix.notation

variables {R : Type*}

open_locale matrix big_operators
open matrix

-- anyone looking at the cookbook likely only cares about fields anyway!
variables [field R]

lemma eq_27 {A : matrix (fin 4) (fin 4) R} :
  det (1 + A) = 1 + det A + trace A + 
              1/2*trace A^2 - 1/2*trace (A^2) + 
              1/6*trace A^3 - 1/2*trace A * trace (A^2) + 1/3 * trace (A^3) := 
begin
  rw matrix.trace,
  rw fin.sum_univ_four, simp only [diag, one_div],
  
end