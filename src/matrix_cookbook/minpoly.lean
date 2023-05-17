import linear_algebra.matrix.spectrum
import linear_algebra.eigenspace
import linear_algebra.charpoly.basic
import linear_algebra.matrix.charpoly.coeff
import linear_algebra.charpoly.to_matrix
import linear_algebra.matrix.charpoly.minpoly
import linear_algebra.matrix.to_linear_equiv
import linear_algebra.matrix.basis

open matrix polynomial
open linear_map module.End  
open_locale matrix big_operators

variables {n: Type*}[fintype n][decidable_eq n] --[nonempty n]
variables {R: Type*}[field R][is_alg_closed R]
variables {Z: matrix n n R}
variables {p: polynomial R}
#check eval₂ (algebra_map R ((n → R) →ₗ[R] n → R)) Z.mul_vec_lin p
#check (eval₂ (algebra_map R (matrix n n R)) Z p)

lemma mat_minpoly_is_linmap_minpoly (A: matrix n n R) :
  minpoly R A = minpoly R (to_lin' A) :=
begin
  -- unfold minpoly, unfold to_lin', unfold to_matrix', dsimp, 
  -- -- have : ∀(p: polynomial R), eval₂ (algebra_map R ((n → R) →ₗ[R] n → R)) A.mul_vec_lin p = 
  -- --    eval₂ (algebra_map R (matrix n n R)) A p, {
      
  -- -- },
  -- rw linear_map.to_matrix' (to_lin' A),
end

/-
dite (is_integral R A) (_.min (λ (p : polynomial R), p.monic ∧ eval₂ (algebra_map R (matrix n n R)) A p = 0))
    (λ (hx : ¬is_integral R A), 0) =
  dite (is_integral R (⇑to_lin' A))
    (λ (hx : is_integral R (⇑to_lin' A)),
       _.min
         (λ (p : polynomial R), p.monic ∧ eval₂ (algebra_map R ((n → R) →ₗ[R] n → R)) A.mul_vec_lin p = 0)
         _)
    (λ (hx : ¬is_integral R (⇑to_lin' A)), 0)
-/
-- open_locale classical matrix

-- noncomputable theory

-- open module.free polynomial matrix


-- universes u v w

-- variables {R : Type u} {M : Type v} [comm_ring R] [nontrivial R]
-- variables [add_comm_group M] [module R M] [module.free R M] [module.finite R M] (f : M →ₗ[R] M)

-- namespace linear_map

-- lemma xcharpoly_to_matrix {ι : Type w} [fintype ι] (b : basis ι R M) :
--   -- (to_matrix b b f).charpoly = f.charpoly :=
--   (minpoly R f) = minpoly R (to_matrix b b f) := 
-- begin
--   set A := to_matrix b b f,
--   set b' := choose_basis R M,
--   set ι' := choose_basis_index R M,
--   set A' := to_matrix b' b' f,
--   set e := basis.index_equiv b b',
--   set φ := reindex_linear_equiv R R e e,
--   set φ₁ := reindex_linear_equiv R R e (equiv.refl ι'),
--   set φ₂ := reindex_linear_equiv R R (equiv.refl ι') (equiv.refl ι'),
--   set φ₃ := reindex_linear_equiv R R (equiv.refl ι') e,
--   set P := b.to_matrix b',
--   set Q := b'.to_matrix b,

--   have hPQ : C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) = 1,
--   { rw [ring_hom.map_matrix_apply, ring_hom.map_matrix_apply, ← matrix.map_mul,
--       @reindex_linear_equiv_mul _ ι' _ _ _ _ R R, basis.to_matrix_mul_to_matrix_flip,
--       reindex_linear_equiv_one, ← ring_hom.map_matrix_apply, ring_hom.map_one] },

--   calc A.charpoly = (reindex e e A).charpoly : (charpoly_reindex _ _).symm
--   ... = (scalar ι' X - C.map_matrix (φ A)).det : rfl
--   ... = (scalar ι' X - C.map_matrix (φ (P ⬝ A' ⬝ Q))).det :
--     by rw [basis_to_matrix_mul_linear_map_to_matrix_mul_basis_to_matrix]
--   ... = (scalar ι' X - C.map_matrix (φ₁ P ⬝ φ₂ A' ⬝ φ₃ Q)).det :
--     by rw [reindex_linear_equiv_mul, reindex_linear_equiv_mul]
--   ... = (scalar ι' X - (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
--   ... = (scalar ι' X ⬝ C.map_matrix (φ₁ P) ⬝ (C.map_matrix (φ₃ Q)) -
--     (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det :
--       by { rw [matrix.mul_assoc ((scalar ι') X), hPQ, matrix.mul_one] }
--   ... = (C.map_matrix (φ₁ P) ⬝ scalar ι' X ⬝ (C.map_matrix (φ₃ Q)) -
--     (C.map_matrix (φ₁ P) ⬝ C.map_matrix A' ⬝ C.map_matrix (φ₃ Q))).det : by simp
--   ... = (C.map_matrix (φ₁ P) ⬝ (scalar ι' X - C.map_matrix A') ⬝ C.map_matrix (φ₃ Q)).det :
--     by rw [← matrix.sub_mul, ← matrix.mul_sub]
--   ... = (C.map_matrix (φ₁ P)).det * (scalar ι' X - C.map_matrix A').det *
--     (C.map_matrix (φ₃ Q)).det : by rw [det_mul, det_mul]
--   ... = (C.map_matrix (φ₁ P)).det * (C.map_matrix (φ₃ Q)).det *
--     (scalar ι' X - C.map_matrix A').det : by ring
--   ... = (scalar ι' X - C.map_matrix A').det : by rw [← det_mul, hPQ, det_one, one_mul]
--   ... = f.charpoly : rfl
-- end

-- end linear_map