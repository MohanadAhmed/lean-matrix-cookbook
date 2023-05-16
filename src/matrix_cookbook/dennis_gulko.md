# Denis Gulko's answer at [math.stackexchange#101275](https://math.stackexchange.com/questions/101275/roots-of-minimal-and-characteristic-polynomials) 
 pointed out by Eric Wieser on Zulip Chat [Eigenvalues of matrices: Trace Determinants and others](https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Eigenvalues.20of.20matrices.3A.20Trace.20Determinants.20and.20others/near/358513935)

1. Let $f(x) \in \mathbb{C}[x]$ be any polynomial. 

2. Let $\lambda$ be an eigenvalue of $A \in \mathbb{C}(m \times m)$ with an associated eigenvector $v$. 

   (using which definition of eigenvalue??)

3. He then claims that $f(A)$ has an eigenvalue of $f(\lambda)$ with an associated eigenvector $v$ the same as above i.e. 

$$ f(A) v = f(\lambda)v $$.

> Argument: Recall that $Av = \lambda v$ and $A^2v = A(\lambda v) = \lambda (A v) = \lambda ^2 v$. In general, by induction, one can show that $A^n v = \lambda^n v$. Thus any polynomial $f(x) = a_nx^n + a_{n-1}x^{n-1} + \ldots + a_1x + a_0$ can be evaluated in the matrix $A$ as $f(A) = a_nA^n + a_{n-1}A^{n-1} + \ldots + a_1A + a_0I_m$. Applying this to the vector v gives $f(A)v = (a_n\lambda^n + a_{n-1}\lambda^{n-1} + \ldots + a_1\lambda + a_0)v = f(\lambda)v$ Hence:

4. The statement above is true for any eigenvalue of the matrix $A$.

5. Let $\chi_A(x)$ be the characteristic polynomial of A. Let $\mu_A(x)$ be the minimal polynomial of A.

> It seems he is going to use the eigenvalue as root of the characteristic polynomial not the minimal polynomial as in mathlib (see [docs#module.End.has_eigenvalue_iff_is_root](https://leanprover-community.github.io/mathlib_docs/linear_algebra/eigenspace.html#module.End.has_eigenvalue_of_is_root)) with the statement being: 
> 
> `f.has_eigenvalue μ ↔ (minpoly K f).is_root μ`
>
> <span style="color:red;"> Thinking about it again seems what I said above is a bit "circular" </span>

6. Applying both polynomials to the statement in 3 we get the two equations below which we will call A1 and A2.
$$ \begin{aligned} 
\text{A1:} \quad \mu_A({A})v &= \mu_A({\lambda})v \\ 
\text{A2:} \quad \chi_A({A})v &= \chi_A({\lambda})v 
\end{aligned} $$ 

7. The author now states:
>Now let $λ$ be a root of $\chi_A(t)$. Thus $λ$ is an eigenvalue and so has an associated eigenvector $v \neq 0$. Using the claim, we get $0=\mu_A(A)⋅v=\mu_A(\lambda)⋅v$ (since $\mu_A(A)=0)$. Since $v \neq 0$, we get $\mu_A(\lambda)=0$.

Trying to follow the logic of the statements:
> a. Now let $λ$ be a root of $\chi_A(t)$.
>  $$ \chi_A(\lambda) = 0 $$

> b. Thus $λ$ is an eigenvalue and so has an associated eigenvector $v \neq 0$.
>  $$ \exists v \in \mathbb{C}^m, v \neq 0 \quad | \quad Av = \lambda v$$

> c. Using the claim, we get $0=\mu_A(A)⋅v=\mu_A(\lambda)⋅v$ (since $\mu_A(A)=0)$. <span style="color:red;"> Which particular claim is he talking about???

<!-- 7. Recall that the minimal polynomial divides the characteristic polynomial i.e. $\exists z(x), \chi_A(x) = \mu_A(x) z(x)$ -->
