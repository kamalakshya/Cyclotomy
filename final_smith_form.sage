def add_zeros(L, des_len):
    """
    Return a vector of desired length by extending the given vector ``L``
    by appending a string of 0s. 
    """
    if len(L) > des_len:
        raise TypeError
    
    else:
        while len(L) < des_len:
            L.extend([0])

def cyclomat(n):
    """
    Return the matrix of the inclusion map (1):

    .. latex::
       \ZZ[X]/\langle X^n - 1 \rangle \to \bigoplus_{d \mid n} \ZZ[X]/\langle \Phi_d(X) \rangle.

    However, we work over the field of rational numbers. 
    """
    div_n = divisors(n)
    R = QQ['x']
    col_list = []
    for ii in range(n):
        a_column = []
        for div in div_n:
            rem = R(x^ii).quo_rem(cyclotomic_polynomial(div))[1].coeffs()
            add_zeros(rem, euler_phi(div))
            a_column.extend(rem)
        col_list.append(a_column)
        
    return column_matrix(ZZ, col_list)

def smith_of_cyclomat(n):
    """
    Return the elementary divisors of the inclusion map (1).
    """
    return cyclomat(n).elementary_divisors()

def smith_of_adjcyclomat(n):
    """
    Return the elementary divisors of the adjoint of the matrix of the inclusion map (1). 
    """
    return cyclomat(n).adjoint().elementary_divisors()

def TensorPerm(n, m):
    if n > m:
        temp = n
        n = m
        m = temp 
    
    if gcd(n, m) != 1:
        raise TypeError
        
    col_vectors = []
    
    for jj in range(m):
        for ii in range(n):
            col_vector = [0 for i in range(n*m)]
            rem = (m*ii + n*jj)%(m*n)
            col_vector[rem] = 1
            col_vectors.append(col_vector)
            
    return column_matrix(ZZ, col_vectors)


def NewTensorPerm(n, m):
    if gcd(n, m) != 1:
        raise TypeError
        
    col_vectors = []
    
    for jj in range(m):
        for ii in range(n):
            col_vector = [0 for i in range(n*m)]
            rem = (m*ii + n*jj)%(m*n)
            col_vector[rem] = 1
            col_vectors.append(col_vector)
            
    return column_matrix(ZZ, col_vectors)


def subdivided_tensor_perm(n, m):
    N = NewTensorPerm(n, m)
    pos_list = [i*n for i in range(1, m)]
    N.subdivide(pos_list, pos_list)
    return N

#### Ordering of the tensor products ####

def lex_left(m, n):
    """
    This is the reverse lexicographic order. 
    
    Examples::
    
    sage: m =  4 
    sage: n = 3
    sage: L = [(m-i, n-j) for i in range(m) for j in range(n)]
    sage: L
    [(4, 3),
    (4, 2),
    (4, 1),
    (3, 3),
    (3, 2),
    (3, 1),
    (2, 3),
    (2, 2),
    (2, 1),
    (1, 3),
    (1, 2),
    (1, 1)]
    """
    return [(m-i, n-j) for i in range(m) for j in range(n)]

#### Addition and Multiplication for the given data structure. #####

## We use the following data structure for elements of (+)_{d divides n} ZZ[x]/\Phi_d(x):
## an element in this ring will be modelled as a list of tuples:
##  [(d, p_d): d ranges over divisors of n]
## where p_d is an element of ZZ[x]/\Phi_d(x). 

def add_vectors(vec1, vec2):
    """
    Return the sum of two elements ``vec1`` and ``vec2`` of the direct sum
    expressed in the data structure. 
    """
    vec3=[]
    for index, T in enumerate(vec1):
        vec3.append((T[0], T[1] + vec2[index][1]))
        
    return vec3

def vector_product(vec_m, vec_n):
    """
    Return the element `T_{m,n}(vec_m \otimes vec_n)` of (+)_{d divides mn} ZZ[x]/\Phi_d(x) where `vec_m` is a  vector in  
    (+)_{d divides m} ZZ[x]/\Phi_d(x) while `vec_n` is a vector in 
     (+)_{d divides n} ZZ[x]/\Phi_d(x). 
    """
    L_m , m = vec_m[0], vec_m[1]
    L_n, n = vec_n[0], vec_n[1]
    L_mn = []
    for item_m in L_m:
        for item_n in L_n:
            L_mn += [(item_m[0]*item_n[0], mult(item_m[1], item_n[1], m, n, item_m[0], item_n[0]))]
            
    return sorted(L_mn)
    
def mult(vec_d1, vec_d2, m, n, d1, d2):
    """
    Return the element `T_{d_1,d_2}(vec_d2 \otimes vec_d2)` where vec_d1 is an 
    element of ZZ[x]/Phi_d1(x) and vec_d2 is an element of \ZZ[x]/Phi_d2(x) 
    where d1 divides m and d2 divides n. 
    """
    R.<x> = ZZ[]
    return ((vec_d1.substitute(x^n))*(vec_d2.substitute(x^m))).quo_rem(cyclotomic_polynomial(d1*d2, x))[1]
    
def scale_an_element(vec, sca):
    """
    Return the element [(d, scal*p_d): d|n] for a scalar `sca` and a 
    vector `vec=[(d, p_d): d|n]` in the direct sum (+)_{d divides n} ZZ[x]/\Phi_d(x).
    """ 
    scaled_element = [] 
    for tup in vec:
        new_tup = (tup[0], sca*tup[1])
        scaled_element += [new_tup] 
        
    return scaled_element

#### Smith Vectors for the primary parts #### 

def A_by_recursion(p, n):
    """
    Uses Lemma 2.5 to construct `A_{p^n}` by recursion. 
    """
    if n == 0: 
        return matrix(ZZ, 1, 1, [1])
    else:
	M = A_by_recursion(p, n-1)
    	top_row = block_matrix([[M]*(p-1)])
    	id = matrix.identity(p^(n-1))
    	right_col = block_matrix([[-id]]*(p-1))
    	id_mat = block_diagonal_matrix([id]*(p-1))
    	return block_matrix([[top_row, M], [id_mat, right_col]])

def Vee_one(p):
    """
    Return `V_p` as in Remark 2.8. 
    """
    mat = matrix.identity(p)
    L = mat.columns()
    for i in range(p-1):
        L[p-1] += L[i]

    return column_matrix(L)
    
def Vee(p,n):
    """
    Return `V_{p^n}` as in Remark 2.8. 
    """
    if n == 1:
        return Vee_one(p)

    V = Vee(p, n-1)
    L = [[V]]*(p-1)

    col_V = block_matrix(L)
    return block_matrix([[1, col_V], [0, V]]) #, subdivide=False)

def double_u(p, n):
    """
    Return `W_{p^n}` as in equation (2.11).  
    """
    if n == 0:
       return matrix(ZZ, 1, 1, [1]) 
    else:
	W = double_u(p, n-1)
    	A = A_by_recursion(p,n-1)
    	Ab = [[A]]*(p-1)
	Ab = block_matrix(Ab).transpose()
    	return block_matrix([[Ab, p*W],[1,0]]) 

def prime_power_basis(p, n):
    """
    This is the module `\\text{SV}(p^e)` as in Section 4.  
    """
    S.<x> = ZZ[] 
    l_of_col = (double_u(p,n)).columns()
    basis = []
    for tup in l_of_col: 
        g = gcd(tup)
        new_tup = tuple()
        for ele in tup:
            new_tup += (ele/g,)
        basis_vec = []
        for i in range(n+1):
            if i == 0:
                pol = S(list(new_tup[0],))
                basis_vec += [(1, pol)]
            else:
                pol = S(list(new_tup[p^(i-1):p^(i)]))
                basis_vec += [(p^i, pol)]
        basis.append(basis_vec)
        
    return list(reversed(basis))


#### Permutation Matrices and Auxiliary Smith Vectors#####

def nz_entry_and_pos(M):
    """
    Return the non-zero entries and positions of a matrix M. 
    """
    L = []
    for r in M.rows():
        L += [[(e, i) for i, e in enumerate(r) if e != 0]]
        
    return L

def order_permutation(m, n):
    """
    Return the permutation `\\sigma_{m,n}` as in Observation 4 of Section 4.2. 
    """ 
    L = [] 
    for i in range(m):
        for j in range(1, n+1):
            L.append((j-1)*m + i + 1)
            
    return Permutation(L)

def diagonals(P, m, n):
    """
    Return the diagonal matrices `D_1` and `D_2` as in Lemma 3.5. Here, P is a permutation 
    matrix of size mn and `m` and `n` are relatively prime.
    """
    D1  = [1 for i in range(m*n)]
    D2  = [1 for i in range(m*n)]
    cycle_tup= P.cycle_tuples() 
    for cycle in cycle_tup: 
        d, u, v = xgcd(n^len(cycle), (-1)^(len(cycle)-1)*m^len(cycle))
        if d != 1: 
            raise ValueError("m and n must be relatively prime!")
        D1[cycle[0]-1] = u
        D2[cycle[0]-1] = v
    #return   (n*(matrix.diagonal(D1)) + m*(matrix.diagonal(D2))*(P.to_matrix())).determinant()  
    return  n*(matrix.diagonal(D1)) + m*(matrix.diagonal(D2))*(P.to_matrix())

def auxiliary_smith_vector(sv_m, sv_n, m, n):
    """
    This implements ``TSV(m, n, sv_m, sv_m)`` as in Section 4. Here, m and n are 
    required to be relatively prime. 
    """
    p = order_permutation(m, n)
    BM=diagonals(p, m, n)
    Index=lex_left(m, n) # Prints out indices in 1-based system. 
    L = nz_entry_and_pos(BM)
        
    sv_mn = []
    
    for r in L:
        t=[(d,  0) for d in (m*n).divisors()]
        for nzep in r:
            a=Index[nzep[1]]
            vp = vector_product((sv_m[-a[0]],m), (sv_n[-a[1]],n))
            vp_scaled = scale_an_element(vp,nzep[0])
            t = add_vectors(t, vp_scaled)
        sv_mn.append(t)

    return sv_mn

### Smith Vector For n ### 

def smith_vector(n):
    """
    This is the module ``SV(n)`` as in Section 4. 
    """
    list_of_factors = list(n.factor())
    x= list_of_factors[0]
    s=prime_power_basis(x[0],x[1])
    for l in range(1, len(list_of_factors)):
        el = list_of_factors[l]
        s1=prime_power_basis(el[0], el[1])
        s=auxiliary_smith_vector(s, s1, Integer(len(s)), Integer(len(s1)))
    
    return s

### Display Functions #### 

def display_vec(vec):
    """
    This omits the divisors from the data structure: returns [p_d: d | n] given the vector 
    vec = [(d, p_d): d | n]. 
    """
    return map(lambda x: x[1], vec)

def display_basis(basis):
    """
    Displays all elements of the basis as in `meth`:display_vec(). 
    """
    for l in basis: 
        print display_vec(l)

def return_basis(basis):
    """
    Returns all elements of the basis as in `meth`:display_vec().
    """
    n = len(basis)
    l0 = divisors(n)[:-1] + ["$\\mathbf{"+str(n)+"}$"]
    L = [l0] 
    for l in basis:
    	L.append(display_vec(l))

    return L

def oplus_add_list(lst):
    """
    Primitive version which prints an oplussed list. 
    """
    if len(lst) == 1: 
        return str(lst[0])
    else:
        return str(lst[0]) + ' \oplus ' + oplus_add_list(lst[1:]) 

def oplus_add(n):
    """
    Display with the oplus addition.
    """
    basis_n = smith_vector(n)
    for vec in basis_n:
    	vec_list = map(lambda x: x[1], vec)
	print oplus_add_list(vec_list)