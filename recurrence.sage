from IPython.display import display, Math, Latex
from types import FunctionType

X = QQ['X'].0
var('a')

def L_to_poly(L):
    """Returns a polynomial whose coefficients are given by the list L"""
    x = QQ['x'].0
    return sum(L[n]*x**n for n in range(len(L)))

def poly_to_L(f):
    """Returns a list of coefficients of f"""
    try:
        return f.coefficients(sparse=False)
    except AttributeError:
        # f is a constant polynomial, which is just a number and has no coefficients() method
        return [f]

def prod_roots(L1,L2):
    """Returns a list of coefficients of the polynomial whose roots are precisely
    the products of a root of the polynomial with coefficients L1 and a root
    of the polynomial with coefficients L2"""
    R.<x> = PolynomialRing(QQ)
    f = R(L_to_poly(L1))
    g = R(L_to_poly(L2))
    K.<t> = (f*g).splitting_field()
    S.<x> = PolynomialRing(K)
    h = prod(prod((x-s[0]*t[0])**(s[1]*t[1]) for s in f.roots(K))\
             for t in g.roots(K))
    poly_to_L(h)
    return [QQ(x) for x in poly_to_L(h)]

def subs(L):
    """ Generator for lists of non-negative integers whose entries are bounded by L"""
    if len(L) == 0:
        yield []
    else:
        for n in range(L[0]+1):
            for LL in subs(L[1:]):
                yield [n] + LL

def convolve(L1,L2):
    """Returns the convolution of L1 and L2"""
    a1,a2 = len(L1),len(L2)
    if a1 == 0 or a2 == 0:
        return []
    return [sum(L1[i]*L2[n-i] for i in range(max(n-a2+1,0),min(a1,n+1))) for n in range(a1+a2-1)]

def rec_test(P,L):
    """ Returns True if L satisfies the recurrence P, False otherwise"""
    for n in range(len(L)-len(P)+1):
        if sum(P[i]*L[n+i] for i in range(len(P))) != 0:
            return False
    return True

def LL_to_seq(L,n):
    return sum(s[0]*s[1]**n for s in L)

def add_primes(T,x):
    """ Appends the prime divisors of x to T, returns T"""
    for s in factor(x):
        if s[0] not in T:
            T.append(s[0])
    return T


def reduce_congruence(T):
    D = len(T)
    for n in range(1,D+1):
        if D%n != 0:
            continue
        TT = [None for _ in range(n)]
        B = True
        for i in range(D):
            if T[i] is not None:
                if TT[i%n] is None:
                    TT[i%n] = T[i]
                elif TT[i%n] != T[i]:
                    B = False
                    break
        if B:
            return TT
    raise Exception("reduce_congruence ran off the end")

class Recurrence(Ring):
    def __init__(self,base=QQ):
        Ring.__init__(self,base)
        self._populate_coercion_lists_()    
    
    def _repr_(self):
        return "The ring of linear recurrent sequences over "+str(self.base())
    
    def _element_constructor_(self,s):
        return RecurrenceElement(self,s)
    
    def _coerce_map_from_(self,S):
        # Can coerce from rings that coerce into base, or rings of recurrent sequences
        # whose base rings coerce into base
        if self.base().coerce_map_from(S):
            return True
        if isinstance(S,Recurrence) and self.base().coerce_map_from(S.base()):
            return True
        return False
    
    def fib(self):
        # Fibonacci sequence
        return RecurrenceElement(self,([-1,-1,1],[0,1]))
    
    def lucas(self):
        # The Lucas sequence
        return RecurrenceElement(self,([-1,-1,1],[2,1]))

    def trib(self,n=3):
        # Generalized tribonacci sequence
        init_vals = [0 for _ in range(n-1)] + [1]
        char_poly = [-1 for _ in range(n)] + [1]
        return RecurrenceElement(self,(char_poly,init_vals))

    def charac(self,a,n):
        # Characteristic sequence of a mod n
        init_vals = [1 if i==a else 0 for i in range(n)]
        char_poly = [-1] + [0 for _ in range(n-1)] + [1]
        return RecurrenceElement(self,(char_poly,init_vals))


class RecurrenceElement(RingElement):
    def __init__(self,parent,data=0):
        RingElement.__init__(self,parent)
        if isinstance(data,RecurrenceElement):
            try:
                self.char_poly = [parent.base()(x) for x in data.char_poly]
                self.init_vals = [parent.base()(x) for x in data.init_vals]
            except:
                raise ValueError("Could not convert recurrent sequence")
        elif isinstance(data,tuple):
            self.char_poly = [parent.base()(x) for x in data[0]]
            self.init_vals = [parent.base()(x) for x in data[1]]
        else:
            try:
                self.char_poly = [parent.base().one(),-parent.base().one()]
                self.init_vals = [parent.base()(data)]
            except:
                raise ValueError("Could not build recurrent sequence")
        self.reduce()
        
    def base(self):
        return parent(self).base()
    
    def _repr_(self):
        return "A recurrent sequence over "+str(self.base())
    
    def _add_(self, other):
        R = parent(self)(0)
        P1 = self.char_poly
        P2 = other.char_poly
        R.char_poly = convolve(P1,P2)
        M = len(P1)+len(P2)-2
        L1 = self.get_range(0,M)
        L2 = other.get_range(0,M)
        R.init_vals = [L1[n]+L2[n] for n in range(M)]
        R.reduce()
        return R
    
    def _mul_(self,other):
        assert parent(self) is parent(other)
        R = parent(self)(0)
        R.char_poly = prod_roots(self.char_poly,other.char_poly)
        m,n = len(self.init_vals),len(other.init_vals)
        L1 = self.get_range(0,m*n)
        L2 = other.get_range(0,m*n)
        R.init_vals = [L1[i]*L2[i] for i in range(m*n)]
        R.reduce()
        return R
    
    def _sub_(self,other):
        return self + other*(-1)
    
    
    def _neg_(self):
        return (-1)*self
    
    def _pow_(self,n):
        if n in ZZ and n >= 0:
            if n == 0:
                return self.parent.one()
            else:
                return self*self^(n-1)
        else:
            return self._inv_()^(-n)
    
    def _inv_(self):
        if self.n() > 2:
            raise ValueError("Recurrent sequence is not invertible")
        try:
            L = [x^(-1) for x in self.init_vals]
            char_poly = self.char_poly[::-1]
            return parent(self)((char_poly,L))
        except:
            raise ValueError("Recurrent sequence is not invertible")
    
    def _div_(self,other):
        return self*other._inv_()
    
    def __getitem__(self,n):
        if not isinstance(n,slice):
            return self.get_range(n,n+1)[0]
        return self.get_range(n.start,n.stop)
      
    def shift(self,n,in_place=False):
        if in_place:
            self.init_vals = self.get_range(n,n+len(self.init_vals))
            T = self
        else:
            r = parent(self)(0)
            r.init_vals = self.get_range(n,n+len(self.init_vals))
            r.char_poly = list(self.char_poly)
            T = r
        return T
            
    def get_range(self,a,b):
        # Returns a list of values from the sequence
        assert a <= b
        L = list(self.init_vals)
        P = self.char_poly
        while len(L)<b:
            L.append(-sum(P[-i-1]*L[-i] for i in range(1,len(P))) / P[-1])
        for _ in range(0,-a):
            L.insert(0,-sum(P[i]*L[i-1] for i in range(1,len(P))) / P[0])
        if a>0:
            L = L[a:]
        L = L[:b-a]
        return L
    
    def POLY(self):
        return sum(self.char_poly[n]*X**n for n in range(len(self.char_poly)))
    
    def reduce(self):
        # Minimizes characteristic polynomial
        if self.base() is not QQ:
            # Don't even try to reduce unless base ring is Q
            return None
        assert len(self.init_vals) >= len(self.char_poly)-1
        self.init_vals = self.init_vals[:len(self.char_poly)-1]
        F = self.POLY().factor()
        L = [x[1] for x in list(F)]
        PL = [x[0] for x in list(F)]
        for LL in subs(L):
            P = prod(PL[n]**LL[n] for n in range(len(LL)))
            P = P + X
            P = P - X
            if rec_test(P.coefficients(sparse=False),self.init_vals):
                self.char_poly = P.coefficients(sparse=False)
                self.init_vals = self.init_vals[:len(self.char_poly)-1]
                return None
        raise Exception('reduce(self) ran off the end')
    
    def splitting_field(self):
        var('a')
        K = (self.POLY().splitting_field(a))
        return K
    
    def gal(self):
        return self.galois_group()
    
    def companion(self):
        # companion matrix
        self.reduce()
        return matrix(self.splitting_field(),companion_matrix(self.POLY())).transpose()
    
    def j_form(self):
        M = self.companion()
        D,P = tuple(M.jordan_form(transformation=True))
        return (D,P,P.inverse())
    
    def L_L(self):
        # Returns a list of pairs, representing an element of L\otimes L
        D,P,Pi = self.j_form()
        D = matrix(D)
        n = len(D.rows())
        if n == 0:
            return []
        u = [1] + [0 for _ in range(n-1)]
        U = vector(u)*P
        V = Pi*vector(self.init_vals)
        L = []
        for i in range(n):
            L.append((U[i]*V[i],D[i][i]))
        return L
    
    
    
    def bad_primes(self):
        """Returns a list of potentially bad primes.
        For every p not on this list, it is
        guaranteed that L is unramified at p, and
        that a_p \equiv 0 \mod p if and only if
        r.A()[phi_p] = 0. The list of potentially bad primes is
        not necessarily minimal."""
        T = []
        L = self.j_form()
        L = flatten([[list(x) for x in Y] for Y in L])
        L += self.init_vals
        for x in L:
            add_primes(T,x.denominator())
        add_primes(T,self.splitting_field().disc())
        A = self.A()
        for g in A:
            if A[g] != 0:
                add_primes(T,norm(A[g]*A[g].denominator()))
        for n in range(1,len(self.char_poly)):
            add_primes(T,n)
        T.sort()
        return T
    
    def galois_group(self):
        """Returns the Galois group of the splitting field of the characteristic polynomial of self"""
        K = self.splitting_field()
        return K.galois_group()
    
    def A(self):
        """ Returns a dictionary {g:f(g)} for the element of A(L) associated with the recurrence self"""
        L = self.L_L()
        G = self.galois_group()
        return {g:sum(s[0]*g(s[1]) for s in L) for g in G}
    
    def CC(self):
        """Returns a list [(conjugacy class in Galois group, minimal polynomial of value on that class)]"""
        G = self.gal()
        A = self.A()
        D = [(c.an_element(),minimal_polynomial(A[c.an_element()])) for c in G.conjugacy_classes()]
        return D
    
    def density(self):
        """Returns the natural density of the set {p: a_p = 0 mod p}"""
        A = self.A()
        n = 0
        d = 0
        for g in A:
            d += 1
            if A[g] == 0:
                n += 1
        return n/d
    
    def n(self):
        """Returns the order of the recurrence relation satisfied by self"""
        self.reduce()
        return len(self.char_poly)
    
    def congruences(self):
        """ Returns a list of length n whose i-th entry is congruent
        to a_p mod p whenever p = i mod n"""
        G = self.galois_group()
        K = self.splitting_field()
        if not G.is_abelian():
            raise Exception("G must be abelian")
        assert len(K.gens()) == 1
        A = self.A()
        a = K.gen(0)
        D = abs(K.disc())
        T = [None for _ in range(D)]
        for p in primes(D+1,10000):
            for g in G:
                if ((g(a)-a**p)/p).is_integral():
                    if T[p%D] is None:
                        T[p%D] = A[g]
                    elif A[g] != T[p%D]:
                        assert False
            B = True
            for n in range(D):
                if gcd(n,D) == 1 and T[n] is None:
                    B = False
                    break
            if B:
                return reduce_congruence(T)
            
    def min_poly_p(self,display=True):
        """Computes the minimal polynomial of a_p \mod p,
        # and the density for each irreducible factor"""
        A = self.A()
        n = len(A)
        D = {}
        for g in A:
            P = minimal_polynomial(A[g])
            if P in D:
                D[P] += 1/n
            else:
                D[P] = 1/n
        if display:
            K = D.keys()
            K.sort(key=lambda f:f.degree())
            for q in K:
                print "%r:\t"%D[q]+str(q)
            return None
        return D
    
    def disc(self):
        """Returns the discriminant"""
        return self.splitting_field().disc()
    
    def is_abelian(self):
        return self.galois_group().is_abelian()
    
    def disp(self,tex=False):
        """disp(self) Renders a description of self in tex
        disp(self,tex=True) returns a string which is tex code"""
        self.reduce()
        k = self.n()
        assert self.char_poly[-1] == 1
        V = []
        for n in range(k):
            V.append(var('x%i'%n))
        E = sum(-V[-n-1]*self.char_poly[n] for n in range(k-1))
        S =  "a_{n} = " + latex(E)
        for n in range(1,k):
            S = S.replace(latex(V[n]),"a_{n-%i}"%n)
        S = "\\text{Recurrent sequence:}\\\\" + S + "\\\\"
        for n in range(self.n()-1):
            S = S + "a_{%i}="%n + str(self.init_vals[n]) + ",\,\,"
        S = S[:-5]
        if tex:
            return S
        else:
            display(Math(S))
            return None
    
    def e(self,n):
        return self.get_range(n,n+1)[0]
    
    def decide(self):
        """ Returns True if there is a prime p for which a_p = 0 mod p,
        False otherwise"""
        if self.density() == 0:
            B = True
            for p in self.bad_primes():
                if numerator(self.e(p))%p == 0:
                    B = False
                    break
            if B:
                return True
        return False

def recurrence_from_class(L,phi,x=None):
    """Returns a recurrent sequence (a_n)
    such that phi(frob_p) = a_p mod p, where phi is a function Gal(L/Q) --> L
    satisfying phi(ghg^{-1}) = g(phi(h))"""
    b = L.gens()[0]
    G = L.galois_group()
    LL = list(G)
    n = len(LL)
    if x is None:
        # Find normal element
        coord_b = b.coordinates_in_terms_of_powers()
        while True:
            x = L.random_element()
            B = transpose(matrix([coord_b(g(x)) for g in G]))
            if B.det() != 0: 
                break
    
    if isinstance(phi,FunctionType):
        # Turn phi into a list
        phi = [phi(g) for g in LL]
    
    M = matrix([[LL[i](LL[j](x)) for i in range(n)] for j in range(n)])
    try:
        v = M.inverse()*vector(phi)
    except ZeroDivisionError:
        raise Exception("Third argument needs to be a normal element")
    
    assert [sum(v[j]*g(LL[j](x)) for j in range(n)) for g in LL] == phi
    
    char_poly = x.minpoly().coefficients(sparse=False)
    init_vals = [sum(v[j]*(LL[j](x))^i for j in range(n)) for i in range(n)]
    R = Recurrence(QQ)
    return R((char_poly,init_vals))