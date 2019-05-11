from IPython.display import display, Math, Latex
from types import FunctionType

def L_to_poly(L):
    """ Returns a polynomial whose coefficients are given by the list L"""
    x = QQ['x'].0
    return sum(L[n]*x**n for n in range(len(L)))

def poly_to_L(f):
    """ Returns a list of coefficients of f"""
    try:
        return f.coefficients(sparse=False)
    except AttributeError:
        # f is a constant polynomial, which is just a number and has no coefficients() method
        return [f]

def prod_roots(L1,L2):
    """ Returns a list of coefficients of the polynomial whose roots are precisely
    the products of a root of the polynomial with coefficients L1 and a root
    of the polynomial with coefficients L2"""
    A = parent(L1[0])
    R.<x> = PolynomialRing(A)
    SS.<z> = PolynomialRing(A)
    S.<y> = PolynomialRing(SS)
    f,g = sum(a*x^i for i,a in enumerate(L1)),sum(a*x^i for i,a in enumerate(L2))
    ff = f.subs({x:y})
    gg = g.subs({x:S(y)*S(z)}).reverse()
    h = ff.resultant(gg)
    hh = h.subs({z:x})
    hh = hh/hh.coefficients()[-1]
    return hh.coefficients(sparse=False)

def subs(L):
    """ Generator for lists of non-negative integers whose entries are bounded by L"""
    if len(L) == 0:
        yield []
    else:
        for n in range(L[0]+1):
            for LL in subs(L[1:]):
                yield [n] + LL

def convolve(L1,L2):
    """ Returns the convolution of L1 and L2"""
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
        for i in range(D):
            if T[i] is not None:
                if TT[i%n] is None:
                    TT[i%n] = T[i]
                elif TT[i%n] != T[i]:
                    break
        else:
            return TT
    raise Exception("reduce_congruence ran off the end")

class Recurrence(Ring):
    def __init__(self,base=QQ):
        Ring.__init__(self,base)
        self._populate_coercion_lists_()    
    
    def _repr_(self):
        return "The ring of linear recurrent sequences over "+str(self.base())
    
    def _element_constructor_(self,s1,s2=None):
        return RecurrenceElement(self,s1,s2)
    
    def _coerce_map_from_(self,S):
        # Can coerce from rings that coerce into base, or rings of recurrent sequences
        # whose base rings coerce into base
        if self.base().coerce_map_from(S):
            return True
        if isinstance(S,Recurrence) and self.base().coerce_map_from(S.base()):
            return True
        return False
    
    def fib(self):
        """ Returns the Fibonacci sequence"""
        return RecurrenceElement(self,([-1,-1,1],[0,1]))
    
    def lucas(self):
        """ Returns the Lucas sequence"""
        return RecurrenceElement(self,([-1,-1,1],[2,1]))

    def trib(self,n=3):
        """ Returns the generalized tribonacci sequence"""
        init_vals = [0 for _ in range(n-1)] + [1]
        char_poly = [-1 for _ in range(n)] + [1]
        return RecurrenceElement(self,(char_poly,init_vals))

    def charac(self,a,n):
        """ Returns the characteristic sequence of a mod n"""
        init_vals = [1 if i==a else 0 for i in range(n)]
        char_poly = [-1] + [0 for _ in range(n-1)] + [1]
        return RecurrenceElement(self,(char_poly,init_vals))
        
    def exp(self,a):
        """ Returns the sequence a^n"""
        return RecurrenceElement(self,[-a,1],[1])


class RecurrenceElement(RingElement):
    def __init__(self,parent,data=0,data2=None):
        RingElement.__init__(self,parent)
        
        if data2 is not None:
            data = (data,data2)
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
                self.char_poly = [-parent.base().one(),parent.base().one()]
                self.init_vals = [parent.base()(data)]
            except:
                raise ValueError("Could not build recurrent sequence")
        if not rec_test(self.char_poly,self.init_vals) or len(self.init_vals) < len(self.char_poly)-1:
            raise ValueError("Data does not determine a unique recurrent sequence")
        self.reduce()
        
    def base(self):
        return parent(self).base()
    
    def _repr_(self):
        return self.show(string=True)
        #return "A recurrent sequence over "+str(self.base())
    
    def _add_(self, other):
        R = parent(self)(0)
        P1 = self.char_poly
        P2 = other.char_poly
        R.char_poly = convolve(P1,P2)
        M = len(P1)+len(P2)-2
        L1 = self.get_range(M)
        L2 = other.get_range(M)
        R.init_vals = [L1[n]+L2[n] for n in range(M)]
        R.reduce()
        return R
    
    def _mul_(self,other):
        assert parent(self) is parent(other)
        R = parent(self)(0)
        R.char_poly = prod_roots(self.char_poly,other.char_poly)
        m,n = len(self.init_vals),len(other.init_vals)
        L1 = self.get_range(m*n)
        L2 = other.get_range(m*n)
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
        a,b = n.start,n.stop
        if a is None:
            a = 0
        return self.get_range(a,b)
    
    def __eq__(self,other):
        if not isinstance(other,RecurrenceElement):
            other = parent(self)(other)
        self.reduce()
        other.reduce()
        return self.init_vals == other.init_vals and self.char_poly == other.char_poly
    
    def shift(self,n):
        L = self.get_range(n,n+len(self.init_vals))
        new_base = parent(self.base()(0) + sum(L))
        R = parent(self) if new_base is self.base() else Recurrence(new_base)
        return R(list(self.char_poly),L)
            
    def get_range(self,a,b=None):
        """ Returns a list of values from the sequence"""
        if b is None:
            a,b = 0,a
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
    
    def characteristic_polynomial(self):
        """ Returns the characteristic polynomial of self, as a polynomial in x"""
        R.<x> = PolynomialRing(self.base())
        return sum(self.char_poly[n]*x**n for n in range(len(self.char_poly)))
        
        
    def reduce(self):
        """ Ensures characteristic polynomial is minimal"""
        base = self.base
        n = len(self.char_poly)
        T = []
        for i in range(n):
            T.append(self[i:i+n-1])
            M = matrix(T)
            if M.rank() == i:
                break
        else:
            raise Exception("This should not happen")
        V = M.left_kernel()
        B = V.basis()
        assert len(B) == 1
        L = [x/B[0][-1] for x in B[0]]
        self.char_poly = L
        self.init_vals = self.init_vals[:i]
        return None
    
   
    def splitting_field(self):
        var('a')
        K = (self.characteristic_polynomial().splitting_field(a))
        return K
    
    def gal(self):
        return self.galois_group()
    
    def companion(self):
        """ Returns the companion matrix of the characteristic polynomial of self"""
        self.reduce()
        return matrix(self.splitting_field(),companion_matrix(self.characteristic_polynomial())).transpose()
    
    def j_form(self):
        """ Returns the Jordan canonical form of the companion matrix of self"""
        M = self.companion()
        D,P = tuple(M.jordan_form(transformation=True))
        return (D,P,P.inverse())
    
    def L_L(self):
        """ L is a splitting field of the characteristic polynomial of self
        There is a unique Galois-invariant element sum a_i\otimes b_i of L\otimes L
        such that self(p) is congruent to sum a_i*frob_p(b_i) mod p for all p.
        L_L(self) returns [(a_i,b_i)]"""
        assert self.base() is QQ or self.base() is ZZ
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
        """ Returns a list of potentially bad primes.
        For every p not on this list, it is
        guaranteed that L is unramified at p, and
        that a_p \equiv 0 \mod p if and only if
        r.A()[phi_p] = 0. The list of potentially bad primes is
        not necessarily minimal."""
        T = []
        L = self.j_form()
        L = flatten([[list(x) for x in Y] for Y in L])
        L += self.init_vals
        L = [x.denominator() for x in L]
        for x in set(L):
            add_primes(T,x)
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
        """ Returns the Galois group of the splitting field of the characteristic polynomial of self"""
        K = self.splitting_field()
        return K.galois_group()
    
    def A(self):
        """ Returns a dictionary {g:f(g)} for the element of A(L) associated with the recurrence self"""
        L = self.L_L()
        G = self.galois_group()
        return {g:sum(s[0]*g(s[1]) for s in L) for g in G}
    
    def CC(self):
        """ Returns a list [(conjugacy class in Galois group, minimal polynomial of value on that class)]"""
        G = self.gal()
        A = self.A()
        D = [(c.an_element(),minimal_polynomial(A[c.an_element()])) for c in G.conjugacy_classes()]
        return D
    
    def density(self):
        """ Returns the natural density of the set {p: a_p = 0 mod p}"""
        A = self.A()
        n = 0
        d = 0
        for g in A:
            d += 1
            if A[g] == 0:
                n += 1
        return n/d
    
    def n(self):
        """ Returns the order of the recurrence relation satisfied by self"""
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
            for n in range(D):
                if gcd(n,D) == 1 and T[n] is None:
                    break
            else:
                return reduce_congruence(T)
            
    def min_poly_p(self,factors=False,display=False):
        """ Computes the minimal polynomial of a_p \mod p,
        and the density for each irreducible factor"""
        A = self.A()
        n = len(A)
        D = {}
        T = None
        for g in A:
            P = minimal_polynomial(A[g])
            if T is None:
                T = P
            else:
                T = lcm(T,P)
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
        if factors:
            return D
        else:
            return T
    
    def disc(self):
        """ Returns the discriminant"""
        return self.splitting_field().disc()
    
    def is_abelian(self):
        return self.galois_group().is_abelian()
    
    def disp(self,mathjax=True,string=False):
        """ Displays a description of self using MathJax
        If mathjax is False, won't use MathJax
        If string is True, returns a string but doesn't display"""
        self.reduce()
        k = self.n()
        assert self.char_poly[-1] == 1
        V = []
        for n in range(k):
            V.append('x%i'%n)
        R = PolynomialRing(self.base(),V)
        V = R.gens()
        E = sum(-V[-n-1]*self.char_poly[n] for n in range(k-1))
        S =  "a_{n} = " + latex(E)
        for n in range(1,k):
            S = S.replace(latex(V[n]),"a_{n-%i}"%n)
        if mathjax:
            S = "\\text{Recurrent sequence over %s:}\\\\"%self.base() + S + "\\\\"
            for n in range(self.n()-1):
                S = S + "a_{%i}="%n + latex(self.init_vals[n]) + ",\,\,"
        else:
            S = S.replace("\\frac{","").replace('}{','/').replace("\\,","").replace("  "," ").replace("} a"," a")
            for n in range(10):
                S = S.replace(str(n)+' a',str(n)+'*a')
            S = "Recurrent sequence over %s:"%self.base() + '\n' + S + '\n'
            for n in range(self.n()-1):
                S = S + "a_%i = "%n + str(self.init_vals[n]) + ", "
        if k >= 2:
            S = S[:(-5 if mathjax else -2)]
        if string:
            return S
        else:
            if mathjax:
                display(Math(S))
            else:
                print S
            return None
        raise Exception("Disp() ran off the end")
    
    def show(self,string=False):
        """ Displays self without MathJax"""
        return self.disp(mathjax=False,string=string)
    
    def decide(self):
        """ Returns True if there is a prime p for which a_p = 0 mod p,
        False otherwise"""
        if self.density() == 0:
            for p in self.bad_primes():
                if numerator(self.e(p))%p == 0:
                    break
            else:
                return True
        return False

def is_normal(x):
    """ Returns True if x is a normal element (its Galois orbit is a basis for underlying number field),
    returns False otherwise"""
    L = parent(x)
    V,_,f = L.vector_space()
    G = L.galois_group()
    return not V.are_linearly_dependent([f(g(x)) for g in G])

def recurrence_from_function(L,phi,x=None):
    """ Returns a recurrent sequence (a_n)
    such that phi(frob_p) = a_p mod p, where phi is a function Gal(L/Q) --> L
    satisfying phi(ghg^{-1}) = g(phi(h))
    This function is not deterministic"""
    b = L.gens()[0]
    G = L.galois_group()
    LL = list(G)
    n = len(LL)
    if x is None:
        # Find normal element
        while True:
            x = L.random_element()
            if is_normal(x):
                break
    else:
        if not is_normal(x):
            raise ValueError("Third argument needs to be a normal element")
    if isinstance(phi,FunctionType):
        # Turn phi into a list
        phi = [phi(g) for g in LL]
    elif isinstance(phi,dict):
        phi = [phi[g] for g in LL]
    M = matrix([[h(g(x)) for g in LL] for h in LL])
    try:
        v = M.inverse()*vector(phi)
    except ZeroDivisionError:
        # Should not happen
        raise ValueError("Cannot tell if third argument is normal")
    assert M*v == vector(phi)
    assert [sum(v[j]*g(h(x)) for j,h in enumerate(LL)) for g in LL] == phi
    char_poly = x.minpoly().coefficients(sparse=False)
    init_vals = [sum(v[j]*(LL[j](x))**i for j in range(n)) for i in range(n)]
    R = Recurrence(QQ)
    return R(char_poly,init_vals)

def recurrence_from_conjugacy_class(C):
    """ Returns a recurrent sequence (a_n) such that a_p = 1 mod p if the 
    frobenius at p is in the conjugacy class C, a_p = 0 mod p otherwise
    This function is not deterministic"""
    G = group_from_subset(C)
    phi = {g:1 if g in C else 0 for g in G}
    return recurrence_from_function(G.number_field(),phi)
    
def group_from_subset(S):
    """ Returns the Galois group with S as a subset"""
    return S.an_element().as_hom().domain().galois_group() # This is ridiculous. There must be a better way
    