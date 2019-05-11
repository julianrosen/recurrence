load('recurrence.sage')
from random import shuffle,randint

R = Recurrence(QQ) # Ring of recurrent sequences over Q

####
#
# Verify an identity for Fibonacci numbers
#
####
F = R.fib()   # Fibonacci sequence
F.show()      # Displays F
F.disp()      # Displays F using MathJax (in Jupyter)
print F[3:12] # Some elements of F
alt = R.exp(-1)  # Alternating sequence (-1)^n
assert F.shift(1)*F.shift(-1) - F^2 == alt  # Verify the identity F_{n+1}*F_{n-1} - F_n^2 == (-1)^n
for n in range(30):
    assert F[n+1]*F[n-1] - F[n]^2 == alt[n]

    
####
#
# Find recurrence relation/initial values of recurrence built from other recurrence
#
####
F = R.fib() # Fibonacci sequence
T = R.trib() # Tribonacci sequence
power_2 = R.exp(2) # Sequence a_n = 2^n
r = F+3-T^2/power_2
r.show()

####
#
# Find minimal polynomial of element of prod_p F_p / sum_p F_p coming from recurrent sequence
#
####
char_poly = [randint(-10,10) for _ in range(3)]+[1]
init_vals = [randint(-10,10) for _ in range(3)]
r = R(char_poly,init_vals) # A recurrent sequence
r.show()
f = r.min_poly_p() # Minimal polynomial
print ""
print "Minimal polynomial of (a_p mod p):"
print f
x = f.variables()[0]
BP = r.bad_primes()
prime_max = 200
r_list = r[:prime_max]
count = 0
for p in prime_range(2,prime_max): # Check that the minimal polynomial actually annihilates sequence mod p
    if p in BP:
        continue
    count += 1
    K = GF(p)
    poly.<y> = PolynomialRing(GF(p))
    ff = poly(f)
    z = K(r_list[p])
    assert ff.subs({y:z}) == K(0)


####
#
# Choose a conjugacy class in the Galois group of a number field
# Build a recurrent sequence such that a_p mod p is the 1 if 
# frob_p is in the conjugacy class, 0 otherwise. Check this numerically
#
####
x = PolynomialRing(QQ,'x').gens()[0]
degree = 3 # Our field will be the splitting field of a random polynomial of at most this degree (slow if degree >= 4)
f = x^degree + sum(randint(-10,10)*x^i for i in range(degree))
f = f.factor()[0][0] # Random irreducible polynomial
L.<y> = (f).splitting_field() # L/Q is a finite Galois extension
print "Number field of degree %i"%L.degree()
O = L.ring_of_integers()
G = L.galois_group() # Galois group of L
CC = G.conjugacy_classes() # List of conjugacy classes
shuffle(CC); C = CC[0] # A random conjugacy class
r = recurrence_from_conjugacy_class(CC[0]) # Build the recurrence
BP = r.bad_primes() # Set of bad primes
prime_max = 300
r_list = r[:prime_max]
count = 0
for p in prime_range(2,prime_max):
    if p in BP:
        continue
    count += 1
    P = O.ideal(p).factor()[0][0] # Prime of L lying over p
    assert P.ramification_index() == 1
    CC = G.conjugacy_class(G.artin_symbol(P)) # Conjugacy class of the Frobenius at p
    K = GF(p)
    assert K(r_list[p]) == (K(1) if C==CC else K(0))
print "Verified for %i primes"%count



####
#
# Choose a random element of A(L), build the corresponding recurrent sequence
#
####
x = PolynomialRing(QQ,'x').gens()[0]
degree = 3 # Our field will be the splitting field of a random polynomial of at most this degree (slow if degree >= 4)
f = x^degree + sum(randint(-10,10)*x^i for i in range(degree))
f = f.factor()[0][0] # Random irreducible polynomial
L.<y> = (f).splitting_field() # L/Q is a finite Galois extension
print "Number field of degree %i"%L.degree()
O = L.ring_of_integers()
G = L.galois_group()
CC = G.conjugacy_classes()
reps = [C.an_element() for C in CC]
def cent(g):
    G = parent(g)
    return G.subgroup([h for h in G if h*g==g*h])
centralizers = [cent(g) for g in reps]
phi = {}
for i,H in enumerate(centralizers):
    if H is G:
        a = QQ.random_element()
    else:
        K,psi = H.fixed_field()
        a = psi(K.random_element())
    for g in G:
        if g*reps[i]*g^(-1) in phi:
            assert phi[g*reps[i]*g^(-1)] == g(a)
        phi[g*reps[i]*g^(-1)] = g(a)
r = recurrence_from_function(L,phi)
BP = r.bad_primes() # Finite set of bad primes (this is a computational bottleneck)
prime_max = 300
r_list = r[:prime_max]
count = 0
A = r.A()
for p in prime_range(2,prime_max):
    if p in BP:
        continue
    count += 1
    FAC = O.ideal(p).factor()
    for P,n in list(FAC):
        assert n == 1 # Every ramified prime should be in list of bad primes
        K = GF(p)
        F = O.quotient_ring(P,names='a') # Not sure what names argument does, but error without
        v = phi[G.artin_symbol(P)]
        a = F(v*v.denominator()) / F(v.denominator())
        a = F(a) # Why do I need this? For some reason a is an element of L and not F otherwise
        b = F(K(r_list[p]))
        assert a == b
print "Verified for %i primes"%count