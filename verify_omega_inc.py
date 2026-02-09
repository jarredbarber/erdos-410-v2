
def get_prime_factors(n):
    factors = set()
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors

def sigma(n):
    sum_div = 0
    for i in range(1, int(n**0.5) + 1):
        if n % i == 0:
            sum_div += i
            if i*i != n:
                sum_div += n // i
    return sum_div

def check_catalan_logic():
    print("Checking Catalan logic...")
    for e in range(1, 20):
        val = 2**(e+1) - 1
        for x in range(2, 10):
            root = round(val**(1/x))
            if root**x == val:
                print(f"Found solution? e={e}, val={val}, q={root}, x={x}")
    print("Catalan check complete.")

def check_composite_injection():
    print("\nChecking Composite Injection...")
    for e in range(1, 20):
        n = e + 1
        val = 2**n - 1
        factors = get_prime_factors(val)
        is_composite_n = False
        if n > 3:
            for i in range(2, int(n**0.5)+1):
                if n % i == 0:
                    is_composite_n = True
                    break
        
        if is_composite_n:
            print(f"e={e}, n={n} (composite), 2^n-1={val}, count={len(factors)}")

def check_sigma_pf_odd_part():
    print("\nChecking sigma(p^f) odd part logic...")
    mersenne_primes = []
    # Find small Mersenne primes
    for e in range(2, 20):
        m = 2**e - 1
        is_p = True
        for i in range(2, int(m**0.5)+1):
            if m % i == 0:
                is_p = False; break
        if is_p:
            mersenne_primes.append(m)
            
    print(f"Mersenne primes: {mersenne_primes}")
    
    for p in mersenne_primes:
        for f in range(3, 20, 2): # Odd f only
            sig = sigma(p**f)
            odd_part = sig
            while odd_part % 2 == 0:
                odd_part //= 2
            
            if odd_part == 1: continue # Power of 2 only

            factors = list(get_prime_factors(odd_part))
            if len(factors) == 1:
                q = factors[0]
                print(f"Possible match: p={p}, f={f}, odd_part={odd_part} (power of {q})")
                if q in mersenne_primes:
                    print(f"  -> CRITICAL: q={q} is Mersenne!")
            else:
                # print(f"p={p}, f={f}, factors={factors}")
                pass

print("Starting checks...")
check_catalan_logic()
check_composite_injection()
check_sigma_pf_odd_part()
