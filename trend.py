import math
import random

def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def pollard_rho(n):
    if n == 1: return 1
    if n % 2 == 0: return 2
    x = random.randint(2, n - 1)
    y = x
    c = random.randint(1, n - 1)
    g = 1
    while g == 1:
        x = ((x * x) % n + c) % n
        y = ((y * y) % n + c) % n
        y = ((y * y) % n + c) % n
        g = gcd(abs(x - y), n)
        if g == n: # failure
            return pollard_rho(n)
    return g

def get_prime_factors(n):
    factors = {}
    if n == 1: return factors
    
    # Trial division for small factors
    d = 2
    temp = n
    while d * d <= 10000 and d * d <= temp:
        while temp % d == 0:
            factors[d] = factors.get(d, 0) + 1
            temp //= d
        d += 1
    
    if temp == 1: return factors
    
    # For larger numbers, use recursion with pollard rho
    # But for very large numbers, this is still slow.
    # However, we only need sigma(n).
    # sigma(n) = product (p^(e+1)-1)/(p-1)
    
    # Let's just use a list of factors to process
    to_process = [temp]
    
    while to_process:
        curr = to_process.pop()
        if curr == 1: continue
        
        # Check primality (Miller-Rabin would be better but expensive to implement fully correctly)
        # For simplicity, if small enough trial division would have caught it.
        # If large, assume composite unless we can't factor it.
        
        # Simple primality test for mid-size
        is_prime = True
        if curr < 10**14: # Deterministic miller rabin for u64 is easy but python handles large ints
             # just try rho
             pass

        # Try to find a factor
        factor = pollard_rho(curr)
        if factor == curr: # Primaly likely
             factors[curr] = factors.get(curr, 0) + 1
        else:
             to_process.append(factor)
             to_process.append(curr // factor)
             
    return factors

def sigma_from_factors(factors):
    res = 1
    for p, e in factors.items():
        res *= (p**(e+1) - 1) // (p-1)
    return res

# Better sigma that handles large numbers via partial factorization?
# Actually, just use the old one but with a higher limit and maybe a slightly better loop.
# Or just accept that we can't go too far.
# Let's stick to the simple one but maybe optimized.

def sigma_simple(n):
    # Re-implement simple trial division but efficient
    if n == 1: return 1
    sum_div = 1
    d = 2
    temp = n
    
    # Check 2 separately
    if temp % 2 == 0:
        p_sum = 1
        cur_p = 1
        while temp % 2 == 0:
            cur_p *= 2
            p_sum += cur_p
            temp //= 2
        sum_div *= p_sum
        
    d = 3
    limit = int(temp**0.5)
    while d <= limit:
        if temp % d == 0:
            p_sum = 1
            cur_p = 1
            while temp % d == 0:
                cur_p *= d
                p_sum += cur_p
                temp //= d
            sum_div *= p_sum
            limit = int(temp**0.5)
        d += 2
        
    if temp > 1:
        sum_div *= (1 + temp)
    return sum_div

def analyze_trend(start_n, steps):
    a = start_n
    limit = 10**20 # Go a bit higher
    
    log_sum = 0
    
    print(f"k\t R_k\t Avg_ln_R")
    
    for k in range(1, steps + 1):
        if a > limit:
            print(f"Limit reached at step {k}")
            break
            
        # Calculate sigma(a)
        # For large a, this is the bottleneck.
        # Use simple sigma.
        try:
             # If a is too large, sigma_simple will be slow.
             # 10^14 takes ~10^7 iters. 10^20 takes 10^10 iters (too slow).
             if a > 10**15:
                 print(f"Stopping exact calc at a ~ {a:.2e}")
                 break
                 
             s = sigma_simple(a)
             r = s / a
             log_sum += math.log(r)
             avg = log_sum / k
             
             div3 = 1 if a % 3 == 0 else 0
             div5 = 1 if a % 5 == 0 else 0
             div7 = 1 if a % 7 == 0 else 0
             
             if k % 5 == 0 or k < 10:
                 print(f"{k}\t {r:.4f}\t {avg:.4f}\t {div3}\t {div5}\t {div7}")
                 
             a = s
        except KeyboardInterrupt:
            break

if __name__ == "__main__":
    analyze_trend(2, 100)
